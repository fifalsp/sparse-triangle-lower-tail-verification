#!/usr/bin/env python3
"""Run one generated Lean replay quietly, then apply the unchanged axiom audit.

The laptop profile caps each Lean process at 8 GiB and one thread. A shared
lock prevents two instances of this runner from competing on the laptop.
Generated proof sources must already exist; generation is a separate step.
"""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT/'lean'
sys.path.insert(0, str(LEAN/'tools'))
from build_bounded import dependency_graph


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target')
    parser.add_argument('--logs', type=Path, required=True)
    parser.add_argument('--hours', type=float, default=24)
    parser.add_argument('--plan-only', action='store_true')
    args = parser.parse_args()
    if not args.target.startswith('SparseLowerTail.') or not 0 < args.hours <= 24:
        parser.error('Use a project target and a time limit in (0,24] hours')
    profile = LEAN/'lakefile.laptop.toml'
    base = tomllib.loads((LEAN/'lakefile.toml').read_text())
    config = tomllib.loads(profile.read_text())
    if config.pop('weakLeanArgs', None) != ['-M8192', '-j1'] or config != base:
        raise ValueError('Laptop profile must equal the current package plus the 8 GiB/one-thread limits')
    graph = dependency_graph(args.target)
    def manifest():
        return {m: hashlib.sha256((LEAN/Path(m.replace('.', '/')).with_suffix('.lean')).read_bytes()).hexdigest()
                for m in sorted(graph)}
    sources = manifest()
    build = [sys.executable, 'tools/build_bounded.py', args.target,
             '--logs', str(args.logs.resolve()/'build'), '--workers', '1',
             '--lean-threads', '1', '--lakefile', str(profile)]
    if args.plan_only:
        print(json.dumps({'target': args.target, 'modules': len(graph), 'build': build,
                          'workers': 1, 'lean_memory_cap_mib': 8192, 'nice': 15}))
        return
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    lockpath = ROOT/'results/laptop-replay.lock'
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    lock = lockpath.open('a+')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    os.nice(15)
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    start = time.monotonic()
    deadline = start+args.hours*3600
    status = {'target': args.target, 'runner_pid': os.getpid(), 'phase': 'starting',
              'started_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'source_parent_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'workers': 1, 'lean_threads': 1, 'lean_memory_cap_mib': 8192,
              'nice': 15, 'time_limit_hours': args.hours,
              'trust_status': 'Incomplete until the full build and axiom audit pass'}
    (logs/'source-manifest.json').write_text(json.dumps(sources, indent=2)+'\n')
    def record():
        status['seconds'] = time.monotonic()-start
        status['max_child_rss_bytes_macos'] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        (logs/'status.json').write_text(json.dumps(status, indent=2)+'\n')
        print(json.dumps(status), flush=True)
    def run(command, filename, phase):
        status['phase'] = phase
        record()
        with (logs/filename).open('w') as output:
            process = subprocess.Popen(command, cwd=LEAN, env=env, stdout=output,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            status['child_pid'] = process.pid
            record()
            try:
                code = process.wait(timeout=max(0.01, deadline-time.monotonic()))
            except BaseException:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                raise
        status.pop('child_pid', None)
        status['last_exit_code'] = code
        record()
        if code:
            raise subprocess.CalledProcessError(code, command)
    try:
        run(build, 'build.log', 'building')
        audit = (LEAN/'Audit.lean').read_text()
        if not audit.startswith('import SparseLowerTail\n'):
            raise ValueError('Unexpected audit header; do not weaken the policy')
        audit_path = logs/'AuditReplay.lean'
        audit_path.write_text(audit.replace('import SparseLowerTail\n', 'import '+args.target+'\n', 1))
        run(['lake', '--file', str(profile), 'env', 'lean', '-M8192', '-j1', str(audit_path)],
            'audit.log', 'axiom_audit')
        if manifest() != sources:
            raise ValueError('Proof sources changed during the run; revalidate before accepting')
        status.update(phase='complete', trust_status='Full target built and namespace-wide axiom audit passed')
        (logs/'REPLAY_SUCCESS.txt').write_text(args.target+' built and audited.\n')
    except subprocess.TimeoutExpired:
        status.update(phase='time_limit', trust_status='Partial build cache only; full theorem not verified')
        record()
        raise SystemExit(3)
    except BaseException as exc:
        status.update(phase='failed', failure=type(exc).__name__,
                      trust_status='Full theorem not verified; inspect logs and preserve checked cache')
        record()
        raise
    record()


if __name__ == '__main__':
    main()

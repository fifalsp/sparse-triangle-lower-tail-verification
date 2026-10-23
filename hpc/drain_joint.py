#!/usr/bin/env python3
"""User-authorized queue drain: signal only the scheduler, never Lean or Lake."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import time

JOB = '30254216'
MANIFEST_SHA = 'b14aedaa8bc2447939e456b80e112b138b16348085539f108bff0f6134514811'
AUDIT_SHA = '956129721ba7190769a93bd755dde91ac7b4fcd15326656721cc822308cc9014'
CONTROLLER_SHA = '559ab431f061fb6561854e8d21f681174dda6016baef3975549d2385df2d06bc'
READY = 'CONTROLLED_HANDOFF_READY.json'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def validate_handoff(read):
    record = json.loads(read(READY))
    if (record.get('job') != JOB or record.get('phase') != 'active-proofs-drained'
            or record.get('authorization') != 'user-approved-six-to-sixteen-worker-handoff'
            or record.get('manifest_sha256') != MANIFEST_SHA
            or record.get('audit_sha256') != AUDIT_SHA
            or record.get('controller_sha256') != CONTROLLER_SHA
            or record.get('proof_processes_signalled') != []
            or digest(read('source-manifest.json')) != MANIFEST_SHA
            or b'KeyboardInterrupt' not in read('combined-build.log')):
        raise ValueError('Invalid controlled handoff evidence')
    proofs = record.get('active_proofs', [])
    modules = [p['module'] for p in proofs]
    if not 1 <= len(modules) <= 6 or len(set(modules)) != len(modules):
        raise ValueError('Invalid active proof set')
    for proof in proofs:
        name = proof['module']
        if not re.fullmatch(r'SparseLowerTail(?:\.[A-Za-z0-9_]+)+', name):
            raise ValueError('Unsafe proof name')
        log = read('combined-build/' + name + '.log')
        if (digest(log) != proof['completed_log_sha256']
                or b'Build completed successfully' not in log):
            raise ValueError('An active proof did not finish successfully')
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--pid', type=int, required=True)
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--authorized', action='store_true', required=True)
    a = p.parse_args()
    work = a.work.resolve()
    repo, logs = work/'repo', work/'logs'
    proc = Path('/proc')/str(a.pid)
    command = (proc/'cmdline').read_bytes().split(b'\0')[:-1]
    command = [v.decode() for v in command]
    expected_script = '/nfs/roberts/project/pi_sl3363/sl3363/triangle-joint-control-2bdd616/build_ready_batches.py'
    if (os.environ.get('SLURM_JOB_ID') != JOB or ('job_'+JOB) not in (proc/'cgroup').read_text()
            or len(command) < 2 or command[1] != expected_script
            or digest(Path(expected_script).read_bytes()) != CONTROLLER_SHA
            or command[command.index('--repo')+1] != str(repo)
            or command[command.index('--logs')+1] != str(logs/'combined-build')
            or command[command.index('--workers')+1] != '6'):
        raise ValueError('Controller identity or allocation differs')
    sigstate = dict(line.split(':',1) for line in (proc/'status').read_text().splitlines() if ':' in line)
    if not int(sigstate['SigCgt'].strip(),16) & 2:
        raise ValueError('Scheduler has no Python interrupt handler')
    def check_inputs():
        if (digest((logs/'source-manifest.json').read_bytes()) != MANIFEST_SHA
                or digest((repo/'lean/Audit.lean').read_bytes()) != AUDIT_SHA):
            raise ValueError('Proof manifest or original audit policy changed')
    check_inputs()
    if (logs/READY).exists():
        raise ValueError('Handoff already recorded')
    frozen = False
    try:
        os.kill(a.pid, signal.SIGSTOP)
        frozen = True
        # Wait until the process is stopped, so its queue cannot refill during inspection.
        for _ in range(100):
            if 'T' in next(v for v in (proc/'status').read_text().splitlines() if v.startswith('State:')):
                break
            time.sleep(.01)
        else:
            raise ValueError('Scheduler did not stop for inspection')
        status = json.loads((logs/'combined-build/status.json').read_text())
        if status['failed'] or status['workers'] != 6 or status['phase'] != 'building':
            raise ValueError('Not a healthy active build')
        children = set()
        for thread in (proc/'task').iterdir():
            children.update(int(pid) for pid in (thread/'children').read_text().split())
        active = []
        for pid in children:
            try:
                args = (Path('/proc')/str(pid)/'cmdline').read_bytes().split(b'\0')[:-1]
            except FileNotFoundError:
                continue
            args = [v.decode() for v in args]
            if not args:
                continue
            if (Path(args[0]).name != 'lake' or '--no-build' in args
                    or 'build' not in args or len(args[args.index('build')+1:]) != 1):
                raise ValueError('Controller is not in an ordinary proof build wave')
            active.append({'module':args[-1], 'lake_pid':pid})
        if not 1 <= len(active) <= 6:
            raise ValueError('No active proof wave to drain safely')
        record = dict(job=JOB, phase='draining',
                      authorization='user-approved-six-to-sixteen-worker-handoff',
                      started_at_utc=datetime.now(timezone.utc).isoformat(),
                      controller_pid=a.pid, controller_sha256=CONTROLLER_SHA,
                      manifest_sha256=MANIFEST_SHA, audit_sha256=AUDIT_SHA,
                      proof_processes_signalled=[], active_proofs=active,
                      conservative_status_before=status)
        (logs/'CONTROLLED_HANDOFF_STARTED.json').write_text(json.dumps(record,indent=2)+'\n')
        # SIGINT is delivered only to Python's main thread. Its executor's context
        # manager waits for the already-running subprocesses before propagating it.
        os.kill(a.pid, signal.SIGINT)
    finally:
        if frozen:
            os.kill(a.pid, signal.SIGCONT)
    while proc.exists():
        try:
            if 'Z' in next(v for v in (proc/'status').read_text().splitlines() if v.startswith('State:')):
                break
        except FileNotFoundError:
            break
        time.sleep(.5)
    check_inputs()
    for proof in active:
        content = (logs/'combined-build'/(proof['module']+'.log')).read_bytes()
        if b'Build completed successfully' not in content:
            raise ValueError('An active proof failed; no handoff-ready marker created')
        proof['completed_log_sha256'] = digest(content)
    if b'KeyboardInterrupt' not in (logs/'combined-build.log').read_bytes():
        raise ValueError('Unexpected controller exit')
    # Counter is conservative: some drained proofs may not have reached report().
    (logs/'combined-build/status.json').write_text(json.dumps(status,indent=2)+'\n')
    record.update(phase='active-proofs-drained',finished_at_utc=datetime.now(timezone.utc).isoformat())
    (logs/READY).write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record),flush=True)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Replay the sparse manuscript's computational checks in a fresh directory."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use -O or PYTHONOPTIMIZE.')

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fingerprints():
    paths = [ROOT/'verify.py', ROOT/'requirements.txt']
    for directory in ['data', 'verification']:
        paths.extend(p for p in (ROOT/directory).rglob('*')
                     if p.is_file() and p.suffix in ['.py', '.json'])
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true',
                        help='Only preliminary checks; does NOT verify global positivity.')
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--max-nodes', type=int, default=2000000)
    parser.add_argument('--output-dir', type=Path,
                        help='New, nonexistent directory; never reuse old results.')
    args = parser.parse_args()
    if args.jobs < 1 or args.max_nodes < 1:
        parser.error('--jobs and --max-nodes must be positive')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out = (args.output_dir or ROOT/'results'/stamp).resolve()
    if out.exists():
        parser.error(f'Output directory already exists: {out}')
    out.mkdir(parents=True)
    (out/'logs').mkdir()
    env = dict(os.environ, SPARSE_VERIFICATION_RESULTS=str(out),
               OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1')
    started = time.monotonic()
    report = dict(status='running', mode='quick' if args.quick else 'full',
                  started_utc=datetime.now(timezone.utc).isoformat(),
                  python=platform.python_version(), platform=platform.platform(),
                  dependencies={p: version(p) for p in ['python-flint','numpy','sympy','mpmath']},
                  source_sha256=fingerprints(), steps=[], cover_jobs=[])

    def save():
        report['elapsed_seconds'] = time.monotonic()-started
        temp = out/'run.json.tmp'
        temp.write_text(json.dumps(report, indent=2)+'\n')
        temp.replace(out/'run.json')

    def run(name, arguments):
        begin = time.monotonic()
        log = out/'logs'/f'{name}.log'
        with log.open('w') as stream:
            proc = subprocess.run([sys.executable, *arguments], cwd=ROOT,
                                  env=env, stdout=stream, stderr=subprocess.STDOUT)
        result = dict(name=name, arguments=[a.replace(str(out), '$RESULTS') for a in arguments], exit_code=proc.returncode,
                      seconds=time.monotonic()-begin, log=str(log.relative_to(out)))
        return result

    def step(name, arguments):
        result = run(name, arguments)
        report['steps'].append(result)
        save()
        if result['exit_code']:
            raise RuntimeError(f'{name} failed; see {result["log"]}')
        print(f'PASS {name}', flush=True)

    save()
    print(f'Results: {out}', flush=True)
    try:
        step('template-check', ['verification/cover/build_templates.py', '--check'])
        step('crossing-support-tangency', ['verification/cover/endpoint_common.py'])
        step('penalized-constants', ['verification/cover/verify_penalized_constants.py'])
        step('planar-coverage', ['verification/cover/planar_coverage.py'])
        step('planar-replay', ['verification/cover/planar_coverage.py', 'verify'])
        step('apex-symbolic', ['verification/apex/symbolic.py'])
        step('apex-local-tail', ['verification/apex/verify_apex.py', '--quick',
                               '--output-dir', str(out/'apex')])
        step('family-preliminary', ['verification/family/verify_family.py', '--quick',
                                    '--output-dir', str(out/'family')])
        step('fail-closed-controls', ['verification/check_fail_closed.py'])
        if args.quick:
            report['status'] = 'quick_checks_passed'
            report['scope'] = 'No compact-domain positivity claim; run without --quick for the full verification.'
        else:
            step('apex-global', ['verification/apex/verify_apex.py', '--max-nodes',
                                str(args.max_nodes), '--output-dir', str(out/'apex')])
            apex = json.loads((out/'apex'/'apex.json').read_text())
            if apex['status'] != 'complete' or apex['pending'] != 0:
                raise RuntimeError('Apex did not finish all boxes')
            step('family-global', ['verification/family/verify_family.py', '--max-nodes',
                                   str(args.max_nodes), '--output-dir', str(out/'family')])
            family = json.loads((out/'family'/'family.json').read_text())
            if family['status'] != 'complete':
                raise RuntimeError('Family verification did not complete')
            for part in ['local1', 'local2', 'compact']:
                item = family['checks'].get(part, {})
                if item.get('status') != 'complete' or item.get('pending') != 0:
                    raise RuntimeError(f'Family {part} did not finish all boxes')
            cells = json.loads((ROOT/'data'/'cover.json').read_text())['cells']
            jobs = [(name,str(i)) for name,c in cells.items() for i in range(len(c['vertices']))]
            jobs += [(name,'apex') for name,c in cells.items() if c['apex']]
            if len(jobs) != 42:
                raise RuntimeError(f'Expected 42 cover jobs, found {len(jobs)}')
            with ThreadPoolExecutor(max_workers=args.jobs) as executor:
                futures = {executor.submit(run, f'cover-{name}-{v}',
                           ['verification/cover/verify_endpoint.py',name,v,str(args.max_nodes)]): (name,v)
                           for name,v in jobs}
                for future in as_completed(futures):
                    name,v = futures[future]
                    result = future.result()
                    report['cover_jobs'].append(result)
                    save()
                    if result['exit_code']:
                        raise RuntimeError(f'Cover {name}/{v} failed; see {result["log"]}')
                    item = json.loads((out/'cover'/f'verified_{name}_{v}.json').read_text())
                    if item['status'] != 'complete' or item['pending'] != 0:
                        raise RuntimeError(f'Cover {name}/{v} has unresolved boxes')
                    if item['inputs_sha256'] != sha(ROOT/'data'/'cover.json'):
                        raise RuntimeError(f'Cover {name}/{v} input hash mismatch')
                    print(f'PASS cover {name}/{v} ({len(report["cover_jobs"])}/42, {item["nodes"]} nodes)', flush=True)
            report['status'] = 'complete'
            report['scope'] = 'All four current-manuscript computational assertion groups, including 42 cover jobs and the parameter family, plus the independent single-apex check.'
            report['cover_jobs_completed'] = 42
        if fingerprints() != report['source_sha256']:
            raise RuntimeError('Source or input files changed while verification was running')
        report['artifact_sha256'] = {str(p.relative_to(out)):sha(p)
                                    for p in sorted(out.rglob('*.json')) if p.name != 'run.json'}
        save()
        print(json.dumps({k:report[k] for k in ['status','scope','elapsed_seconds']},indent=2))
    except BaseException as error:
        report['status'] = 'failed'
        report['failure'] = str(error)
        save()
        raise


if __name__ == '__main__':
    main()

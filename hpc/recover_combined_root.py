#!/usr/bin/env python3
"""Recover only the diagnosed final Lake stack overflow; preserve proof gates."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time

from continuation_gate import MANIFEST_SHA
from resume_assembly import COMMIT, REQUIRED, TARGET, restore
from resume_abb_root import AUDIT_SHA, stack_profile, verify_sources

TOTAL = 94032


def validate_data(data, state, exit_code):
    if state != 'FAILED' or exit_code != '1:0' or data['exit-code.txt'].strip() != b'1':
        raise ValueError('Expected the diagnosed failed allocation, not another exit')
    if hashlib.sha256(data['source-manifest.json']).hexdigest() != MANIFEST_SHA:
        raise ValueError('Original combined source manifest differs')
    sources = json.loads(data['source-manifest.json'])
    status = json.loads(data['combined-build/status.json'])
    inputs = json.loads(data['assembly-inputs.json'])
    if (len(sources) != TOTAL or TARGET not in sources
            or data['source-commit.txt'].decode().strip() != COMMIT
            or status['target'] != TARGET or status['total'] != TOTAL
            or status['completed'] != TOTAL - 1
            or status['phase'] != 'build_failed'
            or status['failed'] != {TARGET: -6}
            or inputs['missing'] or not REQUIRED <= inputs['selected'].keys()
            or b'Stack overflow detected. Aborting.' not in data['root-failure.log']):
        raise ValueError('Failure is not the isolated final Lake stack overflow')
    if data.get('success-marker'):
        raise ValueError('Contradictory success and failure evidence')
    return sources


def evidence(archive, state='FAILED', exit_code='1:0'):
    with tarfile.open(archive, 'r:gz') as stream:
        def read(name):
            return stream.extractfile('logs/' + name).read()
        data = {name: read(name) for name in ('source-manifest.json', 'source-commit.txt',
                'assembly-inputs.json', 'combined-build/status.json', 'exit-code.txt')}
        data['root-failure.log'] = read('combined-build/' + TARGET + '.log')
        data['success-marker'] = 'logs/ASSEMBLY_SUCCESS.txt' in stream.getnames()
    return data, validate_data(data, state, exit_code)


def lake_command(profile, memory, stack):
    if memory != 49152 or stack != 262144:
        raise ValueError('Unexpected native Lake resource profile')
    return ['lake', '--file', str(profile)]


def main():
    if len(sys.argv) == 5 and sys.argv[1] == 'gate':
        evidence(Path(sys.argv[2]), sys.argv[3], sys.argv[4])
        print('resume-isolated-root-stack-overflow')
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--prior-result', type=Path, required=True)
    parser.add_argument('--checkpoint', type=Path)
    parser.add_argument('--logs', type=Path, required=True)
    parser.add_argument('--memory-mib', type=int, default=49152)
    parser.add_argument('--stack-kib', type=int, default=262144)
    args = parser.parse_args()
    if args.memory_mib != 49152 or args.stack_kib != 262144:
        raise ValueError('Unexpected recovery resource profile')
    repo, logs = args.repo.resolve(), args.logs.resolve()
    lean = repo / 'lean'
    logs.mkdir(parents=True, exist_ok=True)
    prior, sources = evidence(args.prior_result)
    for name in ('source-manifest.json', 'source-commit.txt', 'assembly-inputs.json'):
        (logs / name).write_bytes(prior[name])
    (logs / 'predecessor-root-stack-failure.log').write_bytes(prior['root-failure.log'])
    if (repo / 'SOURCE_COMMIT').read_text().strip() != COMMIT:
        raise ValueError('Checkout revision differs')
    if args.checkpoint:
        print('Restoring completed dependencies from finalized checkpoint', flush=True)
        count = restore(args.checkpoint, repo, sources)
        (logs / 'checkpoint-restoration.json').write_text(json.dumps({
            'manifest_sources_restored_or_compared': count, 'complete_stream_read': True}) + '\n')
    verify_sources(lean, sources)
    audit = (lean / 'Audit.lean').read_bytes()
    if (hashlib.sha256(audit).hexdigest() != AUDIT_SHA
            or not audit.startswith(b'import SparseLowerTail\n')):
        raise ValueError('Original audit policy differs')
    (logs / 'source-hashes-before.txt').write_text('All original dependencies and audit policy match.\n')
    profile = lean / 'lakefile.combined-stack.toml'
    expected = stack_profile((lean / 'lakefile.toml').read_text(), args.memory_mib, args.stack_kib)
    if profile.exists() and profile.read_text() != expected:
        raise ValueError('Existing recovery resource profile differs')
    profile.write_text(expected)
    lake = lake_command(profile, args.memory_mib, args.stack_kib)
    build = logs / 'combined-build'
    build.mkdir()
    start = time.monotonic()
    status = dict(target=TARGET, total=TOTAL, completed=TOTAL - 1, failed={},
                  workers=1, phase='building', trust_status='Full target, source hashes and original audit pending')
    def record():
        status['seconds'] = time.monotonic() - start
        (build / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
    def run(command, filename):
        with (logs / filename).open('w') as out:
            result = subprocess.run(command, cwd=lean, env=dict(os.environ, LEAN_NUM_THREADS='0'),
                                    stdout=out, stderr=subprocess.STDOUT)
        if result.returncode:
            status.update(phase='build_failed', failed={TARGET: result.returncode})
            record()
            raise subprocess.CalledProcessError(result.returncode, command)
    record()
    print('Building final aggregate with native Lake, synchronous tasks and 256MiB native/Lean stacks', flush=True)
    run([*lake, 'build', TARGET], 'combined-build.log')
    status.update(completed=TOTAL, phase='build_complete')
    record()
    verify_sources(lean, sources)
    if (lean / 'Audit.lean').read_bytes() != audit:
        raise ValueError('Audit policy changed during build')
    audit_path = logs / 'AuditCompleted.lean'
    audit_path.write_bytes(audit.replace(b'import SparseLowerTail\n',
                                       ('import ' + TARGET + '\n').encode(), 1))
    print('Full target built; running unchanged namespace audit', flush=True)
    run([*lake, 'env', 'lean', '-M49152', '-j1', '-s262144', str(audit_path)], 'combined-audit.log')
    if not re.search(rb'Axiom audit passed: [1-9][0-9]* project declarations, '
                     rb'[1-9][0-9]* theorems; only propext, Classical.choice, '
                     rb'Quot.sound allowed\.', (logs / 'combined-audit.log').read_bytes()):
        raise ValueError('Original namespace audit success evidence missing')
    verify_sources(lean, sources)
    if (lean / 'Audit.lean').read_bytes() != audit:
        raise ValueError('Audit policy changed during audit')
    (logs / 'source-hashes-passed.txt').write_text('All original target sources and audit policy unchanged.\n')
    (logs / 'ASSEMBLY_SUCCESS.txt').write_text('Full combined target and unchanged namespace audit passed.\n')
    (logs / 'SUCCESS.txt').write_text('Full target, source hashes and original audit passed.\n')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Run one full regional replay on a node-local checkout, then audit it."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'


def stage_spec(stage):
    if stage == 'f1':
        return dict(target='SparseLowerTail.Section05.ApexReplay.F1.FullCube',
                    generate=['tools/generate_apex_replay.py', 'data/apex-f1-subdivision-proposal.json'],
                    status='apex-status.json', build='apex-build', audit='apex-audit.log',
                    marker='APEX_SUCCESS.txt', metadata=dict(fan=1))
    if stage in ('cover0', 'cover12'):
        job = int(stage[5:])
        return dict(target=f'SparseLowerTail.Section05.CoverJobReplay.Job{job:02d}Full.Ordered',
                    generate=['tools/generate_cover_job_replay.py', f'data/cover-job-{job:02d}-subdivision-proposal.json.gz', '--full'],
                    status='cover-job-status.json', build='cover-build', audit='cover-job-audit.log',
                    marker='COVER_JOB_SUCCESS.txt', metadata=dict(job=job))
    if stage == 'abb':
        return dict(target='SparseLowerTail.Section08.FamilyABBReplay.Full.FullNeighborhood',
                    generate=['tools/generate_family_abb_replay.py', 'data/family-abb-subdivision-proposal.json.gz'],
                    status='family-abb-status.json', build='family-build', audit='family-abb-audit.log',
                    marker='FAMILY_ABB_SUCCESS.txt', metadata={})
    if stage == 'exterior':
        return dict(target='SparseLowerTail.Section08.FamilyExteriorReplay.Full.CompactCertificate',
                    generate=['tools/generate_family_exterior_replay.py', 'data/family-exterior-subdivision-proposal.json.gz', '--full'],
                    status='family-exterior-status.json', build='exterior-build', audit='family-exterior-audit.log',
                    marker='FAMILY_EXTERIOR_SUCCESS.txt', metadata={})
    raise ValueError(stage)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('stage', choices=['f1', 'cover0', 'cover12', 'abb', 'exterior'])
    p.add_argument('--logs', type=Path, required=True)
    p.add_argument('--lakefile', type=Path, required=True)
    p.add_argument('--workers', type=int, choices=range(1, 9), default=4)
    p.add_argument('--audit-sha256', required=True)
    p.add_argument('--expected-manifest', type=Path)
    a = p.parse_args()
    spec = stage_spec(a.stage)
    logs = a.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    profile = a.lakefile.resolve()
    start = time.monotonic()
    audit_source = (LEAN / 'Audit.lean').read_bytes()
    if hashlib.sha256(audit_source).hexdigest() != a.audit_sha256:
        raise ValueError('Audit policy differs from the checked source')
    status = dict(spec['metadata'], target=spec['target'],
                  trust_status='Full target build, source hashes and unchanged axiom audit pending')
    def record(phase):
        status.update(phase=phase, seconds=time.monotonic()-start)
        (logs / spec['status']).write_text(json.dumps(status, indent=2)+'\n')
    def run(command, filename):
        with (logs / filename).open('w') as output:
            subprocess.run(command, cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'),
                           stdout=output, stderr=subprocess.STDOUT, check=True)
    record('generate')
    run([sys.executable, *spec['generate']], 'generation.log')
    loader = importlib.util.spec_from_file_location('bounded_plan', LEAN / 'tools/build_bounded.py')
    bounded = importlib.util.module_from_spec(loader)
    loader.loader.exec_module(bounded)
    graph = bounded.dependency_graph(spec['target'])
    def manifest():
        return {m: hashlib.sha256((LEAN / Path(m.replace('.', '/')).with_suffix('.lean')).read_bytes()).hexdigest()
                for m in sorted(graph)}
    sources = manifest()
    if a.expected_manifest and json.loads(a.expected_manifest.read_text()) != sources:
        raise ValueError('Resumed proof sources differ from the preserved checkpoint')
    if a.expected_manifest:
        (logs / 'checkpoint-source-match.txt').write_text('Regenerated target dependencies match the preserved checkpoint.\n')
    (logs / 'source-manifest.json').write_text(json.dumps(sources, indent=2)+'\n')
    record('bounded_kernel_build')
    run([sys.executable, str(ROOT / 'hpc/build_ready_batches.py'), '--repo', str(ROOT),
         '--target', spec['target'], '--logs', str(logs / spec['build']),
         '--lakefile', str(profile), '--workers', str(a.workers)], 'regional-build.log')
    record('axiom_audit')
    audit = audit_source.decode()
    if not audit.startswith('import SparseLowerTail\n'):
        raise ValueError('Unexpected audit header')
    audit_path = logs / 'AuditRegion.lean'
    audit_path.write_text(audit.replace('import SparseLowerTail\n', 'import '+spec['target']+'\n', 1))
    run(['lake', '--file', str(profile), 'env', 'lean', '-M16384', '-j1', str(audit_path)], spec['audit'])
    if (LEAN / 'Audit.lean').read_bytes() != audit_source or manifest() != sources:
        raise ValueError('Proof source or audit policy changed during verification')
    (logs / 'source-hashes-passed.txt').write_text('Every target dependency and the audit policy are unchanged.\n')
    status['trust_status'] = 'Full regional target and unchanged axiom audit passed; all target source hashes unchanged'
    if a.stage == 'exterior':
        status['scope'] = 'Full exterior certificate; ABB local theorem remains an internal premise'
    record('complete')
    (logs / spec['marker']).write_text(spec['target']+' built and audited.\n')


if __name__ == '__main__':
    main()

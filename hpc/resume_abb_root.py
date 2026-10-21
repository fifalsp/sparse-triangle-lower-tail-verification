#!/usr/bin/env python3
"""Retry ABB's final module with a larger stack and the preserved proof sources."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

TARGET = 'SparseLowerTail.Section08.FamilyABBReplay.Full.FullNeighborhood'
AUDIT_SHA = '956129721ba7190769a93bd755dde91ac7b4fcd15326656721cc822308cc9014'
FAMILIES = {
    'abb': (TARGET, 7462, 'family', 'family-abb', 'FAMILY_ABB_SUCCESS.txt'),
    'exterior': ('SparseLowerTail.Section08.FamilyExteriorReplay.Full.CompactCertificate',
                 12872, 'exterior', 'family-exterior', 'FAMILY_EXTERIOR_SUCCESS.txt'),
}


def verify_sources(lean, sources):
    for module, expected in sources.items():
        parts = module.split('.')
        if parts[0] != 'SparseLowerTail' or not all(p.isidentifier() for p in parts):
            raise ValueError('Invalid dependency module: ' + module)
        path = lean.joinpath(*parts).with_suffix('.lean')
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('Preserved dependency source changed: ' + module)


def stack_profile(source, memory, stack):
    if 'weakLeanArgs' in source or source.count('defaultTargets') != 1:
        raise ValueError('Unexpected base Lake profile')
    return source.replace('defaultTargets',
        f'weakLeanArgs = ["-M{memory}", "-j1", "-s{stack}"]\ndefaultTargets', 1)


def main(family='abb'):
    target, total, build_prefix, status_prefix, success_marker = FAMILIES[family]
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--previous-logs', type=Path, required=True)
    p.add_argument('--logs', type=Path, required=True)
    p.add_argument('--memory-mib', type=int, default=49152)
    p.add_argument('--stack-kib', type=int, default=65536)
    a = p.parse_args()
    repo, old, logs = a.repo.resolve(), a.previous_logs.resolve(), a.logs.resolve()
    lean = repo / 'lean'
    logs.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    prior = json.loads((old / (build_prefix+'-build/status.json')).read_text())
    assert prior['target'] == target and prior['total'] == total
    assert prior['completed'] == total-1 and prior['failed'] == {target: 1}
    sources = json.loads((old / 'source-manifest.json').read_text())
    assert len(sources) == total and target in sources
    verify_sources(lean, sources)
    audit = (lean / 'Audit.lean').read_bytes()
    assert hashlib.sha256(audit).hexdigest() == AUDIT_SHA
    assert audit.startswith(b'import SparseLowerTail\n')
    (logs / 'source-manifest.json').write_text(json.dumps(sources, indent=2)+'\n')
    (logs / 'source-commit.txt').write_text((repo / 'SOURCE_COMMIT').read_text())
    (logs / 'resume-policy.json').write_text(json.dumps(dict(
        previous_completed=total-1, total=total, family=family, memory_mib=a.memory_mib,
        stack_kib=a.stack_kib, proof_source_changes=False), indent=2)+'\n')
    profile = lean / ('lakefile.'+family+'-stack-' + logs.parent.name + '.toml')
    profile.write_text(stack_profile((lean / 'lakefile.toml').read_text(),
                                    a.memory_mib, a.stack_kib))
    build_dir = logs / (build_prefix+'-build')
    build_dir.mkdir()
    status = dict(target=target, phase='bounded_kernel_build',
                  trust_status='Full target, unchanged audit and source hashes pending')
    def record(phase):
        status.update(phase=phase, seconds=time.monotonic()-started)
        (logs / (status_prefix+'-status.json')).write_text(json.dumps(status, indent=2)+'\n')
    def run(command, filename):
        with (logs / filename).open('w') as output:
            subprocess.run(command, cwd=lean, env=dict(os.environ, LEAN_NUM_THREADS='1'),
                           stdout=output, stderr=subprocess.STDOUT, check=True)
    record('bounded_kernel_build')
    # Ordinary Lake build revalidates cached imports and checks the final target.
    run(['lake', '--file', str(profile), 'build', target], 'regional-build.log')
    (build_dir / 'status.json').write_text(json.dumps(dict(
        target=target, phase='build_complete', completed=total, total=total,
        cached=total-1, failed={}, workers=1,
        seconds=time.monotonic()-started,
        trust_status='Ordinary full-target Lake build passed; audit still required'), indent=2)+'\n')
    record('axiom_audit')
    audit_path = logs / 'AuditRegion.lean'
    audit_path.write_bytes(audit.replace(b'import SparseLowerTail\n',
                                        ('import '+target+'\n').encode(), 1))
    run(['lake', '--file', str(profile), 'env', 'lean',
         '-M'+str(a.memory_mib), '-j1', '-s'+str(a.stack_kib), str(audit_path)],
        status_prefix+'-audit.log')
    verify_sources(lean, sources)
    assert (lean / 'Audit.lean').read_bytes() == audit
    (logs / 'source-hashes-passed.txt').write_text(
        'Every target dependency and the audit policy are unchanged.\n')
    status['trust_status'] = 'Full regional target and unchanged axiom audit passed; all target source hashes unchanged'
    record('complete')
    (logs / success_marker).write_text(target+' built and audited.\n')
    (logs / 'SUCCESS.txt').write_text('Full '+family+' target, source hashes and unchanged audit passed.\n')


if __name__ == '__main__':
    main()

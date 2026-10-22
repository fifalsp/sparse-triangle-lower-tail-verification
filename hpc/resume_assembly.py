#!/usr/bin/env python3
"""Resume an interrupted combined build without regenerating accepted sources."""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile

from resume_abb_root import AUDIT_SHA, stack_profile, verify_sources

COMMIT = '8ecc9d41892517175d46efc84e63a5d745096db0'
TARGET = 'SparseLowerTail.CompletedReplays'
REQUIRED = {*(f'cover:{i}' for i in range(36)),
            *(f'apex:{i}' for i in range(1, 7)), 'abb', 'exterior'}


def prior_evidence(archive):
    wanted = ['source-manifest.json', 'assembly-inputs.json',
              'combined-build/status.json', 'exit-code.txt', 'source-commit.txt']
    with tarfile.open(archive, 'r:gz') as stream:
        data = {name: stream.extractfile('logs/' + name).read() for name in wanted}
    status = json.loads(data['combined-build/status.json'])
    inputs = json.loads(data['assembly-inputs.json'])
    sources = json.loads(data['source-manifest.json'])
    if (data['exit-code.txt'].strip() != b'124' or status['target'] != TARGET
            or status['failed'] or status['total'] != len(sources)
            or TARGET not in sources or inputs['missing']
            or not REQUIRED <= inputs['selected'].keys()
            or data['source-commit.txt'].decode().strip() != COMMIT):
        raise ValueError('Previous run is not the expected interrupted assembly')
    return data, sources


def restore(archive, repo, sources):
    """Read the entire gzip stream; restore manifest sources and regular cache files.

    Existing handwritten sources are compared, never overwritten. Every expected
    project dependency is checked again before any Lean build starts.
    """
    found = set()
    with gzip.open(archive, 'rb') as compressed, tarfile.open(fileobj=compressed, mode='r|') as stream:
        for member in stream:
            path = Path(member.name)
            if path.is_absolute() or '..' in path.parts or member.issym() or member.islnk():
                raise ValueError('Unsafe checkpoint entry: ' + member.name)
            if not member.isfile():
                continue
            if member.name.startswith('lean/SparseLowerTail/') and path.suffix == '.lean':
                module = '.'.join(path.relative_to('lean').with_suffix('').parts)
                if module not in sources:
                    continue
                content = stream.extractfile(member).read()
                if hashlib.sha256(content).hexdigest() != sources[module]:
                    raise ValueError('Checkpoint source differs from manifest: ' + module)
                dest = repo / path
                if dest.exists():
                    if dest.read_bytes() != content:
                        raise ValueError('Refusing to overwrite existing source: ' + module)
                else:
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_bytes(content)
                found.add(module)
            elif member.name.startswith('lean/.lake/build/'):
                dest = repo / path
                dest.parent.mkdir(parents=True, exist_ok=True)
                with dest.open('wb') as out:
                    shutil.copyfileobj(stream.extractfile(member), out)
            elif member.name == 'SOURCE_COMMIT':
                if stream.extractfile(member).read().decode().strip() != COMMIT:
                    raise ValueError('Unexpected checkpoint source revision')
        # tarfile stops at the tar EOF; drain gzip to validate its final CRC too.
        while compressed.read(1024 * 1024):
            pass
    verify_sources(repo / 'lean', sources)
    return len(found)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--prior-result', type=Path, required=True)
    p.add_argument('--checkpoint', type=Path)
    p.add_argument('--logs', type=Path, required=True)
    p.add_argument('--workers', type=int, choices=range(1, 9), default=6)
    p.add_argument('--memory-mib', type=int, default=49152)
    a = p.parse_args()
    repo, logs = a.repo.resolve(), a.logs.resolve()
    lean = repo / 'lean'
    logs.mkdir(parents=True, exist_ok=True)
    prior, sources = prior_evidence(a.prior_result)
    for name in ['source-manifest.json', 'assembly-inputs.json', 'source-commit.txt']:
        (logs / name).write_bytes(prior[name])
    if (repo / 'SOURCE_COMMIT').read_text().strip() != COMMIT:
        raise ValueError('Unexpected checkout revision')
    if a.checkpoint:
        print('Restoring generated sources and cache from complete checkpoint', flush=True)
        restored = restore(a.checkpoint, repo, sources)
        (logs / 'checkpoint-restoration.json').write_text(json.dumps(
            {'manifest_sources_restored_or_compared': restored, 'complete_stream_read': True}) + '\n')
    verify_sources(lean, sources)
    audit = (lean / 'Audit.lean').read_bytes()
    if hashlib.sha256(audit).hexdigest() != AUDIT_SHA or not audit.startswith(b'import SparseLowerTail\n'):
        raise ValueError('Original axiom audit policy differs')
    spec = importlib.util.spec_from_file_location('assembly_plan', lean / 'tools/build_bounded.py')
    plan = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(plan)
    graph = plan.dependency_graph(TARGET)
    if set(graph) != set(sources):
        raise ValueError('Dependency graph differs from prior source manifest')
    (logs / 'source-hashes-before.txt').write_text(
        'All prior combined dependencies and the original audit policy matched before build.\n')
    profile = lean / 'lakefile.yale.toml'
    expected_profile = stack_profile((lean / 'lakefile.toml').read_text(), a.memory_mib, 65536)
    if profile.exists() and profile.read_text() != expected_profile:
        raise ValueError('Existing bounded resource profile differs')
    if not profile.exists():
        profile.write_text(expected_profile)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    def run(argv, name):
        with (logs / name).open('w') as out:
            subprocess.run(argv, cwd=lean, env=env, stdout=out,
                           stderr=subprocess.STDOUT, check=True)
    run(['python3', str(Path(__file__).with_name('build_ready_batches.py')),
         '--repo', str(repo), '--target', TARGET, '--logs', str(logs / 'combined-build'),
         '--lakefile', str(profile), '--workers', str(a.workers)], 'combined-build.log')
    verify_sources(lean, sources)
    if (lean / 'Audit.lean').read_bytes() != audit:
        raise ValueError('Original audit source changed during build')
    audit_path = logs / 'AuditCompleted.lean'
    audit_path.write_bytes(audit.replace(b'import SparseLowerTail\n',
                                       ('import ' + TARGET + '\n').encode(), 1))
    run(['lake', '--file', str(profile), 'env', 'lean', '-M' + str(a.memory_mib),
         '-j1', '-s65536', str(audit_path)], 'combined-audit.log')
    verify_sources(lean, sources)
    if (lean / 'Audit.lean').read_bytes() != audit:
        raise ValueError('Original audit source changed during audit')
    (logs / 'source-hashes-passed.txt').write_text(
        'All combined target dependencies and original axiom audit policy unchanged.\n')
    (logs / 'ASSEMBLY_SUCCESS.txt').write_text(
        'CompletedReplays full target and original namespace audit passed; all internal finite\n'
        'premises discharged, with the seven named external/classical inputs unchanged.\n')
    (logs / 'SUCCESS.txt').write_text('Full target, unchanged source hashes and axiom audit passed.\n')


if __name__ == '__main__':
    main()

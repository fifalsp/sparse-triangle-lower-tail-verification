#!/usr/bin/env python3
"""Validate transferred checkpoints and collect finished Delta proof artifacts."""
import argparse
import hashlib
import re
import tarfile
from pathlib import Path
from audit_result_archives import inspect


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(8 * 1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def validate_transfer(save, selected=None):
    entries = {}
    for line in (save / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        name = Path(name.lstrip('*')).name
        if not re.fullmatch(r'[0-9a-f]{64}', digest) or name in entries:
            raise ValueError('Invalid or duplicate transfer checksum')
        entries[name] = digest
    names = [selected] if selected else sorted(entries)
    for name in names:
        if name not in entries or sha256(save / name) != entries[name]:
            raise ValueError('Transferred archive checksum mismatch: ' + name)
    return len(names)


def collect_delta(save, root):
    """Collect only completed region logs; retain original immutable sources."""
    for result in sorted(root.glob('sparse-lean-results-*.tar.gz')):
        record = inspect(result.read_bytes(), result.name)
        if not record or not record['verified']:
            continue
        dest = save / result.name
        if dest.exists():
            if sha256(dest) != sha256(result):
                raise ValueError('Conflicting result archive: ' + result.name)
        else:
            dest.hardlink_to(result)
        job = re.fullmatch(r'sparse-lean-results-(\d+)\.tar\.gz', result.name)[1]
        checkpoint = save / f'sparse-lean-recovery-checkpoint-{job}.tar.gz'
        if checkpoint.exists():
            continue
        candidates = [root / f'run-{job}' / 'repo']
        for stage in ('abb', 'exterior', 'cover0', 'cover12'):
            candidates += [root / f'family-{stage}-{job}' / 'repo',
                           root / f'remaining-{stage}-{job}' / 'repo']
        repo = next((p for p in candidates if (p / 'SOURCE_COMMIT').is_file()), None)
        if repo is None:
            raise ValueError('Missing persistent source for completed Delta job ' + job)
        kind = record['kind']
        if kind == 'cover':
            subtree = f'lean/SparseLowerTail/Section05/CoverJobReplay/Job{int(record["key"].split(":")[1]):02d}Full'
        elif kind == 'apex':
            subtree = 'lean/SparseLowerTail/Section05/ApexReplay/F' + record['key'].split(':')[1]
        elif kind == 'abb':
            subtree = 'lean/SparseLowerTail/Section08/FamilyABBReplay/Full'
        elif kind == 'exterior':
            subtree = 'lean/SparseLowerTail/Section08/FamilyExteriorReplay/Full'
        else:
            raise ValueError('Unexpected Delta result kind: ' + kind)
        temporary = checkpoint.with_suffix(checkpoint.suffix + '.partial')
        with tarfile.open(temporary, 'w:gz', compresslevel=1) as archive:
            for relative in (subtree, 'lean/.lake/build', 'SOURCE_COMMIT'):
                archive.add(repo / relative, arcname=relative)
        temporary.rename(checkpoint)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--save', type=Path, required=True)
    parser.add_argument('--checkpoint')
    parser.add_argument('--collect-delta', type=Path)
    args = parser.parse_args()
    checked = validate_transfer(args.save, args.checkpoint)
    print(f'Validated {checked} transferred archives.', flush=True)
    if args.collect_delta:
        collect_delta(args.save, args.collect_delta)


if __name__ == '__main__':
    main()

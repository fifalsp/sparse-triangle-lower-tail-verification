#!/usr/bin/env python3
"""Restore generated family proofs and cache, retaining handwritten sources."""
import shutil
import tarfile
from pathlib import Path


def restore(archive, root, family):
    subtree = {'abb': 'FamilyABBReplay', 'exterior': 'FamilyExteriorReplay'}[family]
    prefixes = ('lean/SparseLowerTail/Section08/'+subtree+'/Full/',
                'lean/.lake/build/')
    count = 0
    with tarfile.open(archive, 'r|gz') as stream:
        for member in stream:
            if not member.isfile():
                continue
            path = Path(member.name)
            if path.is_absolute() or '..' in path.parts:
                raise ValueError('Unsafe checkpoint path: '+member.name)
            if not member.name.startswith(prefixes):
                continue
            dest = root / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            with dest.open('wb') as output:
                shutil.copyfileobj(stream.extractfile(member), output)
            count += 1
    return count

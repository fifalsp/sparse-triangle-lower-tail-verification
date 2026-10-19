#!/usr/bin/env python3
"""Check that proof-map file and declaration links resolve in the built Lean project."""
import json
import re
import subprocess
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parents[1]
project = root/'lean'
mapping = json.loads((project/'proof-map.json').read_text())
names = set()
labels = set()
ledger = (project/'ASSUMPTIONS.md').read_text()
recorded_inputs = set(re.findall(r'`((?:classical|external):[^`]+)`', ledger))
for entry in mapping['entries']:
    label = entry['paper_label']
    if label in labels:
        raise SystemExit(f'Duplicate map label: {label}')
    labels.add(label)
    for dependency in entry['explicit_inputs']:
        if dependency.startswith(('classical:', 'external:')) and dependency not in recorded_inputs:
            raise SystemExit(f'Unrecorded external input for {label}: {dependency}')
    for name in entry['lean_declarations']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name):
            raise SystemExit(f'Unsupported declaration name: {name}')
        names.add(name)
    for file in entry['lean_files']:
        path = (project/file).resolve()
        if not path.is_relative_to(project) or not path.is_file():
            raise SystemExit(f'Missing/invalid linked file: {file}')
if not names:
    raise SystemExit('No declarations linked')
with tempfile.TemporaryDirectory(prefix='sparse-lean-map-') as directory:
    check = Path(directory)/'MapCheck.lean'
    check.write_text('import SparseLowerTail\n' + '\n'.join('#check '+n for n in sorted(names))+'\n')
    result = subprocess.run(['lake','env','lean',str(check)],cwd=project,capture_output=True,text=True)
    if result.returncode:
        raise SystemExit(result.stdout+result.stderr)
print(f'Proof-map links passed: {len(labels)} labels, {len(names)} Lean declarations.')

"""Independently compare manuscript certificate tables with data/cover.json.

Usage: python tools/compare_draft.py /path/to/arxiv_v1.tex
The manuscript is read only. Success reports its SHA-256 and exact input match.
Supports the current three coefficient tables and the older two-table layout.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json
import re
import sys

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use Python -O or PYTHONOPTIMIZE.')

NAMES = ['F1','F2','F3','F4','F5','F6','S1','S2','S3','R1','B1','B2']


def table_block(source, label):
    marker = r'\label{' + label + '}'
    if source.count(marker) != 1:
        raise ValueError(f'Expected one table label: {label}')
    return source.split(marker, 1)[1].split(r'\end{table}', 1)[0]


def table_rows(source, label):
    block = table_block(source, label)
    rows = {}
    for line in block.splitlines():
        if any(line.lstrip().startswith(name + ' &') for name in NAMES):
            name, *entries = line.split('&')
            name = name.strip()
            if name in rows:
                raise ValueError(f'Duplicate row {name} in {label}')
            rows[name] = [entry.strip() for entry in entries]
    if set(rows) != set(NAMES):
        raise ValueError(f'Incomplete cell table: {label}')
    return rows


def number(entry):
    if '*' in entry:
        return None
    entry = entry.replace(r'\\', '').strip()
    if not entry:
        return None
    match = re.fullmatch(r'\\text(?:tt|normal)\{([^}]+)\}', entry)
    if match:
        entry = match.group(1)
    entry = entry.strip('$').strip()
    entry = re.sub(r'\\cdot\s*10\^\{([+-]?\d+)\}', r'e\1', entry)
    if not re.fullmatch(r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?', entry):
        raise ValueError(f'Unrecognized numeric table entry: {entry!r}')
    return entry


def dyadic(decimal):
    return str(Fraction(float(decimal)))


def extract(source):
    coefficient_labels = ['tab:coef1', 'tab:coef2']
    if r'\label{tab:coef3}' in source:
        coefficient_labels.append('tab:coef3')
    coefficients = {name: [None] * 12 for name in NAMES}
    seen_indices = []
    for label in coefficient_labels:
        indices = [int(i) for i in re.findall(r'\\theta_\{(\d+)\}', table_block(source, label))]
        if not indices or len(set(indices)) != len(indices) or any(i not in range(12) for i in indices):
            raise ValueError(f'Invalid multiplier headers in {label}')
        seen_indices += indices
        for name, row in table_rows(source, label).items():
            if len(row) != len(indices):
                raise ValueError(f'Wrong coefficient count for {name} in {label}')
            for index, entry in zip(indices, row):
                coefficients[name][index] = number(entry)
    if sorted(seen_indices) != list(range(12)):
        raise ValueError('Multiplier tables must specify every index 0 through 11 exactly once')
    params = table_rows(source, 'tab:cellparams')
    vertices = table_rows(source, 'tab:cells')
    cells = {}
    for name in NAMES:
        theta = coefficients[name]
        if len(theta) != 12:
            raise ValueError(f'{name} does not have 12 multiplier entries')
        if len(params[name]) != 4 or len(vertices[name]) != 2:
            raise ValueError(f'Unexpected table width for {name}')
        lam, numerator, targets, radius = params[name]
        typ, raw = vertices[name]
        if typ == 'rectangle':
            pairs = re.findall(r'\[([^,]+),([^\]]+)\]', raw)
            (ml, mh), (fl, fh) = pairs
            points = [(ml,fl),(mh,fl),(mh,fh),(ml,fh)]
        else:
            points = re.findall(r'\(([^,]+),([^\)]+)\)', raw)
        apex = typ in ('triangle', 'fan triangle')
        target_strings = re.findall(r'\\texttt\{([^}]+)\}', targets)
        if len(points) != (2 if apex else 4) or len(target_strings) != len(points):
            raise ValueError(f'Wrong vertex/target count for {name}')
        cells[name] = {
            'theta': [None if x is None else dyadic(x) for x in theta],
            'lam': dyadic(number(lam)),
            'Q': str(Fraction(int(number(numerator)), 1024)),
            'vertices': [[dyadic(x),dyadic(y)] for x,y in points],
            'targets': [dyadic(x) for x in target_strings],
            'apex': apex,
            'local_radii': [dyadic('0.03'),dyadic(number(radius))] if apex else None,
        }
        if not apex and number(radius) is not None:
            raise ValueError(f'Unexpected local radius for nonapex cell {name}')
    return cells


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manuscript', type=Path)
    args = parser.parse_args()
    if sys.float_info.radix != 2 or sys.float_info.mant_dig != 53:
        raise RuntimeError('The decimal-to-binary64 comparison requires IEEE binary64 floats.')
    raw = args.manuscript.read_bytes()
    cells = extract(raw.decode('utf-8'))
    stored = json.loads((Path(__file__).resolve().parents[1]/'data'/'cover.json').read_text())['cells']
    matches = cells == stored
    print(json.dumps({'draft_sha256': hashlib.sha256(raw).hexdigest(), 'match': matches}, indent=2))
    if not matches:
        differing = [name for name in NAMES if cells.get(name) != stored.get(name)]
        print('Differing cells: ' + ', '.join(differing), file=sys.stderr)
        raise SystemExit(1)


if __name__ == '__main__':
    main()

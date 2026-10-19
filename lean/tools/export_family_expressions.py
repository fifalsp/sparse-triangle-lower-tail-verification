#!/usr/bin/env python3
"""Export the checked Lean expression definitions as an UNTRUSTED search DAG.

Structural sharing preserves the expression tree's evaluation order. No
algebraic simplification or floating-point calculation is performed here.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ['Numerics/RationalExpr.lean','Numerics/RationalExprCalculus.lean',
           'Section08/FamilyCoefficientIntervals.lean','Section08/FamilyParameterCalculus.lean',
           'Section08/FamilyParameterIntervals.lean','Section08/FamilyWeightIntervals.lean',
           'Section08/FamilyLocalFactoredIntervals.lean']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'data/family-expression-dag.json.gz')
    args = p.parse_args()
    raw = subprocess.run(['lake','env','lean','tools/ExportFamilyExpressions.lean'],cwd=ROOT,
                         text=True,capture_output=True,check=True)
    tree = json.loads(raw.stdout)
    nodes, known = [], {}
    def intern(e):
        if e[0] in ('r','v'):
            key = tuple(e)
        elif e[0] in ('+','*'):
            key = (e[0],intern(e[1]),intern(e[2]))
        elif e[0] in ('-','/'):
            key = (e[0],intern(e[1]))
        else:
            raise ValueError('Unknown expression node')
        if key not in known:
            known[key] = len(nodes)
            nodes.append(key)
        return known[key]
    roots = dict(delta=intern(tree['delta']),
                 derivatives=[[intern(e) for e in row] for row in tree['derivatives']],
                 weights=[intern(e) for e in tree['weights']],
                 gradient_weights=[[intern(e) for e in row] for row in tree['gradient_weights']],
                 hessian=[[intern(e) for e in row] for row in tree['hessian']])
    data = dict(schema=1,trust_status=tree['trust_status'],nodes=nodes,roots=roots,
                reference_smoke=tree['reference_smoke'],
                source_sha256={x:hashlib.sha256((ROOT/'SparseLowerTail'/x).read_bytes()).hexdigest()
                               for x in SOURCES})
    payload = (json.dumps(data,separators=(',',':'),sort_keys=True)+'\n').encode()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_bytes(gzip.compress(payload,mtime=0))
    print(json.dumps(dict(nodes=len(nodes),bytes=len(payload),compressed_bytes=args.output.stat().st_size,
                          sha256=hashlib.sha256(payload).hexdigest(),trust_status=data['trust_status'])))


if __name__=='__main__':
    main()

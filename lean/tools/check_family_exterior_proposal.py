#!/usr/bin/env python3
"""Check proposal-tree consistency and recompute exact numerical acceptances.

This is NOT a Lean proof. It detects stale data, missing boxes, bad partitions,
and arithmetic disagreements before the formal replay is generated.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path
import time
from family_exterior_arithmetic import Arithmetic
from propose_family_exterior_cover import INITIAL


def check(path):
    started=time.monotonic()
    payload=gzip.decompress(Path(path).read_bytes())
    data=json.loads(payload)
    a=Arithmetic()
    if data['expression_sha256']!=a.payload_sha256:
        raise ValueError('Expression bundle changed')
    initial=tuple(list(map(F,x)) for x in data['initial'])
    if initial!=INITIAL:raise ValueError('Wrong initial domain')
    stack=[initial];seen=set();minimum=None
    for code in data['tree']:
        if not stack:raise ValueError('Extra nodes after completed tree')
        lo,hi=stack.pop()
        if code>=0:
            if code not in range(4):raise ValueError('Invalid split axis')
            mid=(lo[code]+hi[code])/2
            if not lo[code]<mid<hi[code]:raise ValueError('Degenerate split')
            lu,rl=hi.copy(),lo.copy();lu[code]=mid;rl[code]=mid
            stack.extend([(rl,hi),(lo,lu)])
            continue
        index=-code-1
        if index in seen or not 0<=index<len(data['leaves']):
            raise ValueError('Duplicate or missing leaf index')
        seen.add(index)
        row=data['leaves'][index]
        if (list(map(F,row['lower'])),list(map(F,row['upper'])))!=(lo,hi):
            raise ValueError('Leaf box differs from exact subdivision')
        if row['kind']=='ordered-empty':
            if not (hi[1]<lo[2] or hi[2]<lo[3]):raise ValueError('Not empty in the ordered domain')
            continue
        result=a.evaluate(lo,hi)
        if row['kind']!=result['kind'] or result['kind']=='split':
            raise ValueError('Acceptance does not replay')
        if row['kind']=='taylor':
            if F(row['margin'])!=result['margin'] or result['margin']<=0:
                raise ValueError('Positive margin does not replay')
            if row['choices']!=result['choices'] or list(map(F,row['beta']))!=result['beta']:
                raise ValueError('Quadratic candidates differ')
            minimum=result['margin'] if minimum is None else min(minimum,result['margin'])
    if len(seen)!=len(data['leaves']):raise ValueError('Unused leaf data')
    frontier=[(list(map(F,l)),list(map(F,u))) for l,u in data['frontier']]
    if stack!=frontier:raise ValueError('Frontier does not match unprocessed tree')
    counts=dict(Counter(r['kind'] for r in data['leaves']))
    if data['nodes']!=len(data['tree']) or data['counts']!=counts:
        raise ValueError('Summary does not match actual tree')
    return dict(status='consistent_untrusted_proposal',complete_proposal=not stack,
                nodes=len(data['tree']),leaves=len(seen),frontier=len(stack),counts=counts,
                minimum_taylor_margin=str(minimum),seconds=time.monotonic()-started,
                proposal_sha256=hashlib.sha256(payload).hexdigest(),
                trust_status='Python consistency only; all leaves, local contacts, and coverage still require Lean')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('proposal',type=Path)
    p.add_argument('--report',type=Path)
    args=p.parse_args()
    result=check(args.proposal)
    text=json.dumps(result,indent=2)+'\n'
    if args.report:args.report.write_text(text)
    print(text,end='')


if __name__=='__main__':
    main()

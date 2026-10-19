#!/usr/bin/env python3
"""UNTRUSTED exact-rational subdivision of the ordered compact family domain.

Each search acceptance is proposal data. The two local neighborhoods and
all exterior leaves must be formally proved, together with tree coverage.
Bounded/resumable; this script does not start any Lean replay.
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

ROOT=Path(__file__).resolve().parents[1]
INITIAL=([F(39,10),F(0),F(0),F(0)],[F(19,2),F(12),F(12),F(12)])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--budget',type=int,default=5000,help='Maximum total tree nodes, including resumed nodes')
    p.add_argument('--seconds',type=float,default=30,help='Wall-time budget for this invocation')
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--resume',type=Path)
    args=p.parse_args()
    a=Arithmetic()
    codehash={name:hashlib.sha256((ROOT/'tools'/name).read_bytes()).hexdigest()
              for name in ['family_exterior_arithmetic.py','propose_family_exterior_cover.py']}
    if args.resume:
        old=json.loads(gzip.decompress(args.resume.read_bytes()))
        if old['expression_sha256']!=a.payload_sha256 or old['code_sha256']!=codehash:
            raise ValueError('Cannot resume with different expressions or arithmetic/search code')
        tree,leaves=old['tree'],old['leaves']
        stack=[(list(map(F,l)),list(map(F,u))) for l,u in old['frontier']]
        elapsed_before=old['seconds']
    else:
        tree,leaves,stack,elapsed_before=[],[],[INITIAL],0
    started=time.monotonic()
    while stack and len(tree)<args.budget and time.monotonic()-started<args.seconds:
        lo,hi=stack.pop()
        if hi[1]<lo[2] or hi[2]<lo[3]:
            result=dict(kind='ordered-empty')
        else:
            result=a.evaluate(lo,hi)
        if result['kind']=='split':
            axis=result['axis'];mid=(lo[axis]+hi[axis])/2
            if not lo[axis]<mid<hi[axis]:
                stack.append((lo,hi))
                raise RuntimeError('Cannot split unresolved point box')
            tree.append(axis)
            left_hi,right_lo=hi.copy(),lo.copy()
            left_hi[axis]=mid;right_lo[axis]=mid
            stack.append((right_lo,hi));stack.append((lo,left_hi))
        else:
            tree.append(-len(leaves)-1)
            row=dict(kind=result['kind'],lower=list(map(str,lo)),upper=list(map(str,hi)))
            if result['kind']=='taylor':
                row.update(margin=str(result['margin']),choices=result['choices'],beta=list(map(str,result['beta'])))
            leaves.append(row)
    elapsed=elapsed_before+time.monotonic()-started
    data=dict(schema=1,scope='Ordered q1>=q2>=q3 in [0,12]^3; L in [39/10,19/2]',
              trust_status='UNTRUSTED proposal only; all leaves, contacts, and coverage need Lean proofs',
              expression_sha256=a.payload_sha256,code_sha256=codehash,
              initial=[list(map(str,INITIAL[0])),list(map(str,INITIAL[1]))],
              tree=tree,leaves=leaves,frontier=[[list(map(str,l)),list(map(str,u))] for l,u in stack],
              nodes=len(tree),counts=dict(Counter(row['kind'] for row in leaves)),seconds=elapsed)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    payload=(json.dumps(data,separators=(',',':'),sort_keys=True)+'\n').encode()
    args.output.write_bytes(gzip.compress(payload,mtime=0))
    print(json.dumps({k:data[k] for k in ['nodes','counts','seconds','trust_status']} |
                     dict(frontier=len(stack),compressed_bytes=args.output.stat().st_size,
                          proposal_sha256=hashlib.sha256(payload).hexdigest())))


if __name__=='__main__':
    main()

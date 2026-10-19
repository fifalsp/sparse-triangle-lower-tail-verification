#!/usr/bin/env python3
"""Bounded/resumable UNTRUSTED subdivision for any of the 36 nonapex jobs.

The complete tree and all numeric leaves still require Lean replay.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path
import time
from cover_job_arithmetic import Arithmetic


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--job',type=int,choices=range(36),required=True)
    p.add_argument('--seconds',type=float,default=30)
    p.add_argument('--budget',type=int,default=5000,help='New tree nodes for this invocation')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--resume',action='store_true')
    args=p.parse_args();a=Arithmetic();a.check_reference();job=a.jobs[args.job];q=F(job['Q'])
    source=Path(__file__).resolve().parent
    hashes={n:hashlib.sha256((source/n).read_bytes()).hexdigest() for n in
            ['cover_job_arithmetic.py','propose_cover_job.py','generate_exp_endpoints.py']}
    tree=[];frontier=[([F(0)]*3,[q]*3)]
    if args.resume:
        old=json.loads(gzip.decompress(args.output.read_bytes()))
        if old['job']!=args.job or old['expression_sha256']!=a.sha256 or old['code_sha256']!=hashes:
            raise ValueError('Resume job or implementation mismatch')
        tree=old['preorder'];frontier=[(list(map(F,l)),list(map(F,u))) for l,u in old['frontier']]
    start=time.monotonic();initial=len(tree)
    while frontier and len(tree)-initial<args.budget and time.monotonic()-start<args.seconds:
        lo,hi=frontier.pop();lo=[max(lo),max(lo[1:]),lo[2]];hi=[hi[0],min(hi[:2]),min(hi)]
        if any(l>u for l,u in zip(lo,hi)):tree.append(4);continue
        result=a.evaluate(args.job,lo,hi)
        if result['code'] is not None:tree.append(result['code'])
        else:
            axis=max(range(3),key=lambda i:hi[i]-lo[i]);mid=(lo[axis]+hi[axis])/2
            if not lo[axis]<mid<hi[axis]:raise ValueError('Unresolved point; not evidence of negativity')
            tree.append(5+axis);lh,rl=hi.copy(),lo.copy();lh[axis]=rl[axis]=mid
            frontier.extend([(rl,hi),(lo,lh)])
    data=dict(schema=1,trust_status='UNTRUSTED proposal; full Lean leaves and coverage remain required',
              job=args.job,cell=job['cell_name'],Q=str(q),expression_sha256=a.sha256,code_sha256=hashes,
              preorder=tree,frontier=[(list(map(str,l)),list(map(str,u))) for l,u in frontier],
              status='complete proposal' if not frontier else 'incomplete proposal',
              counts=dict(Counter(tree)),seconds_this_run=time.monotonic()-start)
    payload=(json.dumps(data,separators=(',',':'),sort_keys=True)+'\n').encode()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_bytes(gzip.compress(payload,mtime=0))
    print(json.dumps({k:v for k,v in data.items() if k not in ('preorder','frontier','code_sha256')} |
                     dict(nodes=len(tree),frontier=len(frontier),sha256=hashlib.sha256(payload).hexdigest())))


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Replay Proposition prop:family and its local/compact appendix checks.

--quick checks exact tangencies and rational identities, the elementary endpoint
and tail inequalities, and coefficient signs. It does NOT prove the compact
positivity claim. The default run additionally proves both local Hessian claims
and the entire compact cover; only an empty stack permits status=complete.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not run with -O or PYTHONOPTIMIZE.')

import flint
from flint import arb,ctx
import core
import selfcheck

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
PRECISION=128
ctx.prec=PRECISION
L0=3.9  # binary64 value is below the exact decimal 39/10.
L1=9.5
DELTA=0.1  # exact binary64 input as specified in the draft.


def write(path, data):
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    tmp.replace(path)


def digest_files():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('*.py'))}


def quick_checks(output):
    series_check=selfcheck.run()
    log=output/'symbolic.log'
    with log.open('w') as stream:
        result=subprocess.run([sys.executable,str(HERE/'symbolic.py')],stdout=stream,stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Symbolic verification failed; see {log}')
    assert arb(L0)<=arb(39)/10 and arb(L1)>=arb(19)/2
    assert arb(DELTA)>arb(1)/10
    assert (-arb('9.5')).exp()<arb('0.000075')
    assert (-arb('3.9')).exp()>arb('0.0201')
    assert (-arb('3.9')).exp()<arb(1)/40
    qa_bound=arb('9.5')+2*arb('3.9')*(-arb('3.9')).exp()/(1-(-arb('3.9')).exp())**2
    assert qa_bound+2<arb('11.67') and qa_bound+2<12
    # Explicit elementary bounds from certcoef/certtail, evaluated outward.
    assert arb(40).log()>arb('3.68') and arb(40).log()<arb('3.69')
    assert arb(40).log()/40<arb('0.09225')
    gbound=1-arb('3.68')+6*arb('0.09225')**2+3*arb('0.09225')/1600+arb(3)/1600
    assert gbound<arb('-2.6')
    assert arb(2).exp()>4
    # Also check coefficient signs, mean sign, tail threshold, and derivative
    # directly over all L by interval bisection; no sampling enters this test.
    stack=[(L0,L1,0)];leaves=0;nodes=0
    while stack:
        lo,hi,depth=stack.pop();nodes+=1
        c=core.coefficients(core.ball(lo,hi));Q=c['qa']+2
        good=(c['D']<0 and c['c1']>0 and c['c2']>0 and c['c3']<0 and c['c4']>0
              and c['c1']+c['c2']+c['c3']*c['m']*c['m']/c['t']<0
              and Q>1+1/c['A'] and Q>2+arb(2).sqrt()
              and -c['c3']-(-Q).exp()*(c['c1']+c['c4']*(Q*Q-2*Q))>0)
        if good:
            leaves+=1
        else:
            if depth>=30:
                raise RuntimeError('Unresolved coefficient/tail interval.')
            mid=(lo+hi)/2
            if not lo<mid<hi:
                raise RuntimeError('Degenerate coefficient interval.')
            stack.extend([(lo,mid,depth+1),(mid,hi,depth+1)])
    data={'status':'complete','scope':'symbolic identities, endpoint and tail inequalities, coefficient signs; excludes compact/local Hessian proofs',
          'series_check':series_check,'nodes':nodes,'leaves':leaves,'pending':0,'qa_plus_two_upper':str((qa_bound+2).upper()),'code_sha256':digest_files()}
    write(output/'quick.json',data)
    return data


def local_check(box, pattern):
    lo,hi=box
    c,_,_,_=core.enclosure(lo[0],hi[0])
    qs=[c['qa' if pattern==1 or i==0 else 'qb']+core.ball(lo[i+1],hi[i+1]) for i in range(3)]
    return core.positive_definite(core.hessian(c,qs,scaled=True))


def subdivide(kind, max_nodes, output, pattern=None):
    start=time.monotonic();n=0;counts={};maxstack=1
    if kind=='local':
        stack=[((L0,-DELTA,-DELTA,-DELTA),(L1,DELTA,DELTA,DELTA))]
        name='local'+str(pattern)
    else:
        stack=[((L0,0.,0.,0.),(L1,12.,12.,12.))]
        name='compact'
    digest=hashlib.sha256()
    next_progress=start+30
    while stack and n<max_nodes:
        box=core.tighten(stack.pop(),pattern if kind=='local' else None)
        if box is None:
            counts['order-prune']=counts.get('order-prune',0)+1
            continue
        n+=1
        if kind=='local':
            ok=local_check(box,pattern)
            index=max(range(4),key=lambda i:(box[1][i]-box[0][i])*(8 if i==0 else 4))
            reason='hessian' if ok else 'split'
        else:
            ok,index,reason=core.compact_test(box,arb(DELTA))
        counts[reason]=counts.get(reason,0)+1
        if ok:
            digest.update(repr((box,reason)).encode())
        else:
            stack.extend(core.split(box,index));maxstack=max(maxstack,len(stack))
        now=time.monotonic()
        if now>=next_progress:
            print(json.dumps({'part':name,'nodes':n,'pending':len(stack),'seconds':now-start,'counts':counts}),flush=True)
            next_progress=now+30
    data={'status':'complete' if not stack else 'incomplete','part':name,'L_interval':[L0,L1],
          'q_cube':[0,12] if kind=='compact' else None,'radius_binary64':DELTA if kind=='local' else None,
          'radius_exact_ratio':list(DELTA.as_integer_ratio()) if kind=='local' else None,
          'pattern':pattern,'precision_bits':ctx.prec,'nodes':n,'pending':len(stack),'counts':counts,
          'maxstack':maxstack,'seconds':time.monotonic()-start,'accepted_partition_sha256':digest.hexdigest(),
          'remaining_boxes':stack,'code_sha256':digest_files()}
    write(output/(name+'.json'),data)
    print(json.dumps({k:data[k] for k in ('part','status','nodes','pending','seconds')}),flush=True)
    if stack:
        raise RuntimeError(f'{name}: node budget exhausted with {len(stack)} unresolved boxes; this is not a proof.')
    return data


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick',action='store_true')
    parser.add_argument('--max-nodes',type=int,default=20000000,help='Node limit for EACH of local1, local2, compact.')
    parser.add_argument('--output-dir',type=Path,default=Path(os.environ.get('SPARSE_VERIFICATION_RESULTS',REPO/'results'))/'family')
    args=parser.parse_args()
    if args.max_nodes<1:
        parser.error('--max-nodes must be positive')
    output=args.output_dir.resolve();output.mkdir(parents=True,exist_ok=True)
    start=time.monotonic()
    manifest={'status':'running','scope':'quick only' if args.quick else 'full Proposition prop:family verification',
              'python':sys.version,'python_flint':flint.__version__,'flint':flint.__FLINT_VERSION__,
              'platform':platform.platform(),'precision_bits':ctx.prec,'code_sha256':digest_files(),'checks':{}}
    write(output/'family.json',manifest)
    try:
        manifest['checks']['quick']=quick_checks(output)
        if not args.quick:
            # Local certificates are computed during this invocation. No saved
            # status or external report is trusted to enable membership tests.
            manifest['checks']['local1']=subdivide('local',args.max_nodes,output,1)
            manifest['checks']['local2']=subdivide('local',args.max_nodes,output,2)
            manifest['checks']['compact']=subdivide('compact',args.max_nodes,output)
        if digest_files()!=manifest['code_sha256']:
            raise RuntimeError('Verifier source changed during the run.')
        manifest['status']='quick_checks_passed' if args.quick else 'complete'
    except BaseException as exc:
        manifest['status']='incomplete';manifest['error']=repr(exc)
        raise
    finally:
        manifest['seconds']=time.monotonic()-start
        write(output/'family.json',manifest)
        print(json.dumps({k:manifest[k] for k in ('status','scope','seconds')}),flush=True)


if __name__=='__main__':
    main()

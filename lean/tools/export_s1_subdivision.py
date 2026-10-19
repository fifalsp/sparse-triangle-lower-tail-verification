#!/usr/bin/env python3
"""Export the existing Arb search as an UNTRUSTED compact subdivision proposal.

Run with ../.venv/bin/python tools/export_s1_subdivision.py from lean/.
The exported leaf methods are NOT Lean proofs. Their role is to preserve the
complete search tree for later checked Taylor replay, instead of only a digest.
"""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,sys,time
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'verification/cover'))
import verify_endpoint as ve
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,default=ROOT/'lean/data/s1-vertex0-subdivision-proposal.json')
parser.add_argument('--budget',type=int,default=2000000)
a=parser.parse_args()
c,cell,theta,lam,_=ve.model('S1')
m,F=map(lambda v:ve.A(Fraction(v)),cell['vertices'][0])
target=3*ve.A(Fraction(cell['targets'][0]));Q=float(Fraction(cell['Q']))
# Preorder: 0 direct,1 Taylor1,2 Taylor2,3 Taylor3,4 empty,
# 5/6/7 split on axes 0/1/2. Each split has exactly two descendants.
codes={'direct':0,'Taylor1':1,'Taylor2':2,'Taylor3':3,'empty':4}
stack=[((0.,0.,0.),(Q,Q,Q))];tree=[];counts={};bounds={};start=time.monotonic()
while stack and len(tree)<a.budget:
 lo,hi=stack.pop()
 lo=(max(lo[0],lo[1],lo[2]),max(lo[1],lo[2]),lo[2])
 hi=(hi[0],min(hi[0],hi[1]),min(hi[0],hi[1],hi[2]))
 if any(l>h for l,h in zip(lo,hi)):kind,lower='empty',None
 else:kind,lower=ve.analyze(lo,hi,c,theta,lam,m,F,target,[])
 if kind:
  tree.append(codes[kind]);counts[kind]=counts.get(kind,0)+1
  if lower is not None and (kind not in bounds or ve.A(lower)<ve.A(bounds[kind])):bounds[kind]=lower
  continue
 axis=max(range(3),key=lambda i:hi[i]-lo[i]);mid=(lo[axis]+hi[axis])/2
 if not lo[axis]<mid<hi[axis]:raise RuntimeError('Unresolved non-splittable box')
 tree.append(5+axis);counts['split']=counts.get('split',0)+1
 lh=list(hi);rl=list(lo);lh[axis]=mid;rl[axis]=mid
 stack.extend([(tuple(rl),hi),(lo,tuple(lh))])
if stack:raise RuntimeError(f'Incomplete proposal: {len(stack)} pending boxes; no file written')
# Structural check only: do not claim analytic validation from these tags.
pending=1
for i,code in enumerate(tree):
 if pending<=0:raise RuntimeError('Trailing nodes in preorder tree')
 pending+=1 if code>=5 else -1
if pending:raise RuntimeError('Missing nodes in preorder tree')
out={'trust_status':'UNTRUSTED SEARCH PROPOSAL: Taylor/direct leaf tags are not Lean proofs',
 'cell':'S1','vertex':0,'Q':cell['Q'],'encoding':'preorder; 0 direct,1 Taylor1,2 Taylor2,3 Taylor3,4 empty,5/6/7 binary split axis0/1/2',
 'geometry':'At every node first tighten bounds using q0>=q1>=q2; split longest tightened coordinate at its exact dyadic midpoint; left child precedes right child.',
 'node_count':len(tree),'leaf_count':sum(v for k,v in counts.items() if k!='split'),
 'counts':counts,'search_seconds':time.monotonic()-start,'scaled_target':str(target),
 'arb_lower_bound_proposals':bounds,'inputs_sha256':hashlib.sha256((ROOT/'data/cover.json').read_bytes()).hexdigest(),
 'preorder':tree}
a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(json.dumps(out,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['preorder','arb_lower_bound_proposals']},indent=2))

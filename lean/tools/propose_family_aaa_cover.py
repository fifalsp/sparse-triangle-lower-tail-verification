#!/usr/bin/env python3
"""Untrusted exact dyadic proposal of all-L local AAA leaves, radius1/10.
Every accepted leaf is later replayed by Lean; these tests alone prove nothing.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import json,time
from generate_family_leaf_example import I,S,ep,expbox,coeff
from s1_expr_model import E,c,v

def phi_expr():
 q=[v(i) for i in range(3)];x=[v(i+3) for i in range(3)]
 return c(3)*v(6)+v(7)*(x[0]+x[1]+x[2])-v(8)*(q[0]*x[0]+q[1]*x[1]+q[2]*x[2])-v(9)*(q[0]+q[1]+q[2])+v(10)*(q[0]*q[0]*x[0]+q[1]*q[1]*x[1]+q[2]*q[2]*x[2])+v(11)*(x[0]*x[1]+x[1]*x[2]+x[2]*x[0])+x[0]*x[1]*x[2]*(1-v(12)*(q[0]+q[1]+q[2]))
@lru_cache(None)
def diff(e,i):
 op,*a=e.t
 if op=='c':return c(0)
 if op=='v':return c(1) if a[0]==i else -v(i+3) if a[0]==i+3 else c(0)
 if op=='+':return diff(a[0],i)+diff(a[1],i)
 if op=='-':return -diff(a[0],i)
 return diff(a[0],i)*a[1]+a[0]*diff(a[1],i)
H=[[diff(diff(phi_expr(),i),j) for j in range(3)] for i in range(3)]
def eval_hessian(box):
 q=box[:3];x=box[3:6];c0,c1,c2,c3,c4,mu3,A=box[6:]
 G=x[0]*x[1]*x[2]*(1+2*A-A*(q[0]+q[1]+q[2]))
 return [[x[i]*(c1+c2*(2-q[i])+c4*((q[i]-2)**2-2))+mu3*x[i]*(sum((x[k] for k in range(3) if k!=i),I(0)))+G if i==j else mu3*x[i]*x[j]+G for j in range(3)] for i in range(3)]

def leaf(lo,hi):
 elo,ehi=ep(lo),ep(hi);L=I(I(lo).l,I(hi).u);z=expbox(elo,ehi)
 delta=2*z*L/(1-z)**2;dlo,dhi=ep(F(delta.l,S)),ep(F(delta.u,S));b=expbox(dlo,dhi);cs=coeff(z,L,b)
 qlo=F((lo+F(delta.l,S)-F(1,10))*10**6//1,10**6)
 qhi=F(-((-hi-F(delta.u,S)-F(1,10))*10**6//1),10**6)
 eqlo,eqhi=ep(qlo),ep(qhi);qi=I(I(qlo).l,I(qhi).u);xi=expbox(eqlo,eqhi)
 hs=eval_hessian([qi]*3+[xi]*3+cs)
 margin=min(hs[i][i].l-sum(max(-hs[i][j].l,hs[i][j].u) for j in range(3) if j!=i) for i in range(3))
 return {'lo':str(lo),'hi':str(hi),'qlo':str(qlo),'qhi':str(qhi),'margin':margin}
def main():
 st=[(F('3.9'),F('9.5'))];leaves=[];t=time.time()
 while st:
  lo,hi=st.pop()
  try:r=leaf(lo,hi)
  except ValueError:r=None
  if r is not None and r['margin']>0:leaves.append(r)
  else:
   if hi-lo<F('0.00001'):raise RuntimeError((lo,hi,r))
   mid=(lo+hi)/2;st.extend([(mid,hi),(lo,mid)])
 out={'trust_status':'untrusted proposal; Lean replay required','radius':'1/10','leaves':leaves}
 (Path(__file__).resolve().parents[1]/'data/family-aaa-proposal.json').write_text(json.dumps(out,indent=2)+'\n')
 print(len(leaves),'leaves',time.time()-t,'seconds; minmargin',min(r['margin'] for r in leaves)/S)
if __name__=='__main__':main()

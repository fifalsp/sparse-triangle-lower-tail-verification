#!/usr/bin/env python3
"""Untrusted local Hessian diagnostics at the published radii.
Every successful candidate still needs a separate Lean kernel replay.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import json,re,math
from s1_expr_model import E,c,v,simp
from generate_family_leaf_example import I,S,ep,expbox
ROOT=Path(__file__).resolve().parents[1]
def average(xs):return (xs[0]+xs[1]+xs[2])*c(F(1,3))
def expr():
 x=[v(3+i)for i in range(3)];lg=[-v(i)for i in range(3)]
 h=[x[i]*lg[i]-x[i]+1 for i in range(3)];k=[x[i]*lg[i]-2*x[i]+2 for i in range(3)]
 g=[x[i]+v(7)*h[i]for i in range(3)];km=1+v(10)-v(9)
 et=lambda j,i:[c(1),x[i],x[i]**2,x[i]**3,x[i]*lg[i]][j]
 vt=lambda j,i:[x[i],x[i]**3,x[i]**4,x[i]*lg[i]][j]
 feat=[average(x)-v(9),x[0]*x[1]*x[2]-v(6),average(h)-v(10)]
 feat +=[average([et(j,i)*(lg[i]+v(8)*x[(i+1)%3]*x[(i+2)%3])for i in range(3)])for j in range(5)]
 feat +=[average([vt(j,i)*(k[(i+1)%3]+k[(i+2)%3]-2*km)for i in range(3)])for j in range(4)]
 ho=average([y*y for y in g])-2*average([g[0]*g[1],g[1]*g[2],g[2]*g[0]])+(v(9)+v(7)*v(10))**2
 total=c(0)
 for i in reversed(range(12)):total=v(11+i)*feat[i]+total
 return -total-v(23)*ho
@lru_cache(None)
def diff(e,i):
 op,*a=e.t
 if op=='c':return c(0)
 if op=='v':return c(1)if a[0]==i else -v(i+3)if a[0]==i+3 else c(0)
 if op=='+':return diff(a[0],i)+diff(a[1],i)
 if op=='-':return -diff(a[0],i)
 return diff(a[0],i)*a[1]+a[0]*diff(a[1],i)
def evaluate(e,box):
 @lru_cache(None)
 def run(e):
  op,*a=e.t
  if op=='c':return I(a[0])
  if op=='v':return box[a[0]]
  if op=='+':return run(a[0])+run(a[1])
  if op=='-':return -run(a[0])
  return run(a[0])*run(a[1])
 return run(e)
def main():
 src=(ROOT/'SparseLowerTail/Section05/ApexPrimitiveIntervals.lean').read_text().split('def apexPrimitiveBounds',1)[1].split('theorem',1)[0]
 bounds=[(F(a),F(b))for a,b in re.findall(r'⟨([0-9/]+),([0-9/]+)⟩',src)];assert len(bounds)==9
 constants=[I(I(a).l,I(b).u)for a,b in bounds]
 data=json.loads((ROOT/'data/apex-fan-interval-proposal.json').read_text())
 cells=json.loads((ROOT.parent/'data/cover.json').read_text())['cells']
 e=expr();H=[[simp(diff(diff(e,i),j))for j in range(3)]for i in range(3)]
 third=[simp(diff(diff(diff(e,i),j),k))for i in range(3)for j in range(3)for k in range(3)]
 out=[]
 for k in range(6):
  cell=cells['F'+str(k+1)];sol=[I(*row)for row in data['solutions'][k]]
  theta=[sol[[0,2,3,4].index(j)]if j in [0,2,3,4]else I(F(t))for j,t in enumerate(cell['theta'])]
  for mixed in [False,True]:
   radius=F(cell['local_radii'][int(mixed)]);center=[bounds[0],bounds[int(mixed)],bounds[int(mixed)]]
   lows=[a-radius for a,b in center];highs=[b+radius for a,b in center]
   box=[I(I(a).l,I(b).u)for a,b in zip(lows,highs)]+[expbox(ep(a),ep(b))for a,b in zip(lows,highs)]+constants[4:]+theta+[I(F(cell['lam']))]
   hs=[[evaluate(H[i][j],box)for j in range(3)]for i in range(3)]
   mid=[[float(F(hs[i][j].l+hs[j][i].l+hs[i][j].u+hs[j][i].u,4*S))for j in range(3)]for i in range(3)]
   dot=lambda a,b:sum(a[i]*mid[i][j]*b[j]for i in range(3)for j in range(3))
   vs=[];norms=[]
   for j in range(3):
    vv=[float(i==j)for i in range(3)]
    for u,nn in zip(vs,norms):
     z=dot(u,vv)/nn;vv=[a-z*b for a,b in zip(vv,u)]
    vs.append(vv);norms.append(dot(vv,vv))
   if min(norms)<=0:raise ValueError(('nonpositive midpoint pivot',k,mixed,norms))
   T=[[F(round(vs[j][i]/math.sqrt(norms[j])*10**6),10**6)for j in range(3)]for i in range(3)]
   J=[[sum((I(T[a][i])*hs[a][b]*I(T[b][j])for a in range(3)for b in range(3)),I(0))for j in range(3)]for i in range(3)]
   margin=min(J[i][i].l-sum(max(-J[i][j].l,J[i][j].u)for j in range(3)if j!=i)for i in range(3))
   pbox=[I(I(a).l,I(b).u)for a,b in center]+[expbox(ep(a),ep(b))for a,b in center]+constants[4:]+theta+[I(F(cell['lam']))]
   ph=[[evaluate(H[i][j],pbox)for j in range(3)]for i in range(3)]
   pm=[[float(F(ph[i][j].l+ph[j][i].l+ph[i][j].u+ph[j][i].u,4*S))for j in range(3)]for i in range(3)]
   center_eig=sum(pm[i][i]for i in range(3))/3
   spread=math.sqrt((sum((pm[i][i]-center_eig)**2 for i in range(3))+2*sum(pm[i][j]**2 for i in range(3)for j in range(i+1,3)))/6)
   B=[[(pm[i][j]-(center_eig if i==j else 0))/spread for j in range(3)]for i in range(3)]
   detB=B[0][0]*(B[1][1]*B[2][2]-B[1][2]*B[2][1])-B[0][1]*(B[1][0]*B[2][2]-B[1][2]*B[2][0])+B[0][2]*(B[1][0]*B[2][1]-B[1][1]*B[2][0])
   angle=math.acos(max(-1,min(1,detB/2)))/3
   eig=center_eig+2*spread*math.cos(angle+2*math.pi/3)
   ell=F(math.floor(.9*eig*10**16),10**16)
   shifted=[[pm[i][j]-(float(ell)if i==j else 0)for j in range(3)]for i in range(3)]
   dotp=lambda a,b:sum(a[i]*shifted[i][j]*b[j]for i in range(3)for j in range(3))
   vs=[];norms=[]
   for j in range(3):
    vv=[float(i==j)for i in range(3)]
    for u,nn in zip(vs,norms):
     z=dotp(u,vv)/nn;vv=[a-z*b for a,b in zip(vv,u)]
    vs.append(vv);norms.append(dotp(vv,vv))
   if min(norms)<=0:raise ValueError(('nonpositive shifted pivot',k,mixed,norms))
   Tp=[[F(round(vs[j][i]/math.sqrt(norms[j])*10**6),10**6)for j in range(3)]for i in range(3)]
   S3=sum(max(-evaluate(g,box).l,evaluate(g,box).u)for g in third)
   taylor=3*ell-radius*F(S3,S)
   row={'fan':k,'mixed':mixed,'radius':str(radius),'lower':list(map(str,lows)),'upper':list(map(str,highs)),'transform':[[str(x)for x in r]for r in T],'margin_proposal':margin,'eigen_lower_proposal':str(ell),'shifted_transform':[[str(x)for x in r]for r in Tp],'third_sum_proposal':S3,'taylor_margin_proposal':str(taylor)}
   out.append(row);print(k+1,'ABB'if mixed else'AAA',margin/S,'ell',float(ell),'Taylor margin',float(taylor),flush=True)
 (ROOT/'data/apex-local-box-proposal.json').write_text(json.dumps({'trust_status':'untrusted diagnostics; no Lean positivity claim','boxes':out},indent=2)+'\n')
if __name__=='__main__':main()

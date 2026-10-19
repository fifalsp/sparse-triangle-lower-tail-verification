"""Untrusted exact-rational proposal model for the Lean S1 expression checker.
No output of this module is accepted without the corresponding Lean proof.
"""
from fractions import Fraction as F
from decimal import Decimal,localcontext
from functools import lru_cache
from pathlib import Path
import json

@lru_cache(None)
def c(x):return E(('c',F(x)))
@lru_cache(None)
def v(i):return E(('v',i))
class E:
 def __init__(self,t):self.t=t
 def __hash__(self):return hash(self.t)
 def __eq__(self,x):return isinstance(x,E) and self.t==x.t
 def __add__(a,b):return E(('+',a,b if isinstance(b,E) else c(b)))
 __radd__=__add__
 def __neg__(a):return E(('-',a))
 def __sub__(a,b):return a+-b if isinstance(b,E) else a+-c(b)
 def __rsub__(a,b):return c(b)+-a
 def __mul__(a,b):return E(('*',a,b if isinstance(b,E) else c(b)))
 def __rmul__(a,b):return (b if isinstance(b,E) else c(b))*a
 def __pow__(a,n):
  z=c(1)
  for _ in range(n):z=z*a
  return z
@lru_cache(None)
def simp(e):
 op,*a=e.t
 if op in ('c','v'):return e
 if op=='-':
  z=simp(a[0]);return c(-z.t[1]) if z.t[0]=='c' else z.t[1] if z.t[0]=='-' else -z
 x,y=map(simp,a)
 if x.t[0]==y.t[0]=='c':return c(x.t[1]+y.t[1] if op=='+' else x.t[1]*y.t[1])
 if op=='+':
  if x==c(0):return y
  if y==c(0):return x
 else:
  if x==c(0) or y==c(0):return c(0)
  if x==c(1):return y
  if y==c(1):return x
 return E((op,x,y))
D=[v(9),v(10),v(11),-(v(9)*v(3)),-(v(10)*v(4)),-(v(11)*v(5))]+[c(0)]*6
@lru_cache(None)
def diff(e):
 op,*a=e.t
 if op=='c':z=c(0)
 elif op=='v':z=D[a[0]]
 elif op=='+':z=diff(a[0])+diff(a[1])
 elif op=='-':z=-diff(a[0])
 else:z=diff(a[0])*a[1]+a[0]*diff(a[1])
 return simp(z)
def evaluate(e,box):
 @lru_cache(None)
 def rec(e):
  op,*a=e.t
  if op=='c':return (a[0],a[0])
  if op=='v':return box[a[0]]
  if op=='-':
   l,u=rec(a[0]);return(-u,-l)
  l,u=rec(a[0]);L,U=rec(a[1])
  if op=='+':return(l+L,u+U)
  x=[l*L,l*U,u*L,u*U];return(min(x),max(x))
 return rec(e)
def size(e):
 op,*a=e.t
 return 1 if op in ('c','v') else 1+sum(size(x) for x in a)
def expr():
 root=Path(__file__).resolve().parents[2]
 cell=json.loads((root/'data/cover.json').read_text())['cells']['S1']
 m,f=map(F,cell['vertices'][0]);theta=list(map(F,cell['theta']));lam=F(cell['lam'])
 x=[v(i+3) for i in range(3)];l=[-v(i) for i in range(3)]
 h=[x[i]*l[i]-x[i]+1 for i in range(3)]
 ve=[x[i]*l[i]-2*x[i]+2 for i in range(3)]
 g=[x[i]+v(7)*h[i] for i in range(3)]
 avg=lambda a:(a[0]+a[1]+a[2])*c(F(1,3))
 feats=[avg(x)-m,x[0]*x[1]*x[2]-v(6),avg(h)-f]
 for j in range(5):
  terms=[]
  for i in range(3):
   test=[c(1),x[i],x[i]**2,x[i]**3,x[i]*l[i]][j]
   terms.append(test*(l[i]+v(8)*x[(i+1)%3]*x[(i+2)%3]))
  feats.append(avg(terms))
 for j in range(4):
  terms=[]
  for i in range(3):
   test=[x[i],x[i]**3,x[i]**4,x[i]*l[i]][j]
   terms.append(test*(ve[(i+1)%3]+ve[(i+2)%3]-2*(c(1)+c(f)-c(m))))
  feats.append(avg(terms))
 H=avg([a**2 for a in g])-2*avg([g[i]*g[(i+1)%3] for i in range(3)])+(c(m)+v(7)*c(f))**2
 s=c(0)
 for t,a in reversed(list(zip(theta,feats))):s=c(t)*a+s
 return -s-c(lam)*H
T=(F(9217366866,10**12),F(9217366881,10**12));O=(F(92312137,10**8),F(92312139,10**8))
MU=(F(173856571583,5000000000),F(347713218831,10000000000))
def exp_interval(q,bits=60):
 with localcontext() as ctx:
  ctx.prec=100;y=(-Decimal(q.numerator)/Decimal(q.denominator)).exp()*Decimal(2**bits)
  k=int(y)
 return F(k,2**bits),F(k+1,2**bits)
def boxes(lo,hi):
 mid=[(a+b)/2 for a,b in zip(lo,hi)];rad=[(b-a)/2 for a,b in zip(lo,hi)]
 start=[(a,a) for a in mid]+[exp_interval(a) for a in mid]+[T,O,MU]+[(-r,r) for r in rad]
 whole=list(zip(lo,hi))+[(exp_interval(b)[0],exp_interval(a)[1]) for a,b in zip(lo,hi)]+[T,O,MU]+[(-r,r) for r in rad]
 return start,whole
if __name__=='__main__':
 import time
 t=time.monotonic();e=expr();d=diff(e);dd=diff(d)
 print('expression sizes',size(e),size(d),size(dd),'seconds',time.monotonic()-t)
 lo=list(map(F,['47201/4096','47201/4096','20229/4096']));hi=list(map(F,['6743/512','6743/512','6743/1024']))
 st,wh=boxes(lo,hi);t=time.monotonic();vals=[evaluate(e,st)[0],evaluate(d,st)[0],evaluate(dd,wh)[0]]
 print('Taylor terms',list(map(float,vals)),'lower',float(vals[0]+vals[1]+vals[2]/2),'seconds',time.monotonic()-t)

def partial(e,axis):
 ds=[c(int(i==axis)) for i in range(3)]+[-v(i+3) if i==axis else c(0) for i in range(3)]+[c(0)]*6
 @lru_cache(None)
 def go(e):
  op,*a=e.t
  if op=='c':z=c(0)
  elif op=='v':z=ds[a[0]]
  elif op=='+':z=go(a[0])+go(a[1])
  elif op=='-':z=-go(a[0])
  else:z=go(a[0])*a[1]+a[0]*go(a[1])
  return simp(z)
 return go(e)
if __name__=='__main__':
 g=[partial(e,i) for i in range(3)];h=[[partial(g[i],j) for j in range(3)] for i in range(3)]
 rad=[(b-a)/2 for a,b in zip(lo,hi)]
 G=[evaluate(x,st) for x in g];H=[[evaluate(x,wh) for x in row] for row in h]
 grad=-sum(max(abs(l),abs(u))*r for (l,u),r in zip(G,rad))
 hes=-sum(max(abs(l),abs(u))*rad[i]*rad[j] for i,row in enumerate(H) for j,(l,u) in enumerate(row))
 print('partial sizes',[size(x) for x in g],[[size(x) for x in row]for row in h])
 print('partial Taylor lower',float(vals[0]+grad+hes/2),'terms',float(grad),float(hes))

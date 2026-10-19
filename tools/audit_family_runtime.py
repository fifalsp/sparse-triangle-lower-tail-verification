"""Independent symbolic audit of actual family runtime function bodies.
No repository source is changed; replace Arb arithmetic only inside this process.
"""
from pathlib import Path
import hashlib,json,sys
import sympy as s
if not __debug__: raise RuntimeError('Verification requires assertions; do not use -O.')
repo=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(repo/'verification/family'))
import core
core.arb=s.sympify
s.Expr.exp=lambda self:s.exp(self)
a=s.symbols('a0:4');b=s.symbols('b0:4',nonzero=True)
A=core.Jet.coeffs(a);B=core.Jet.coeffs(b)
product=(A*B).c
assert all(s.expand(product[n]-sum(a[k]*b[n-k] for k in range(n+1)))==0 for n in range(4))
quotient=(A/B).c
assert all(s.factor(sum(quotient[k]*b[n-k] for k in range(n+1))-a[n])==0 for n in range(4))
exponential=A.exp().c
expected=[s.exp(a[0]),s.exp(a[0])*a[1],s.exp(a[0])*(a[2]+a[1]**2/2),s.exp(a[0])*(a[3]+a[1]*a[2]+a[1]**3/6)]
assert all(s.simplify(x-y)==0 for x,y in zip(exponential,expected))
q=s.symbols('q0:3',real=True);c0,c1,c2,c3,c4,mu3,AA=s.symbols('c0 c1 c2 c3 c4 mu3 AA',real=True)
x=[s.exp(-v) for v in q];total=sum(q);E=s.exp(-total)
phi=sum(c0+c1*xx-c2*xx*qq-c3*qq+c4*xx*qq*qq for xx,qq in zip(x,q))
phi+=mu3*sum(x[i]*x[j] for i in range(3) for j in range(i+1,3))+E*(1-AA*total)
f,df,e=core.weights(q)
alpha=[3*c0,c1,-c2,-c3,c4,mu3,-AA]
assert s.simplify(phi-sum(u*v for u,v in zip(alpha,f))-e)==0
assert all(s.simplify(s.diff(f[k],q[i])-df[i][k])==0 for i in range(3) for k in range(7))
c=dict(c1=c1,c2=c2,c3=c3,c4=c4,mu3=mu3,A=AA)
H=core.hessian(c,q);Hs=core.hessian(c,q,scaled=True)
assert all(s.simplify(s.diff(phi,q[i],q[j])-H[i][j])==0 for i in range(3) for j in range(3))
assert all(s.simplify(Hs[i][j]-H[i][j]*s.exp((q[i]+q[j])/2))==0 for i in range(3) for j in range(3))
out={'status':'complete','method':'Symbolic arithmetic adapter applied to actual runtime Jet, weights and Hessian functions; no copied numerical implementation.', 'checks':['normalized Taylor product recurrence','normalized Taylor quotient recurrence','normalized Taylor exponential recurrence','coefficient/weight phi decomposition','all21 weight qderivatives','all9 unscaled Hessian entries','all9 scaled Hessian entries'], 'core_sha256':hashlib.sha256((repo/'verification/family/core.py').read_bytes()).hexdigest()}
print(json.dumps(out,indent=2))

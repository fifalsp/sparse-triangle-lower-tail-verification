"""Exact symbolic verification of the coefficient and tangency identities.

Adapted from symbolic_apex_family.py; prints results and never writes inputs.
"""
import sys
if not __debug__: raise RuntimeError("Verification requires assertions; do not use Python -O or PYTHONOPTIMIZE.")
import sympy as s
z,L=s.symbols('z L',positive=True)
M=2*L/(1-z)**2
la=-L*(1+z*z)/(1-z)**2
lb=-2*L*z/(1-z)**2
m=(1+z)/2
t=(z**3+3*z)/4
mat=s.Matrix([
 [3*(z-m),3*(z*la+M*t),3*(la+M*z*z),3*z*la*(la+M*z*z)],
 [1,1+la,1/z+2*M*z,la*la+2*la+M*z*z*(1+3*la)],
 [1,1+la,1/z+2*M,la*la+2*la+M*(1+la+2*lb)],
 [1,1+lb,1+M*(z+1),lb*lb+2*lb+M*z*(1+la+2*lb)],
])
rhs=s.Matrix([t-z**3,-z*z,-1,-z])
ds=[s.factor(x) for x in mat.inv()*rhs]
D=6*L**2*z**2+3*L*z**3-L*z**2-L*z-L-z**3+3*z**2-3*z+1
explicit=[
 z*(z-1)*(z+1)*(L+z-1)*(2*L+z-1)/(2*D),
 z*(z-1)**2*(2*L*z+z**2-1)/(2*D),
 -z*(z-1)**3*(3*L*z+L+2*z**2-2)/(2*(z+1)*D),
 (z-1)**4*(2*L*z+z**2-1)/(2*L*(z+1)*D),
]
assert all(s.factor(x-y)==0 for x,y in zip(ds,explicit))
assert all(s.factor(x)==0 for x in mat*s.Matrix(explicit)-rhs)
assert s.factor(mat.det())!=0
d1,d2,d3,d4=explicit
d0=-d1*m+d2*M*t-t/3
def S(u,ell):return d0+d1*u+d2*u*ell+d3*ell+d4*u*ell**2
def Sd(u,ell):return d1+d2*(1+ell)+d3/u+d4*(ell**2+2*ell)
tangencies=[
 3*S(z,la)+3*M*d3*z*z+z**3*(1+3*M*d4*la),
 Sd(z,la)+2*M*d3*z+z*z*(1+M*d4+3*M*d4*la),
 S(z,la)+2*S(1,lb)+M*d3*(2*z+1)+z*(1+M*d4*(la+2*lb)),
 Sd(z,la)+2*M*d3+1+M*d4*(1+la+2*lb),
 Sd(1,lb)+M*d3*(z+1)+z*(1+M*d4*(1+la+2*lb)),
]
assert all(s.factor(x)==0 for x in tangencies)
print('ALL FIVE EXACT VALUE/GRADIENT TANGENCY IDENTITIES VERIFIED',flush=True)
for i,d in enumerate(ds,1): print(f'd{i}={d}',flush=True)
A1=s.factor(ds[0]+ds[1]*lb+ds[3]*lb**2)
A2=s.factor(ds[1]+2*ds[3]*lb)
A3=ds[2];A4=ds[3]
print('NORMALIZED',flush=True)
for n,d in zip(('A1','A2','A3','A4'),(A1,A2,A3,A4)):print(n,'=',d,flush=True)
print('MEAN_SIGN/b^2=',s.factor(ds[0]+ds[1]+ds[2]*m*m/t),flush=True)

# Exact derivative identities used by the numerical branch-and-bound code.
qs=s.symbols('q0:3'); xs=s.symbols('x0:3')
c0,c1,c2,c3,c4,mu=s.symbols('c0 c1 c2 c3 c4 mu')
phi=sum(c0+c1*x-c2*x*q-c3*q+c4*x*q*q for x,q in zip(xs,qs))
phi+=mu*c3*sum(xs[i]*xs[j] for i in range(3) for j in range(i+1,3))
phi+=s.prod(xs)*(1-mu*c4*sum(qs))
def qdiff(f,i):
    return s.diff(f,qs[i])-xs[i]*s.diff(f,xs[i])
gradient=[xs[i]*(-c1+c2*(qs[i]-1)+c4*(2*qs[i]-qs[i]*qs[i]))-c3-
          mu*c3*xs[i]*(sum(xs)-xs[i])+s.prod(xs)*(mu*c4*sum(qs)-1-mu*c4)
          for i in range(3)]
assert all(s.expand(qdiff(phi,i)-gradient[i])==0 for i in range(3))
tri=s.prod(xs)*(1+2*mu*c4-mu*c4*sum(qs))
hess=s.Matrix(3,3,lambda i,j:
    xs[i]*(c1+c2*(2-qs[i])+c4*(qs[i]*qs[i]-4*qs[i]+2))+
    mu*c3*xs[i]*(sum(xs)-xs[i])+tri if i==j else mu*c3*xs[i]*xs[j]+tri)
assert all(s.expand(qdiff(gradient[i],j)-hess[i,j])==0 for i in range(3) for j in range(3))
B=s.Matrix([[1,0,0],[0,1,1],[0,-1,1]])
assert B.det()!=0
x,y,z=xs
A=[u*(c1+c2*(2-q)+c4*(q*q-4*q+2)) for u,q in zip(xs,qs)]
k11=A[0]+mu*c3*x*(y+z)+tri
k12=mu*c3*x*(y-z)
k13=mu*c3*x*(y+z)+2*tri
k22=A[1]+A[2]+mu*c3*x*(y+z)
k23=A[1]-A[2]+mu*c3*x*(y-z)
k33=A[1]+A[2]+mu*c3*(x*(y+z)+4*y*z)+4*tri
congruent=s.Matrix([[k11,k12,k13],[k12,k22,k23],[k13,k23,k33]])
assert all(s.expand(e)==0 for e in B.T*hess*B-congruent)
print('ALL GRADIENT, HESSIAN, AND FIXED CONGRUENCE IDENTITIES VERIFIED',flush=True)

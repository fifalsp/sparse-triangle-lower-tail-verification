import sympy as s
if not __debug__:
    raise RuntimeError("Verification requires assertions; do not run with -O or PYTHONOPTIMIZE.")
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
assert s.factor(mat.det()+3*L*(z+1)*D/(z*(z-1)**2))==0
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

# Remaining rational identities used in Lemmas certcoef and certtail.
P=2*L**2*z*(z+1)*(z*z+3)+L*(5*z**5-5*z**4+14*z**3-2*z*z-11*z-1)+2*z**6-4*z**5+6*z**4-10*z*z+4*z+2
assert s.factor(d1+d2+d3*m*m/t-(z-1)*P/(2*(z*z+3)*D))==0
qa=-la; A=M*d4
N=2*L**2*z**3+3*L**2*z*z-L**2*z+L*z**4+L*z*z-2*L*z-z**4+2*z**3-2*z+1
assert s.factor(A*(qa+1)-1+2*N/((z+1)*D))==0
T=2*L**2*z**5+2*L**2*z**4+6*L**2*z**3-2*L**2*z*z+L*z**6+7*L*z**5-19*L*z**4+34*L*z**3-33*L*z*z+7*L*z+3*L+3*z**6-13*z**5+24*z**4-14*z**3-17*z*z+27*z-10
assert s.factor(4*(-d3)-z*(d1+d4*qa*(qa+2))+z*T/(2*(z+1)*D))==0
print('MEAN SIGN AND TAIL RATIONAL IDENTITIES VERIFIED', flush=True)

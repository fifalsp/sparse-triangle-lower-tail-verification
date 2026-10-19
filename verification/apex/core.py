"""Arb formulas for the sparse apex certificate.

Adapted from the recorded sparse investigation's verify_apex_family.py.
See provenance.json. These functions alone do not assert a positivity result.
"""
if not __debug__:
    raise RuntimeError('Verification requires assertions; do not use Python -O or PYTHONOPTIMIZE.')

from flint import arb, ctx

def ball(lo,hi):
    return (arb(lo)+arb(hi))/2+arb(0,(arb(hi)-arb(lo))/2)


def coefficients(L):
    z=(-L).exp();b=(-2*L*z/(1-z)**2).exp();a=z*b
    mu=2*L/((1-z)**2*b*b);m=(a+b)/2;t=(a*a*a+3*a*b*b)/4
    D=6*L*L*z*z+3*L*z**3-L*z*z-L*z-L-z**3+3*z*z-3*z+1
    c1=b*b*z*(z-1)*(z+1)*(L+z-1)*(2*L+z-1)/(2*D)
    c2=b*b*z*(z-1)**2*(2*L*z+z*z-1)/(2*D)
    c3=-b**3*z*(z-1)**3*(3*L*z+L+2*z*z-2)/(2*(z+1)*D)
    c4=b*b*(z-1)**4*(2*L*z+z*z-1)/(2*L*(z+1)*D)
    c0=-c1*m+c2*mu*t-t/3
    qa=L+2*L*z/(1-z)**2;qb=2*L*z/(1-z)**2
    return dict(z=z,a=a,b=b,mu=mu,m=m,t=t,D=D,c0=c0,c1=c1,c2=c2,c3=c3,c4=c4,qa=qa,qb=qb)


def psi(c,qs):
    c0,c1,c2,c3,c4=[c[k] for k in ('c0','c1','c2','c3','c4')]
    mu=c['mu'];xs=[(-q).exp() for q in qs]
    return sum(c0+c1*x-c2*x*q-c3*q+c4*x*q*q for x,q in zip(xs,qs))+mu*c3*(xs[0]*xs[1]+xs[1]*xs[2]+xs[2]*xs[0])+(-sum(qs)).exp()*(1-mu*c4*sum(qs))


def hessian(c,qs):
    c1,c2,c3,c4=[c[k] for k in ('c1','c2','c3','c4')]
    mu=c['mu'];xs=[(-q).exp() for q in qs];s=sum(qs)
    g=(-s).exp()*(1+2*mu*c4-mu*c4*s)
    H=[[arb(0) for j in range(3)] for i in range(3)]
    for i in range(3):
        for j in range(3):
            if i==j:
                q=qs[i];x=xs[i]
                H[i][j]=x*(c1+c2*(2-q)+c4*(q*q-4*q+2))+mu*c3*x*(sum(xs)-x)+g
            else:H[i][j]=mu*c3*xs[i]*xs[j]+g
    return H


def positive_definite(H):
    if not H[0][0]>0:return False
    # python-flint's general arb.__pow__ may return nan on a ball containing
    # zero, even for exponent 2. Multiplication gives a valid enclosure.
    d1=H[1][1]-H[0][1]*H[0][1]/H[0][0]
    if not d1>0:return False
    off=H[1][2]-H[0][1]*H[0][2]/H[0][0]
    d2=H[2][2]-H[0][2]*H[0][2]/H[0][0]-off*off/d1
    return bool(d2>0)


def hessian_symmetry_basis(c,qs):
    """Congruence by e1,e2-e3,e2+e3, with cancellations done algebraically."""
    c1,c2,c3,c4=[c[k] for k in ('c1','c2','c3','c4')]
    mu=c['mu'];x,y,z=[(-q).exp() for q in qs];s=sum(qs)
    g=(-s).exp()*(1+2*mu*c4-mu*c4*s)
    A=[u*(c1+c2*(2-q)+c4*(q*q-4*q+2)) for u,q in zip((x,y,z),qs)]
    k11=A[0]+mu*c3*x*(y+z)+g
    k12=mu*c3*x*(y-z)
    k13=mu*c3*x*(y+z)+2*g
    k22=A[1]+A[2]+mu*c3*x*(y+z)
    k23=A[1]-A[2]+mu*c3*x*(y-z)
    k33=A[1]+A[2]+mu*c3*(x*(y+z)+4*y*z)+4*g
    return [[k11,k12,k13],[k12,k22,k23],[k13,k23,k33]]



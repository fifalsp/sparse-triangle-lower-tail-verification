"""Arb inclusions for the exact certificate family in Appendix app:family.

The only floating-point calculations here propose splitting directions and
congruence matrices. Every accepted inequality is rechecked in Arb arithmetic.
"""
import functools
import math
import numpy as np
from flint import arb

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not run with -O or PYTHONOPTIMIZE.')


def ball(lo, hi):
    """Contain the closed interval with exact binary64 (or Arb) endpoints."""
    lo, hi = arb(lo), arb(hi)
    return (lo + hi) / 2 + arb(0, (hi - lo) / 2)


def radius(lo, hi, center):
    return ((arb(hi) - arb(lo)) / 2 + abs(arb(center) - (arb(lo) + arb(hi)) / 2)).upper()


class Jet:
    """Four normalized Taylor coefficients, with all operations in Arb."""
    ORDER = 3

    def __init__(self, value, derivative=0):
        self.c = [arb(value), arb(derivative), arb(0), arb(0)]

    @classmethod
    def coeffs(cls, values):
        out = cls(0)
        out.c = list(values)
        return out

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Jet) else Jet(value)

    def __add__(self, other):
        other = self.coerce(other)
        return self.coeffs([a+b for a,b in zip(self.c, other.c)])
    __radd__ = __add__

    def __neg__(self):
        return self.coeffs([-a for a in self.c])

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return self.coeffs([sum(self.c[k]*other.c[n-k] for k in range(n+1)) for n in range(4)])
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        # Enclosures with a vanishing denominator produce a non-finite result
        # and cannot pass a strict acceptance test.
        values = []
        for n in range(4):
            values.append((self.c[n]-sum(other.c[k]*values[n-k] for k in range(1,n+1)))/other.c[0])
        return self.coeffs(values)

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def __pow__(self, n):
        if not isinstance(n, int) or n < 0:
            raise ValueError('Only nonnegative integer jet powers are used.')
        out = Jet(1)
        for _ in range(n):
            out = out * self
        return out

    def exp(self):
        values = [self.c[0].exp()]
        for n in range(1,4):
            values.append(sum(k*self.c[k]*values[n-k] for k in range(1,n+1))/n)
        return self.coeffs(values)


def coefficients(L):
    """Equations eq:branch, eq:certcoef and eq:certpsi, literally."""
    z=(-L).exp(); b=(-2*L*z/(1-z)**2).exp(); a=z*b
    mu=2*L/((1-z)**2*b*b); m=(a+b)/2; t=(a*a*a+3*a*b*b)/4
    D=6*L*L*z*z+3*L*z**3-L*z*z-L*z-L-z**3+3*z*z-3*z+1
    c1=b*b*z*(z-1)*(z+1)*(L+z-1)*(2*L+z-1)/(2*D)
    c2=b*b*z*(z-1)**2*(2*L*z+z*z-1)/(2*D)
    c3=-b**3*z*(z-1)**3*(3*L*z+L+2*z*z-2)/(2*(z+1)*D)
    c4=b*b*(z-1)**4*(2*L*z+z*z-1)/(2*L*(z+1)*D)
    c0=-c1*m+c2*mu*t-t/3
    qa=L+2*L*z/(1-z)**2; qb=2*L*z/(1-z)**2
    return dict(z=z,a=a,b=b,mu=mu,m=m,t=t,D=D,c0=c0,c1=c1,c2=c2,c3=c3,c4=c4,qa=qa,qb=qb,A=mu*c4,mu3=mu*c3)


def alpha(c):
    return [3*c['c0'], c['c1'], -c['c2'], -c['c3'], c['c4'], c['mu3'], -c['A']]


@functools.lru_cache(maxsize=16000)
def enclosure(lo, hi):
    midpoint=(lo+hi)/2
    width=radius(lo,hi,midpoint)
    whole=coefficients(Jet(ball(lo,hi),1))
    center=coefficients(Jet(arb(midpoint),1))
    enclosed={}
    for key, cj in center.items():
        error=abs(cj.c[1])*width+abs(cj.c[2])*width*width+abs(whole[key].c[3])*width*width*width
        enclosed[key]=cj.c[0]+arb(0,error)
    return enclosed, alpha(center), alpha(whole), width


def weights(qs):
    xs=[(-q).exp() for q in qs]; s=sum(qs); E=(-s).exp()
    f=[arb(1),sum(xs),sum(q*x for q,x in zip(qs,xs)),s,
       sum(q*q*x for q,x in zip(qs,xs)),xs[0]*xs[1]+xs[0]*xs[2]+xs[1]*xs[2],s*E]
    df=[]
    for i,(q,x) in enumerate(zip(qs,xs)):
        df.append([arb(0),-x,(1-q)*x,arb(1),(2*q-q*q)*x,
                   -x*sum(xs[j] for j in range(3) if j!=i),(1-s)*E])
    return f,df,E


def hessian(c,qs,scaled=False):
    c1,c2,c4=c['c1'],c['c2'],c['c4']; mu3,A=c['mu3'],c['A']
    xs=[(-q).exp() for q in qs]; s=sum(qs); factor=1+2*A-A*s
    H=[[arb(0) for _ in range(3)] for _ in range(3)]
    for i in range(3):
        j,k=[j for j in range(3) if j!=i]
        q=qs[i]
        diagonal=c1+c2*(2-q)+c4*(q*q-4*q+2)+mu3*(xs[j]+xs[k])+xs[j]*xs[k]*factor
        H[i][i]=diagonal if scaled else xs[i]*diagonal
        for j in range(i):
            k=3-i-j
            H[i][j]=H[j][i]=((-(qs[i]+qs[j])/2).exp() if scaled else xs[i]*xs[j])*(mu3+xs[k]*factor)
    return H


def positive_definite(H):
    """Exact-binary64 congruence proposal, Arb Gershgorin verification."""
    try:
        numerical=np.array([[float(v.mid()) for v in row] for row in H])
        if not np.all(np.isfinite(numerical)):
            return False
        _, vectors=np.linalg.eigh(numerical)
    except (ValueError,np.linalg.LinAlgError):
        return False
    T=[[arb(float(vectors[i,j])) for j in range(3)] for i in range(3)]
    HT=[[sum(H[i][k]*T[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    M=[[sum(T[k][i]*HT[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    return all(M[i][i]-sum(abs(M[i][j]) for j in range(3) if j!=i)>0 for i in range(3))


def tighten(box, pattern=None):
    lo,hi=[list(xs) for xs in box]
    if pattern != 2:
        lo[2]=max(lo[2],lo[3]);lo[1]=max(lo[1],lo[2]);hi[2]=min(hi[2],hi[1]);hi[3]=min(hi[3],hi[2])
    else:
        lo[2]=max(lo[2],lo[3]);hi[3]=min(hi[3],hi[2])
    if any(a>b for a,b in zip(lo,hi)):
        return None
    return tuple(lo),tuple(hi)


def split(box,index):
    lo,hi=box;mid=(lo[index]+hi[index])/2
    if not lo[index]<mid<hi[index]:
        raise RuntimeError('Unresolved box reached binary64 subdivision limit.')
    lhi=list(hi);lhi[index]=mid;rlo=list(lo);rlo[index]=mid
    return [(tuple(rlo),hi),(lo,tuple(lhi))]


def inside(qs,pattern,c,delta):
    p=[c['qa']]*3 if pattern==1 else [c['qa'],c['qb'],c['qb']]
    return all(q-pi>-delta and q-pi<delta for q,pi in zip(qs,p))


def compact_test(box, delta):
    lo,hi=box;c,at,aw,w=enclosure(lo[0],hi[0])
    if not(c['D']<0 and c['c1']>0 and c['c2']>0 and c['c3']<0 and c['c4']>0):
        return False,0,'coefficient-split'
    qs=[ball(lo[i],hi[i]) for i in range(1,4)]
    for pattern in (1,2):
        if inside(qs,pattern,c,delta):
            return True,None,'local'+str(pattern)
    mids=[(lo[i]+hi[i])/2 for i in range(1,4)]
    radii=[radius(lo[i+1],hi[i+1],mids[i]) for i in range(3)]
    f,df,E=weights([arb(q) for q in mids])
    phi=[sum(at[k].c[n]*f[k] for k in range(7))+(E if n==0 else 0) for n in range(3)]
    third=sum(aw[k].c[3]*f[k] for k in range(7))
    H=hessian(c,qs)
    Lerror=w*abs(phi[1])+w*w*w*abs(third)
    lower=phi[0]-Lerror+min(arb(0),phi[2].lower())*w*w
    contributions=[]
    for i,r in enumerate(radii):
        g0=sum(at[k].c[0]*df[i][k] for k in range(7))-E
        g1=sum(at[k].c[1]*df[i][k] for k in range(7))
        g2=sum(aw[k].c[2]*df[i][k] for k in range(7))
        error=w*abs(g1)+w*w*abs(g2)
        plus=(abs(g0)+error).upper(); minus=(abs(g0)-error).lower(); h=H[i][i].lower()
        candidates=[-plus*r+min(arb(0),h)*r*r/2]
        if h>0:
            candidates.append(-plus*plus/(2*h))
            if minus>=h*r:
                candidates.append(-plus*r+h*r*r/2)
        beta=max(candidates,key=lambda value:float(value.lower()))
        lower+=beta
        contributions.append(plus*r+abs(h)*r*r/2)
    for i in range(3):
        for j in range(i):
            term=radii[i]*radii[j]*abs(H[i][j]);lower-=term
            contributions[i]+=term;contributions[j]+=term
    if lower>0:
        return True,None,'taylor'
    impacts=[Lerror]+contributions
    index=max(range(4),key=lambda i:float(impacts[i].abs_upper()))
    if lo[index]==hi[index]:
        index=max(range(4),key=lambda i:hi[i]-lo[i])
    return False,index,'split'

"""Arb reconstruction of the inherited sparse endpoint certificate data."""
from pathlib import Path
from fractions import Fraction as Q
import json,re,hashlib,os,sys
if not __debug__: raise RuntimeError("Verification requires assertions; do not run Python with -O or PYTHONOPTIMIZE.")
from flint import arb,arb_mat,ctx
import generated_templates as gt
ctx.prec=256
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
SOURCE=REPO/'data'/'cover.json'
OUTPUT=Path(os.environ.get('SPARSE_VERIFICATION_RESULTS', str(REPO/'results')))/'cover'
OUTPUT.mkdir(parents=True, exist_ok=True)

def A(x):
    if isinstance(x,Q):return arb(x.numerator)/x.denominator
    return arb(x)
def ball(lo,hi):
    lo,hi=A(lo),A(hi)
    return (lo+hi)/2+arb(0,(hi-lo)/2)
def dyadic(s):return Q(float(s))
def h(x):return x*x.log()-x+1

def branch(z):
    b=(2*z*z.log()/((1-z)*(1-z))).exp();a=z*b
    t=(a*a*a+3*a*b*b)/4;r=t.root(3)
    return dict(z=z,a=a,b=b,t=t,r=r,m=(a+b)/2,F=(h(a)+h(b))/2,
                mu=-b.log()/(a*b),qa=-a.log(),qb=-b.log(),omega=(b-a)/(h(a)-h(b)))
def crossing(z):
    c=branch(z);return h(c['r'])-c['F']

def setup_constants():
    lo=Q('0.0200554310548823255291088');hi=Q('0.0200554310548823255291090')
    assert crossing(A(lo))>0 and crossing(A(hi))<0
    assert crossing(A(Q('0.02005543105488')))>0
    assert crossing(A(Q('0.02005543105489')))<0
    for _ in range(110):
        mid=(lo+hi)/2;v=crossing(A(mid))
        if v>0:lo=mid
        elif v<0:hi=mid
        else:raise AssertionError('Ambiguous crossing sign')
    c=branch(ball(lo,hi));c['z_bracket']=[str(lo),str(hi)]
    assert c['a']>0 and c['b']<1 and c['a']<c['b']
    # Exact decimal-rational enclosures printed in Lemma bal:digits.
    targets={'a':('0.01703401908','0.01703401909'),
             'b':('0.8493469443','0.8493469444'),
             'mu':('11.28627816','11.28627817'),
             'r':('0.2096696762','0.2096696763')}
    for key,(left,right) in targets.items():
        assert c[key]>A(Q(left)) and c[key]<A(Q(right)), (key,c[key])
    return c


def input_data():
    data=json.loads(SOURCE.read_text())
    cells=data['cells']
    expected=['F1','F2','F3','F4','F5','F6','S1','S2','S3','R1','B1','B2']
    assert list(cells)==expected
    for name,cell in cells.items():
        assert len(cell['theta'])==12
        assert len(cell['vertices'])==len(cell['targets'])
        assert [i for i,x in enumerate(cell['theta']) if x is None]==([0,2,3,4] if cell['apex'] else [])
        assert Q(cell['lam'])>=0 and Q(cell['Q'])>0
        for value in cell['theta']:
            if value is not None: Q(value)
    return cells


def args(q,theta,lam,c,m,F):
    mu=(1-F-m)/c['t'];kb=1+F-m
    return [*q,*[(-qi).exp() for qi in q],*theta,lam,mu,kb,c['t'],m,F,c['omega']]

def evaluate(q,theta,lam,c,m,F,mode='all'):
    fn={'all':gt.all_derivatives,'value':gt.value,'first':gt.value_gradient,'second':gt.value_hessian}[mode]
    return fn(*args(q,theta,lam,c,m,F))


def positive_definite(H):
    if not H[0][0]>0:return False
    d=H[1][1]-H[0][1]*H[0][1]/H[0][0]
    if not d>0:return False
    off=H[1][2]-H[0][1]*H[0][2]/H[0][0]
    d2=H[2][2]-H[0][2]*H[0][2]/H[0][0]-off*off/d
    return bool(d2>0)


def hessian(values):
    return [[values[4],values[5],values[6]],[values[5],values[7],values[8]],[values[6],values[8],values[9]]]


def tangent_coefficients(cell,c):
    theta=[A(0) if x is None else A(Q(x)) for x in cell['theta']];lam=A(Q(cell['lam']))
    if not cell['apex']:return theta,None
    unknown=[0,2,3,4];pa=[c['qa']]*3;pb=[c['qa'],c['qb'],c['qb']]
    def equations(tvec,lambda_):
        va=evaluate(pa,tvec,lambda_,c,c['m'],c['F'],'first')
        vb=evaluate(pb,tvec,lambda_,c,c['m'],c['F'],'first')
        return [va[0],va[1],vb[1],vb[2]]
    rhs=[-v for v in equations(theta,lam)];cols=[]
    for j in unknown:
        unit=[A(0)]*12;unit[j]=A(1);cols.append(equations(unit,A(0)))
    mat=arb_mat([[cols[j][i] for j in range(4)] for i in range(4)])
    assert not mat.det().contains(0)
    solution=mat.solve(arb_mat([[x] for x in rhs]))
    for k,j in enumerate(unknown):theta[j]=solution[k,0]
    assert all(v.contains(0) for v in equations(theta,lam))
    # The unused abb value is zero algebraically because the balanced
    # triangle law annihilates every E and has H=0, hence Psi(aaa)+3Psi(abb)=0.
    assert evaluate(pb,theta,lam,c,c['m'],c['F'],'value')[0].contains(0)
    return theta,dict(determinant=str(mat.det()),solution={str(j):str(theta[j]) for j in unknown})


def support_check(cell,c):
    ms=[A(Q(v[0])) for v in cell['vertices']];fs=[A(Q(v[1])) for v in cell['vertices']]
    if cell['apex']:ms.append(c['m']);fs.append(c['F'])
    # Source minima are bounded below by lower endpoints of all balls.
    ml=min(v.lower() for v in ms);fl=min(v.lower() for v in fs)
    bound=((1-fl)*(1-fl)-ml*ml)/(2*c['t'])
    assert ml>0 and fl<1 and bound<=A(Q(cell['Q']))
    return dict(mean_lower=str(ml),cost_lower=str(fl),log_support_upper=str(bound))

if __name__=='__main__':
    cells=input_data();c=setup_constants();checks={}
    for name,cell in cells.items():
        th,tan=tangent_coefficients(cell,c);checks[name]=dict(support=support_check(cell,c),tangency=tan)
    out=dict(inputs_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),precision_bits=ctx.prec,
             z_bracket=c['z_bracket'],constants={k:str(v) for k,v in c.items() if k!='z_bracket'},cells=cells,checks=checks)
    (OUTPUT/'endpoint_inputs_verified.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(constants_verified=True,support_checks=12,tangent_solves=6),indent=2))

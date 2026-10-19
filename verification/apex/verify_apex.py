"""Fail-closed Arb verification of the historical single-apex inequality.

This is an additional crossing check, not the current draft's uniform
family verification over L in [3.9, 9.5].

Run ``python verification/apex/verify_apex.py --quick`` for constants, the
validated solve, tail, and local tests. Omit --quick for the full ordered
cube [0,53]^3. An incomplete run exits nonzero; --quick is never reported
as a full proof. Reports go to results/apex by default.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import sys
if not __debug__: raise RuntimeError("Verification requires assertions; do not use Python -O or PYTHONOPTIMIZE.")
import time
from flint import arb, arb_mat, ctx
import core

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]


def A(x):
    return arb(x.numerator) / x.denominator if isinstance(x, Q) else arb(x)


def h(x):
    return x * x.log() - x + 1


def crossing(z):
    b = (2 * z * z.log() / ((1-z)*(1-z))).exp()
    a = z*b
    t = (a*a*a+3*a*b*b)/4
    return h(t.root(3))-(h(a)+h(b))/2


def grad(c, qs):
    c1,c2,c3,c4 = [c[k] for k in ('c1','c2','c3','c4')]
    mu=c['mu']; xs=[(-q).exp() for q in qs]; total=sum(qs)
    tr=(-total).exp()*(mu*c4*total-1-mu*c4)
    return [x*(-c1+c2*(q-1)+c4*(2*q-q*q))-c3-
            mu*c3*x*(sum(xs)-x)+tr for x,q in zip(xs,qs)]


def model():
    lo=Q('0.0200554310548823255291088')
    hi=Q('0.0200554310548823255291090')
    assert crossing(A(lo))>0 and crossing(A(hi))<0
    for _ in range(110):
        mid=(lo+hi)/2; val=crossing(A(mid))
        if val>0: lo=mid
        elif val<0: hi=mid
        else: raise AssertionError('Unresolved crossing sign')
    z=core.ball(A(lo),A(hi)); c=core.coefficients(-z.log())
    a,b,mu,m,t=[c[k] for k in ('a','b','mu','m','t')]
    la,lb=a.log(),b.log()
    mat=arb_mat([
        [3*(a-m),3*(a*la+mu*t),3*(la+mu*a*a),3*a*la*(la+mu*a*a)],
        [1,1+la,1/a+2*mu*a,la*la+2*la+mu*a*a*(1+3*la)],
        [1,1+la,1/a+2*mu*b,la*la+2*la+mu*b*b*(1+la+2*lb)],
        [1,1+lb,1/b+mu*(a+b),lb*lb+2*lb+mu*a*b*(1+la+2*lb)]])
    rhs=arb_mat([[t-a*a*a],[-a*a],[-b*b],[-a*b]])
    determinant=mat.det(); assert not determinant.contains(0)
    sol=mat.solve(rhs)
    for i in range(4):
        assert (sol[i,0]-c[f'c{i+1}']).contains(0)
        c[f'c{i+1}']=sol[i,0]
    c['c0']=-c['c1']*m+c['c2']*mu*t-t/3
    assert c['c1']>0 and c['c2']>0 and c['c3']<0 and c['c4']>0
    gamma=3*c['c0']-3*c['c2']/arb(1).exp()+3*mu*c['c3']-mu*c['c4']*(-1-1/(mu*c['c4'])).exp()
    assert -c['c3'] > A(Q('0.004038'))
    assert gamma > A(Q('-0.2122'))
    tail=-53*c['c3']+gamma
    assert tail>0
    locals_=[]
    for pattern,radius in [(1,Q(float('0.03'))),(2,Q(float('0.002')))]:
        center=[c['qa']]*3 if pattern==1 else [c['qa'],c['qb'],c['qb']]
        wide=[x+arb(0,A(radius)) for x in center]
        # Congruence preserves positive definiteness; this basis avoids
        # avoidable dependency loss in the repeated-coordinate pattern.
        H=core.hessian_symmetry_basis(c,wide)
        assert core.positive_definite(H), ('local Hessian test failed',pattern)
        assert core.psi(c,center).contains(0)
        assert all(v.contains(0) for v in grad(c,center))
        locals_.append(dict(pattern=pattern,radius=str(radius),method='interval Hessian positive definite by exact congruence and LDL pivots'))
    return c,dict(z_bracket=[str(lo),str(hi)],determinant=str(determinant),
                  coefficients={f'c{i}':str(c[f'c{i}']) for i in range(5)},
                  gamma0=str(gamma),tail_lower_bound=str(tail),
                  printed_tail_bounds={'abs_c3': '> 0.004038', 'gamma0': '> -0.2122'},
                  local_checks=locals_)


def analyze(lo,hi,c,target):
    qs=[core.ball(A(l),A(u)) for l,u in zip(lo,hi)]
    for pattern,rad in [(1,Q(float('0.03'))),(2,Q(float('0.002')))]:
        centers=[c['qa']]*3 if pattern==1 else [c['qa'],c['qb'],c['qb']]
        if all(abs(x-y)<A(rad) for x,y in zip(qs,centers)):
            return f'local{pattern}'
    if core.psi(c,qs)>target: return 'direct'
    mid=[(l+u)/2 for l,u in zip(lo,hi)]
    ma=list(map(A,mid))
    radii=[max(abs(A(l)-m),abs(A(u)-m)) for l,u,m in zip(lo,hi,ma)]
    value=core.psi(c,ma); gs=grad(c,qs)
    if value-sum(abs(g)*r for g,r in zip(gs,radii))>target: return 'Taylor1'
    cg=grad(c,ma); H=core.hessian(c,qs)
    lower=value-sum(abs(g)*r for g,r in zip(cg,radii))
    for i in range(3):
        if not H[i][i]>=0: lower-=abs(H[i][i])*radii[i]*radii[i]/2
        for j in range(i+1,3): lower-=abs(H[i][j])*radii[i]*radii[j]
    if lower>target: return 'Taylor2'
    return None


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick',action='store_true')
    p.add_argument('--max-nodes',type=int,default=2000000)
    p.add_argument('--precision',type=int,default=256)
    p.add_argument('--output-dir',type=Path,default=REPO/'results'/'apex')
    args=p.parse_args()
    if args.precision<192: p.error('precision must be at least 192 bits')
    if args.max_nodes<1: p.error('max-nodes must be positive')
    assert sys.float_info.radix==2 and sys.float_info.mant_dig==53
    ctx.prec=args.precision; started=time.monotonic(); c,checks=model()
    out=dict(status='quick_checks_passed',scope='constants, coefficient solve, tail and local Hessians only',
             precision_bits=ctx.prec,checks=checks,source_sha256={n:hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in ['core.py','verify_apex.py','symbolic.py']})
    exitcode=0
    if not args.quick:
        todo=[((0.,0.,0.),(53.,53.,53.))]; nodes=0; counts={}; digest=hashlib.sha256(); failure=None
        target=A(Q(float('1e-12')))
        while todo and nodes<args.max_nodes:
            lo,hi=todo.pop(); nodes+=1
            lo=(max(lo),max(lo[1:]),lo[2]); hi=(hi[0],min(hi[:2]),min(hi))
            if any(l>u for l,u in zip(lo,hi)):
                counts['empty']=counts.get('empty',0)+1; continue
            kind=analyze(lo,hi,c,target)
            if kind:
                counts[kind]=counts.get(kind,0)+1
                digest.update(repr((kind,lo,hi)).encode()); continue
            i=max(range(3),key=lambda k:hi[k]-lo[k]); mid=(lo[i]+hi[i])/2
            if not lo[i]<mid<hi[i] or hi[i]-lo[i]<2**-42:
                todo.append((lo,hi)); failure='unresolved box at minimum dyadic width'; break
            uh=list(hi); ll=list(lo); uh[i]=mid; ll[i]=mid
            todo.extend([(tuple(ll),hi),(lo,tuple(uh))])
            counts['split']=counts.get('split',0)+1
            if nodes%10000==0: print(json.dumps(dict(nodes=nodes,pending=len(todo),seconds=time.monotonic()-started)),flush=True)
        out.update(status='complete' if not todo else 'incomplete',scope='ordered cube [0,53]^3, local equality neighborhoods and analytic tail',
                   Q=53,target=str(target),nodes=nodes,pending=len(todo),counts=counts,
                   accepted_partition_sha256=digest.hexdigest(),remaining_boxes=todo,failure=failure)
        exitcode=0 if not todo else 1
    out['seconds']=time.monotonic()-started
    args.output_dir.mkdir(parents=True,exist_ok=True)
    path=args.output_dir/('quick.json' if args.quick else 'apex.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['remaining_boxes','checks','source_sha256']},indent=2),flush=True)
    raise SystemExit(exitcode)

if __name__=='__main__': main()

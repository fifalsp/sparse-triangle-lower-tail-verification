"""Independent FLINT series cross-checks of the hand-written Taylor formulas.

These tests compare two implementations at specified inputs. They supplement,
but do not replace, the interval inclusion arguments in core.py and the draft.
"""
from flint import arb,arb_series,ctx
import core

if not __debug__:
    raise RuntimeError('Verification requires assertions; do not run with -O or PYTHONOPTIMIZE.')


def run():
    old_cap=ctx.cap;ctx.cap=4;count=0
    try:
        for L in [arb(39)/10,arb(5),arb(7),arb(19)/2,core.ball(4,4.0001)]:
            manual=core.coefficients(core.Jet(L,1))
            independent=core.coefficients(arb_series([L,arb(1)]))
            for key in manual:
                for n in range(4):
                    if not manual[key].c[n].overlaps(independent[key][n]):
                        raise RuntimeError(f'Taylor recurrence mismatch: {key}, order {n}.')
                    count+=1
        directions=[[1,0,0],[0,1,0],[0,0,1],[1,1,0],[1,0,1],[0,1,1]]
        for L,point in [(4,[4,2,.1]),(7,[6,3,1]),(9.5,[9.6,.1,-.05])]:
            c=core.coefficients(arb(L));a=core.alpha(c)
            qs=[arb(q) for q in point];H=core.hessian(c,qs)
            _,df,E=core.weights(qs)
            gradient=[sum(a[k]*df[i][k] for k in range(7))-E for i in range(3)]
            for direction in directions:
                qseries=[arb_series([q,arb(d)]) for q,d in zip(qs,direction)]
                f,_,es=core.weights(qseries)
                phi=sum(a[k]*f[k] for k in range(7))+es
                first=sum(direction[i]*gradient[i] for i in range(3))
                second=sum(direction[i]*direction[j]*H[i][j] for i in range(3) for j in range(3))/2
                if not first.overlaps(phi[1]) or not second.overlaps(phi[2]):
                    raise RuntimeError('Gradient/Hessian mismatch against independent FLINT series.')
                count+=2
            S=core.hessian(c,qs,scaled=True)
            for i in range(3):
                for j in range(3):
                    if not (S[i][j]*(-(qs[i]+qs[j])/2).exp()).overlaps(H[i][j]):
                        raise RuntimeError('Scaled Hessian congruence mismatch.')
                    count+=1
    finally:
        ctx.cap=old_cap
    return {'status':'passed','comparisons':count,'method':'independent FLINT arb_series recurrence and directional derivative cross-checks'}


if __name__=='__main__':
    import json
    ctx.prec=128
    print(json.dumps(run()))

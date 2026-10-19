"""Independent Arb reconstruction of sparse main.tex Lemma src:uni:constants.

Only interval sign decisions accept endpoints.  Every number used for a
published enclosure is an exact decimal rational, not a binary float.
"""
from pathlib import Path
from fractions import Fraction as Q
import json, hashlib
import endpoint_common as ec
A, ctx = ec.A, ec.ctx
HERE = Path(__file__).resolve().parent


def constant_stationary(gamma):
    """Enclose the unique root for all gamma in an Arb interval."""
    lo, hi = Q(1, 8), Q(1, 2)
    def fun(s):
        x = A(s)
        return x.log() + 3*gamma*x*x
    assert fun(lo) < 0 and fun(hi) > 0
    # Refine independently from below and above.  An indeterminate sign
    # retains the existing bracket; it is never interpreted as a root.
    for _ in range(240):
        mid = (lo+hi)/2
        v = fun(mid)
        if v < 0:
            lo = mid
        elif v > 0:
            hi = mid
        else:
            break
    return ec.ball(lo, hi), [str(lo), str(hi)]


def data(z):
    c = ec.branch(z)
    gamma = c['mu']/3
    s, bracket = constant_stationary(gamma)
    phi = c['F'] + gamma*c['t']
    C0 = ec.h(s) + gamma*s*s*s
    return dict(delta=phi-C0, gamma=gamma, C=phi, rplus=s,
                t2=s*s*s, rminus=c['r'], t1=c['t']), bracket


def main():
    lo, hi = Q('8.352460192e-5'), Q('8.352460193e-5')
    left, sl = data(A(lo)); right, sr = data(A(hi))
    assert left['delta'] < 0 and right['delta'] > 0
    original = [str(lo), str(hi)]
    # Extra root refinement avoids dependency overestimation without
    # changing or weakening any of the source's six printed enclosures.
    for _ in range(100):
        mid = (lo+hi)/2
        d, _ = data(A(mid))
        if d['delta'] < 0:
            lo = mid
        elif d['delta'] > 0:
            hi = mid
        else:
            raise AssertionError('Ambiguous Delta sign in root refinement')
    vals, sb = data(ec.ball(lo, hi))
    targets = dict(gamma=('6.280969860','6.280969861'),
        C=('0.4999589178','0.4999589179'),
        rplus=('0.2653474271','0.2653474272'),
        t2=('0.01868291522','0.01868291523'),
        rminus=('0.03965310391','0.03965310392'),
        t1=('6.234929748e-5','6.234929749e-5'))
    for key, (a,b) in targets.items():
        assert vals[key] > A(Q(a)) and vals[key] < A(Q(b)), (key, vals[key])
    out = dict(status='complete', precision_bits=ctx.prec,
        original_z_bracket=original,
        delta_signs=[str(left['delta']),str(right['delta'])],
        refined_z_bracket=[str(lo),str(hi)],
        stationary_root_bracket=sb,
        enclosures={k:str(vals[k]) for k in targets}, targets=targets,
        inputs_sha256=hashlib.sha256(ec.SOURCE.read_bytes()).hexdigest(),
        common_sha256=hashlib.sha256(Path(ec.__file__).read_bytes()).hexdigest(),
        program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ec.OUTPUT/'penalized_constants_verified.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__ == '__main__':
    main()

"""Exact planar and Arb one-variable coverage for the sparse endpoint.

This rebuild verifies only the cover geometry and its curved-domain
inclusion. It does not verify the twelve nonlinear scalar certificates.
All printed cell decimals have exact nearest-binary64 interpretation;
Omega+ endpoints have exact decimal interpretation, as in the manuscript.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys
import time

import endpoint_common as common

A, ball = common.A, common.ball
PATH = common.OUTPUT/'planar_coverage.json'


def digest(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True,
        separators=(',', ':')).encode()).hexdigest()


def orient(a, b, p):
    return (b[0]-a[0])*(p[1]-a[1])-(b[1]-a[1])*(p[0]-a[0])


def area2(poly):
    return sum((a[0]*b[1]-a[1]*b[0]
                for a, b in zip(poly, poly[1:]+poly[:1])), Q(0))


def clean(poly):
    out = []
    for p in poly:
        if not out or p != out[-1]:
            out.append(p)
    if len(out) > 1 and out[0] == out[-1]:
        out.pop()
    return out


def clip(poly, a, b, inside=True):
    """Clip a closed convex polygon to one closed rational half plane."""
    out = []
    for x, y in zip(poly, poly[1:]+poly[:1]):
        fx, fy = orient(a, b, x), orient(a, b, y)
        if not inside:
            fx, fy = -fx, -fy
        if fx >= 0:
            out.append(x)
        if (fx < 0 < fy) or (fy < 0 < fx):
            t = fx/(fx-fy)
            out.append((x[0]+t*(y[0]-x[0]), x[1]+t*(y[1]-x[1])))
    return clean(out)


def subtract(poly, cover):
    """Closed polygonal superset of poly minus the convex closed cover."""
    remainder = poly
    outside = []
    for a, b in zip(cover, cover[1:]+cover[:1]):
        if not remainder:
            break
        part = clip(remainder, a, b, inside=False)
        if part:
            outside.append(part)
        remainder = clip(remainder, a, b, inside=True)
    return outside


def rect(x0, x1, y0, y1):
    x0, x1, y0, y1 = map(Q, (x0, x1, y0, y1))
    return [(x0,y0),(x1,y0),(x1,y1),(x0,y1)]


def serialize(poly):
    return [[str(x), str(y)] for x, y in poly]


def planar_checks(c, cells):
    assert sys.float_info.mant_dig == 53 and sys.float_info.radix == 2
    fan = [tuple(map(Q, cells['F1']['vertices'][0]))]
    fan += [tuple(map(Q, cells[f'F{i}']['vertices'][1])) for i in range(1,7)]
    assert len(set(fan)) == 7
    determinants = []
    for j, (a,b) in enumerate(zip(fan,fan[1:]+fan[:1])):
        for k,p in enumerate(fan):
            if k not in (j,(j+1)%7):
                det = orient(a,b,p)
                assert det > 0
                determinants.append(det)
    # Broad independently outward-checked binary64 box suffices.
    bx = list(map(common.dyadic, ['.4331904816','.4331904818']))
    by = list(map(common.dyadic, ['.4627797518','.4627797520']))
    assert A(bx[0]) < c['m'] and c['m'] < A(bx[1])
    assert A(by[0]) < c['F'] and c['F'] < A(by[1])
    apex_box = rect(*bx,*by)
    apex_dets = [orient(a,b,p) for a,b in zip(fan,fan[1:]+fan[:1]) for p in apex_box]
    assert min(apex_dets) > 0
    assert fan[0][1] > by[1] and fan[-1][1] > by[1]
    other_names = ['S1','S2','S3','R1','B1','B2']
    others = [[tuple(map(Q,v)) for v in cells[n]['vertices']] for n in other_names]
    for poly in others:
        assert area2(poly) > 0
        for j,(a,b) in enumerate(zip(poly,poly[1:]+poly[:1])):
            assert all(orient(a,b,p) >= 0 for p in poly)
        assert all(not (bx[0] <= p[0] <= bx[1] and by[0] <= p[1] <= by[1]) for p in poly)
    omega = [rect('.2186','.3301','.391','.4627799'),
             rect('.3301','.5095','.3355','.4627799')]
    traces = []
    for initial in omega:
        pieces = [initial]
        trace = []
        for name,cover in zip(['W']+other_names,[fan]+others):
            produced = [p for part in pieces for p in subtract(part,cover)]
            assert all(area2(p) >= 0 for p in produced)
            zero = [p for p in produced if area2(p) == 0]
            pieces = [p for p in produced if area2(p) > 0]
            trace.append(dict(subtract=name,positive_pieces=len(pieces),
                zero_pieces=len(zero),remaining_area2=str(sum(map(area2,pieces),Q(0))),
                positive_polygons=[serialize(p) for p in pieces]))
        assert not pieces
        traces.append(trace)
    return dict(fan=serialize(fan),apex_box=serialize(apex_box),
        least_fan_orientation=str(min(determinants)),
        least_apex_orientation=str(min(apex_dets)),omega_rectangles=list(map(serialize,omega)),
        subtraction_traces=traces,
        interpretation='The omitted zero-area pieces cannot hide an uncovered point: the cover is closed and each Omega+ rectangle has nonempty interior.')


def beta(m):
    return (-m.log()-1+m)/(1-m)**2


def lower_bound(lo, hi, c):
    x = ball(lo,hi)
    hb = common.h(x).lower()
    bb = beta(x).lower()
    assert bb > 0
    z = max(A(0), (x**3-c['t']).lower())
    return hb+bb*(z.root(3)**2)


def verify_leaves(leaves, lo, hi, target, c):
    parsed = [(Q(x),Q(y)) for x,y in leaves]
    assert parsed and parsed[0][0] == lo and parsed[-1][1] == hi
    assert all(x < y for x,y in parsed)
    assert all(x[1] == y[0] for x,y in zip(parsed[:-1],parsed[1:]))
    assert sum(y-x for x,y in parsed) == hi-lo
    margins = []
    for x,y in parsed:
        margin = lower_bound(x,y,c)-A(target)
        assert margin > 0
        margins.append(margin.lower())
    return str(min(margins))


def region_checks(c, stored=None):
    m0,m1,m2,m3 = map(Q,['.2182','.2186','.3301','.5095'])
    L1,L2,Fplus = map(Q,['.391','.3355','.4627799'])
    r = c['r']
    M1 = r+9*beta(r)**3*r**4/(-r.log())**3
    mG = (1+(1+8*c['t']).sqrt())/4
    assert 0 < A(m0) and A(m0) <= M1
    assert mG <= A(m3) and c['F'] < A(Fplus)
    out = []
    for i,(lo,hi,target) in enumerate([(m0,m1,Fplus),(m1,m2,L1),(m2,m3,L2)]):
        if stored is not None:
            leaves = stored['interval_checks'][i]['leaves']
        else:
            stack = [(lo,hi)]
            parsed = []
            while stack:
                x,y = stack.pop()
                if lower_bound(x,y,c) > A(target):
                    parsed.append((x,y))
                else:
                    assert y-x > Q(1,10**18), (x,y,target)
                    mid = (x+y)/2
                    stack.extend([(mid,y),(x,mid)])
                assert len(stack)+len(parsed) < 1000000
            leaves = [[str(x),str(y)] for x,y in parsed]
        least = verify_leaves(leaves,lo,hi,target,c)
        out.append(dict(interval=[str(lo),str(hi)],target=str(target),
                        leaves=leaves,least_margin_arb=least))
    result = dict(M1=str(M1),mG=str(mG),Fstar=str(c['F']),interval_checks=out)
    if stored is not None:
        assert result == stored
    return result


def build(stored=None):
    c = common.setup_constants()
    cells = common.input_data()
    return dict(precision_bits=common.ctx.prec,
        inputs_sha256=hashlib.sha256(common.SOURCE.read_bytes()).hexdigest(),
        common_sha256=hashlib.sha256(Path(common.__file__).read_bytes()).hexdigest(),
        z_bracket=c['z_bracket'],planar=planar_checks(c,cells),
        region=region_checks(c,stored['region'] if stored else None),
        scope='Sparse endpoint curved-region inclusion and exact planar cover only. Scalar certificate positivity and apex positivity are separate obligations.')


if __name__ == '__main__':
    started=time.monotonic()
    if sys.argv[1:] == ['verify']:
        saved=json.loads(PATH.read_text())
        assert digest(saved['data']) == saved['sha256']
        out=build(saved['data'])
        assert out == saved['data']
    else:
        assert not sys.argv[1:]
        out=build()
        PATH.write_text(json.dumps(dict(data=out,sha256=digest(out)),indent=2)+'\n')
    report=dict(verified=True,region_intervals=sum(len(x['leaves']) for x in out['region']['interval_checks']),
        region_interval_counts=[len(x['leaves']) for x in out['region']['interval_checks']],
        fan_orientation_checks=35,apex_orientation_checks=28,
        omega_rectangles=2,sha256=digest(out),seconds=time.monotonic()-started)
    PATH.with_suffix('.replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

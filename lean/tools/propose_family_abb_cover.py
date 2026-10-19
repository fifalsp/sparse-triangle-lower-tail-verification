#!/usr/bin/env python3
"""UNTRUSTED four-dimensional local ABB Hessian subdivision proposal.
The full parameter interval and full offset cube are searched. A positive
margin is proposal data only: Lean must verify the matrix and coverage.
"""
import argparse
import gzip
import json
import math
import time
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

from generate_family_leaf_example import I, S, ep, expbox, coeff
from propose_family_aaa_cover import eval_hessian


@lru_cache(maxsize=100000)
def endpoint(q):
    return ep(q)


@lru_cache(maxsize=10000)
def parameters(lo, hi):
    L = I(I(lo).l, I(hi).u)
    z = expbox(endpoint(lo), endpoint(hi))
    delta = 2*z*L/(1-z)**2
    b = expbox(endpoint(F(delta.l, S)), endpoint(F(delta.u, S)))
    return delta, coeff(z, L, b)


def scaled_hessian(box, qlo, qhi):
    q, x = box[:3], box[3:6]
    _, c1, c2, _, c4, mu3, A = box[6:]
    factor = 1+2*A-A*(q[0]+q[1]+q[2])
    H = [[None]*3 for _ in range(3)]
    for i in range(3):
        j, k = [a for a in range(3) if a != i]
        H[i][i] = c1+c2*(2-q[i])+c4*((q[i]-2)**2-2)+mu3*(x[j]+x[k])+x[j]*x[k]*factor
        for j in range(i):
            k = 3-i-j
            half = expbox(endpoint((qlo[i]+qlo[j])/2), endpoint((qhi[i]+qhi[j])/2))
            H[i][j] = H[j][i] = half*(mu3+x[k]*factor)
    return H


def factored_congruence(box, T):
    q, x = box[:3], box[3:6]
    _, c1, c2, _, c4, mu3, A = box[6:]
    G = x[0]*x[1]*x[2]*(1+2*A-A*(q[0]+q[1]+q[2]))
    D = [x[k]*(c1+c2*(2-q[k])+c4*((q[k]-2)**2-2)+
         mu3*(sum((x[l] for l in range(3) if l != k), I(0))-x[k])) for k in range(3)]
    u = [sum((I(T[k][i])*x[k] for k in range(3)), I(0)) for i in range(3)]
    s = [sum(T[k][i] for k in range(3)) for i in range(3)]
    return [[sum((I(T[k][i]*T[k][j])*D[k] for k in range(3)), I(0))+
             mu3*u[i]*u[j]+I(s[i]*s[j])*G for j in range(3)] for i in range(3)]


def propose(lo, hi, scaled=False, factored=False):
    delta, cs = parameters(lo[0], hi[0])
    base_lo = [lo[0]+F(delta.l, S), F(delta.l, S), F(delta.l, S)]
    base_hi = [hi[0]+F(delta.u, S), F(delta.u, S), F(delta.u, S)]
    qlo = [a+v for a, v in zip(base_lo, lo[1:])]
    qhi = [a+v for a, v in zip(base_hi, hi[1:])]
    box = [I(I(a).l, I(b).u) for a, b in zip(qlo, qhi)]
    box += [expbox(endpoint(a), endpoint(b)) for a, b in zip(qlo, qhi)] + cs
    H = scaled_hessian(box, qlo, qhi) if scaled else eval_hessian(box)
    M = [[(H[i][j].l+H[i][j].u)/(2*S) for j in range(3)] for i in range(3)]
    dot = lambda a, b: sum(a[i]*M[i][j]*b[j] for i in range(3) for j in range(3))
    vectors, norms = [], []
    for j in range(3):
        v = [float(i == j) for i in range(3)]
        for w, norm in zip(vectors, norms):
            c = dot(w, v)/norm
            v = [a-c*b for a, b in zip(v, w)]
        norm = dot(v, v)
        if norm <= 0:
            return None
        vectors.append(v)
        norms.append(norm)
    T = [[F(round(vectors[j][i]/math.sqrt(norms[j])*10**6), 10**6)
          for j in range(3)] for i in range(3)]
    J = [[sum((I(T[k][i])*H[k][l]*I(T[l][j])
               for k in range(3) for l in range(3)), I(0)) for j in range(3)] for i in range(3)]
    if factored:
        J = factored_congruence(box, T)
    margin = min(J[i][i].l-sum(max(-J[i][j].l, J[i][j].u)
                             for j in range(3) if j != i) for i in range(3))
    if margin <= 0:
        return None
    return {'lower': list(map(str, lo)), 'upper': list(map(str, hi)),
            'qLower': list(map(str, qlo)), 'qUpper': list(map(str, qhi)),
            'transform': [[str(x) for x in row] for row in T], 'margin': margin}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--budget', type=int, default=20000)
    parser.add_argument('--seconds', type=float, default=90)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--scaled', action='store_true')
    parser.add_argument('--factored', action='store_true')
    parser.add_argument('--resume', type=Path)
    args = parser.parse_args()
    if args.scaled and args.factored:
        parser.error('--scaled and --factored are alternative methods')
    r = F(1, 10)
    frontier = [([F(39, 10), -r, -r, -r], [F(19, 2), r, r, r])]
    codes, leaves = [], []
    if args.resume:
        saved = json.loads(gzip.decompress(args.resume.read_bytes()) if args.resume.suffix == '.gz' else args.resume.read_bytes())
        if saved.get('scaled', False) != args.scaled or saved.get('factored', False) != args.factored or saved['radius'] != str(r):
            raise ValueError('Resume proposal uses a different Hessian or radius')
        codes, leaves = saved['preorder'], saved['leaves']
        frontier = [(list(map(F, lo)), list(map(F, hi))) for lo, hi in saved['frontier']]
    started = time.monotonic()
    while frontier and len(codes) < args.budget and time.monotonic()-started < args.seconds:
        lo, hi = frontier.pop()
        try:
            row = propose(lo, hi, args.scaled, args.factored)
        except ValueError:
            row = None
        if row is not None:
            codes.append(0)
            leaves.append(row)
        else:
            axis = max(range(4), key=lambda j: hi[j]-lo[j])
            mid = (lo[axis]+hi[axis])/2
            if mid == lo[axis] or mid == hi[axis]:
                raise ValueError('Unresolved singleton')
            codes.append(1+axis)
            lh, rl = hi.copy(), lo.copy()
            lh[axis] = rl[axis] = mid
            frontier.extend([(rl, hi), (lo, lh)])
        if len(codes) % 2000 == 0:
            print(json.dumps({'nodes': len(codes), 'leaves': len(leaves),
                              'pending': len(frontier), 'seconds': time.monotonic()-started}), flush=True)
    result = {'trust_status': 'UNTRUSTED, Lean has not checked this proposal',
              'status': 'complete proposal' if not frontier else 'incomplete proposal',
              'scaled': args.scaled, 'factored': args.factored,
              'radius': str(r), 'preorder': codes, 'leaves': leaves,
              'frontier': [(list(map(str, a)), list(map(str, b))) for a, b in frontier],
              'seconds': time.monotonic()-started}
    raw = (json.dumps(result, separators=(',', ':'))+'\n').encode()
    args.output.write_bytes(gzip.compress(raw, mtime=0) if args.output.suffix == '.gz' else raw)
    print(json.dumps({k: v for k, v in result.items() if k not in ('preorder', 'leaves', 'frontier')})
          + f' leaves={len(leaves)} pending={len(frontier)}', flush=True)


if __name__ == '__main__':
    main()

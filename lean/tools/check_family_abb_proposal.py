#!/usr/bin/env python3
"""Independently reconstruct a full ABB proposal and its rational margins.

This is a generator consistency check, NOT a Lean certificate. It checks the
whole midpoint tree, exact contact-to-box bounds, and the supplied congruences.
Only the later Lean replay can discharge the formal certificate obligation.
"""
import argparse
import gzip
import hashlib
import json
import time
from fractions import Fraction as F
from pathlib import Path
from propose_family_abb_cover import parameters, endpoint, scaled_hessian
from generate_family_leaf_example import I, S, expbox


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('proposal', type=Path)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    raw = args.proposal.read_bytes()
    if args.proposal.suffix == '.gz':
        raw = gzip.decompress(raw)
    data = json.loads(raw)
    if data.get('status') != 'complete proposal' or data.get('frontier'):
        raise ValueError('Incomplete search')
    if data.get('scaled') is not True or data.get('factored', False) or data['radius'] != '1/10':
        raise ValueError('Wrong method or radius')
    pending = [([F('3.9')]+[-F('0.1')]*3, [F('9.5')]+[F('0.1')]*3)]
    cursor = 0
    start = time.monotonic()
    min_margin = None
    for node, code in enumerate(data['preorder']):
        if not pending:
            raise ValueError(f'Trailing tree code at {node}')
        lo, hi = pending.pop()
        if code == 0:
            row = data['leaves'][cursor]
            if list(map(F, row['lower'])) != lo or list(map(F, row['upper'])) != hi:
                raise ValueError(f'Leaf {cursor} does not match reconstructed box')
            delta, cs = parameters(lo[0], hi[0])
            contact_lo = [lo[0]+F(delta.l,S), F(delta.l,S), F(delta.l,S)]
            contact_hi = [hi[0]+F(delta.u,S), F(delta.u,S), F(delta.u,S)]
            qlo, qhi = list(map(F,row['qLower'])), list(map(F,row['qUpper']))
            if any(qlo[i] > contact_lo[i]+lo[i+1] or contact_hi[i]+hi[i+1] > qhi[i]
                   for i in range(3)):
                raise ValueError(f'Leaf {cursor} misses moving contact bounds')
            box = [I(I(a).l,I(b).u) for a,b in zip(qlo,qhi)]
            box += [expbox(endpoint(a),endpoint(b)) for a,b in zip(qlo,qhi)] + cs
            H = scaled_hessian(box,qlo,qhi)
            T = [[F(x) for x in r] for r in row['transform']]
            J = [[sum((I(T[k][i])*H[k][l]*I(T[l][j])
                       for k in range(3) for l in range(3)),I(0))
                  for j in range(3)] for i in range(3)]
            margin = min(J[i][i].l-sum(max(-J[i][j].l,J[i][j].u)
                         for j in range(3) if i != j) for i in range(3))
            if margin <= 0 or margin != row['margin']:
                raise ValueError(f'Leaf {cursor} margin mismatch or nonpositive margin')
            min_margin = margin if min_margin is None else min(min_margin,margin)
            cursor += 1
        elif type(code) is int and 1 <= code <= 4:
            axis = code-1
            mid = (lo[axis]+hi[axis])/2
            lh, rl = hi.copy(), lo.copy()
            lh[axis] = rl[axis] = mid
            pending.extend([(rl,hi),(lo,lh)])
        else:
            raise ValueError(f'Invalid split code {code}')
    if pending or cursor != len(data['leaves']):
        raise ValueError('Tree ended prematurely or extra leaves remain')
    report = {'status':'Python consistency check passed; full Lean replay remains unproved',
              'proposal_sha256':hashlib.sha256(raw).hexdigest(),
              'nodes':len(data['preorder']), 'leaves':cursor,
              'min_dyadic_margin_numerator':min_margin, 'dyadic_scale':S,
              'seconds':time.monotonic()-start}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)


if __name__ == '__main__':
    main()

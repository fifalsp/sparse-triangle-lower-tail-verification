#!/usr/bin/env python3
"""UNTRUSTED apex subdivision search using the refined constant enclosures.

Local leaves use exact rational containment in the already proved contact
cubes. Other leaves propose direct or second-order interval positivity.
All arithmetic, box coverage and final statements still require Lean replay.
The output saves the frontier, so a bounded run can be resumed without loss.
"""
import argparse
import json
import re
import time
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

from generate_family_leaf_example import I, S, ep, expbox
from propose_apex_local_boxes import expr, diff
from s1_expr_model import simp

ROOT = Path(__file__).resolve().parents[1]


def compiled(expressions):
    """A shared arithmetic DAG; it has no theorem-producing authority."""
    nodes, seen = [], {}

    def add(e):
        if e in seen:
            return seen[e]
        op, *a = e.t
        if op == 'c':
            node = (op, I(a[0]))
        elif op == 'v':
            node = (op, a[0])
        else:
            node = (op, *(add(x) for x in a))
        seen[e] = len(nodes)
        nodes.append(node)
        return seen[e]

    outputs = [add(e) for e in expressions]

    def run(box):
        values = []
        for op, *a in nodes:
            if op == 'c':
                value = a[0]
            elif op == 'v':
                value = box[a[0]]
            elif op == '-':
                value = -values[a[0]]
            elif op == '+':
                value = values[a[0]] + values[a[1]]
            else:
                value = values[a[0]] * values[a[1]]
            values.append(value)
        return [values[i] for i in outputs]
    return run


def primitive_bounds():
    source = (ROOT / 'SparseLowerTail/Section05/ApexRefinedPrimitives.lean').read_text()
    source = source.split('def apexRefinedPrimitiveBounds', 1)[1].split('theorem', 1)[0]
    source = re.sub(r'\(([0-9/]+) : ℚ\)', r'\1', source)
    bounds = [(F(a), F(b)) for a, b in re.findall(r'⟨([0-9/]+),([0-9/]+)⟩', source)]
    if len(bounds) != 9:
        raise ValueError('Expected nine actual primitive enclosures')
    return bounds


@lru_cache(maxsize=100000)
def endpoint(q):
    return ep(q)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fan', type=int, choices=range(1, 7), required=True)
    parser.add_argument('--budget', type=int, default=200000)
    parser.add_argument('--seconds', type=float, default=3600)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    cell = json.loads((ROOT.parent / 'data/cover.json').read_text())['cells'][f'F{args.fan}']
    bounds = primitive_bounds()
    constants = [I(I(a).l, I(b).u) for a, b in bounds]
    solutions = json.loads((ROOT / 'data/apex-refined-system-proposal.json').read_text())['solutions']
    theta = [I(*solutions[args.fan-1][[0, 2, 3, 4].index(j)]) if t is None else I(F(t))
             for j, t in enumerate(cell['theta'])]
    fixed = constants[4:] + theta + [I(F(cell['lam']))]
    e = expr()
    gradients = [simp(diff(e, i)) for i in range(3)]
    hessians = [simp(diff(g, j)) for g in gradients for j in range(3)]
    center_eval = compiled([e] + gradients)
    hessian_eval = compiled(hessians)
    direct_eval = compiled([e])

    def environment(lo, hi):
        return ([I(I(a).l, I(b).u) for a, b in zip(lo, hi)] +
                [expbox(endpoint(a), endpoint(b)) for a, b in zip(lo, hi)] + fixed)

    def classify(lo, hi):
        for mixed in (False, True):
            radius = F(cell['local_radii'][int(mixed)])
            contact = [bounds[0], bounds[int(mixed)], bounds[int(mixed)]]
            if all(b-radius <= l and h <= a+radius
                   for (a, b), l, h in zip(contact, lo, hi)):
                return int(mixed)
        whole = environment(lo, hi)
        if direct_eval(whole)[0].l > 0:
            return 3
        mid = [(a+b)/2 for a, b in zip(lo, hi)]
        radii = [(b-a)/2 for a, b in zip(lo, hi)]
        velocities = [I(I(-r).l, I(r).u) for r in radii]
        val, *grad = center_eval(environment(mid, mid))
        first = sum((v*g for v, g in zip(velocities, grad)), I(0))
        second = I(0)
        for k, h in enumerate(hessian_eval(whole)):
            i, j = divmod(k, 3)
            vi, vj = velocities[i], velocities[j]
            prod = (I(0, -((-max(vi.l**2, vi.u**2))//S)) if i == j else vi*vj)
            second += prod*h
        return 2 if 2*val.l + 2*first.l + second.l > 0 else None

    q = F(cell['Q'])
    codes, frontier = [], [([F(0)]*3, [q]*3)]
    if args.resume:
        old = json.loads(args.output.read_text())
        if old['fan'] != args.fan or F(old['Q']) != q:
            raise ValueError('Resume fan/domain mismatch')
        codes = old['preorder']
        frontier = [(list(map(F, lo)), list(map(F, hi))) for lo, hi in old['frontier']]
    start, initial = time.monotonic(), len(codes)
    while frontier and len(codes)-initial < args.budget and time.monotonic()-start < args.seconds:
        lo, hi = frontier.pop()
        lo = [max(lo), max(lo[1:]), lo[2]]
        hi = [hi[0], min(hi[:2]), min(hi)]
        if any(a > b for a, b in zip(lo, hi)):
            codes.append(4)
            continue
        kind = classify(lo, hi)
        if kind is not None:
            codes.append(kind)
        else:
            axis = max(range(3), key=lambda i: hi[i]-lo[i])
            mid = (lo[axis]+hi[axis])/2
            if mid == lo[axis] or mid == hi[axis]:
                raise ValueError('Unresolved singleton: not evidence of negativity')
            codes.append(5+axis)
            left_hi, right_lo = hi.copy(), lo.copy()
            left_hi[axis] = right_lo[axis] = mid
            frontier.extend([(right_lo, hi), (lo, left_hi)])
        if len(codes) % 2000 == 0:
            print(json.dumps({'nodes': len(codes), 'pending': len(frontier),
                              'seconds': round(time.monotonic()-start, 2)}), flush=True)
    result = {'trust_status': 'UNTRUSTED proposal; no Lean coverage/positivity claim',
              'fan': args.fan, 'Q': str(q), 'preorder': codes,
              'frontier': [(list(map(str, lo)), list(map(str, hi))) for lo, hi in frontier],
              'status': 'complete proposal' if not frontier else 'incomplete proposal',
              'counts': dict(Counter(codes)), 'seconds_this_run': time.monotonic()-start}
    args.output.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('preorder', 'frontier')}, indent=2))


if __name__ == '__main__':
    main()

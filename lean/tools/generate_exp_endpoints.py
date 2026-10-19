#!/usr/bin/env python3
"""Propose compact exact exp(-q) endpoint data; Lean checks every comparison.

Usage: python3 lean/tools/generate_exp_endpoints.py 0 1 16 --output /tmp/Endpoints.lean
The generated file imports ExpEndpoints and proves each Valid claim using
`decide +kernel`. Python output alone is not a verification result.
"""
from argparse import ArgumentParser
from fractions import Fraction
from math import factorial
from pathlib import Path


def endpoint(q: Fraction, order: int, bits: int):
    if not -16 <= q <= 16:
        raise ValueError('Every endpoint must lie in [-16,16]')
    if order < 1 or bits < 1:
        raise ValueError('order and bits must be positive')
    x = -q / 16
    polynomial = sum((x**m / factorial(m) for m in range(order)), Fraction())
    remainder = abs(x)**order * Fraction(order + 1, factorial(order) * order)
    scale = 2**bits

    def lower(value):
        return Fraction(value.numerator * scale // value.denominator, scale)

    def upper(value):
        return -lower(-value)

    lo, hi = lower(polynomial - remainder), upper(polynomial + remainder)
    if lo < 0:
        raise ValueError('Increase the Taylor order to get a nonnegative base lower bound')
    return q, order, lo, hi, lower(lo**16), upper(hi**16)


def rat(value):
    return f'({value.numerator}/{value.denominator} : ℚ)'


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('q', type=Fraction, nargs='+')
    parser.add_argument('--order', type=int, default=20)
    parser.add_argument('--bits', type=int, default=60)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    lines = ['import SparseLowerTail.Numerics.ExpEndpoints', '',
             '/-! Generated rational proposals; the Valid proofs are kernel checked. -/',
             'namespace SparseLowerTail.Numerics.GeneratedExpEndpoints',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 4000000', '']
    for i, q in enumerate(dict.fromkeys(args.q)):
        q, order, lo, hi, lower, upper = endpoint(q, args.order, args.bits)
        lines += [f'def endpoint{i} : ExpEndpointCertificate :=',
                  f'  ⟨{rat(q)}, {order}, {rat(lo)}, {rat(hi)}, {rat(lower)}, {rat(upper)}⟩',
                  f'theorem endpoint{i}_valid : endpoint{i}.Valid := by decide +kernel',
                  f'theorem endpoint{i}_bounds :',
                  f'    Bounds (Real.exp (-(endpoint{i}.q : ℝ)))',
                  f'      (endpoint{i}.lower : ℝ) (endpoint{i}.upper : ℝ) :=',
                  f'  endpoint{i}.bounds endpoint{i}_valid', '']
    lines += ['end SparseLowerTail.Numerics.GeneratedExpEndpoints', '']
    args.output.write_text('\n'.join(lines))


if __name__ == '__main__':
    main()

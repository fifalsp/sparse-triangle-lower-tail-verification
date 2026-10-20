#!/usr/bin/env python3
"""Emit certificates for the exact crossing bracket in the current manuscript.

This reuses the checked arithmetic proof generator at greater precision. Decimal
arithmetic proposes enclosures; the emitted Lean proofs validate every bound.
Existing threshold certificates are left intact.
"""
from pathlib import Path
from fractions import Fraction as F

ROOT = Path(__file__).resolve().parents[1]
LOWER = F('0.0200554310548823255291088')
UPPER = F('0.0200554310548823255291090')


def generate():
    src = (ROOT / 'tools/generate_threshold_digits.py').read_text()

    def replace(old, new):
        nonlocal src
        assert src.count(old) == 1, old
        src = src.replace(old, new)

    replace("out=Path('SparseLowerTail/Section04/ThresholdDigits.lean')",
            "out=Path('SparseLowerTail/Section04/ManuscriptThresholdDigits.lean')")
    replace('import SparseLowerTail.Section04.BalancedPhase',
            'import SparseLowerTail.Section04.BalancedPhase\nimport SparseLowerTail.Numerics.PreciseLogTwo')
    replace('namespace SparseLowerTail.Section04\n',
            'namespace SparseLowerTail.Section04.ManuscriptDigits\n'
            'set_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n\n'
            f'def digitZLower : ℝ := {LOWER.numerator}/{LOWER.denominator}\n'
            f'def digitZUpper : ℝ := {UPPER.numerator}/{UPPER.denominator}\n')
    assert src.count('end SparseLowerTail.Section04') == 2
    src = src.replace('end SparseLowerTail.Section04', 'end SparseLowerTail.Section04.ManuscriptDigits')
    replace('tools/generate_threshold_digits.py.', 'tools/generate_manuscript_threshold_digits.py.')
    replace('zs=[F(2005543105488,10**14),F(2005543105489,10**14)]',
            f'zs=[F({LOWER.numerator},{LOWER.denominator}),F({UPPER.numerator},{UPPER.denominator})]')
    replace('def bounds(d,p=20):', 'def bounds(d,p=32):')
    replace('scale=10**24;', 'scale=10**36;')
    replace("z,-zd.ln(),40)", "z,-zd.ln(),65)")
    replace("t,-td.ln(),18)", "t,-td.ln(),30)")
    replace('(n := 20)', '(n := 32)')
    replace('log_two_bounds_22.1', 'log_two_bounds_40.1')
    replace('log_two_bounds_22.2', 'log_two_bounds_40.2')
    replace('convert digit_normalized_lower using 1\\n  norm_num [digitZLower]',
            'exact digit_normalized_lower')
    replace('convert digit_normalized_upper using 1\\n  norm_num [digitZUpper]',
            'exact digit_normalized_upper')
    env = {}
    exec(compile(src, 'manuscript_threshold_generator', 'exec'), env)
    return env


if __name__ == '__main__':
    generate()
    print('Proposed exact manuscript bracket:', LOWER, UPPER, 'width', UPPER - LOWER)

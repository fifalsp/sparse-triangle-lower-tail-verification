# Twelve-cell threshold cover

The verifier reads `data/cover.json`, containing exact rational encodings of the
printed binary64 cell data. It evaluates **three times** the paper's certificate
`Psi`. Every strict numerical target is consequently multiplied by three.
Tangency replaces precisely coordinates `0,2,3,4` of each fan's twelve-coordinate
vector. The remaining coordinates and the published neighborhoods stay fixed.

From the repository root:

```sh
python verification/cover/build_templates.py --check
python verification/cover/endpoint_common.py
python verification/cover/planar_coverage.py
python verification/cover/verify_penalized_constants.py
python verification/cover/verify_endpoint.py F1 apex 2000000
python verification/cover/verify_endpoint.py F1 0 2000000
```

`endpoint_common.py` checks both crossing signs, all four printed enclosures in
`lem:digits` (formerly `bal:digits`), all twelve support levels, and all six validated tangency solves.
`planar_coverage.py` proves the curved-domain inclusion and exact planar cover;
it does not prove positivity of the scalar certificates. The full positivity
suite consists of six fan-apex jobs and thirty-six fixed-vertex jobs. Each job
must exit zero, report `complete`, and have zero pending boxes. Exhausted node
budgets, unresolved interval signs, and failed local tests cannot pass.
The verifier refuses optimized Python (`-O`/`-OO`), which disables assertions.

Results go to `results/cover/`. Set `SPARSE_VERIFICATION_RESULTS` to another
results root if desired. Scripts do not read the manuscript, research directory,
or old reports. `build_templates.py --check` reconstructs the formulas in memory
and compares the exact generated code and manifest without writing; only the
explicit `--write` option regenerates these committed source files.

## Computational proof bridge

The direct bound and the first two Taylor bounds use the same interval
inclusion principle as the paper. The implementation also has a valid
alternative third-order bound. It is not a literal implementation of the
current draft's box-Hessian supporting-quadratic bound.

Write `d=q-c`, `|d_i|<=r_i`, `g=gradient Phi(c)`, and `H=Hessian Phi(c)`. Let `S3`
be the sum, with multinomial multiplicities, of upper bounds for the absolute
third partial derivatives on the whole box. Taylor's theorem gives

```
Phi(c+d) >= Phi(c) + g.d + (d.H.d)/2 - S3 * max(r)^3 / 6.
```

When the exact center Hessian is certified positive definite, its quadratic
polynomial is bounded below by its supporting affine plane at any proposed
point `y`. Minimizing that plane over the coordinate box gives

```
Phi(c) + g.y + (y.H.y)/2
  + sum_i min((g+H.y)_i*(-r_i-y_i), (g+H.y)_i*(r_i-y_i))
  - S3 * max(r)^3 / 6.
```

All terms are bounded with Arb. NumPy only proposes `y` and a positive Hessian
lower bound; neither floating-point proposal is accepted as proof. The chosen
`y` is converted to an exact dyadic rational. Positive definiteness and every
final sign are independently checked with Arb. The target is accepted only
when the resulting strict lower bound exceeds it.

At an exact tangency pattern, the local test verifies `H >= ell I` at the
center and `radius*S3 < 3*ell` throughout the published neighborhood. Thus the
Taylor remainder is smaller than the positive quadratic term away from the
center. The code fails if this test fails at a printed radius; it never silently
shrinks that radius.

The interval formulas, derivative order, certificate scaling, and input
conventions are unchanged from the independently reconstructed historical
cover, except that the apex target now uses the paper's exact binary64
interpretation of `1e-12`. This is slightly below the exact decimal rational
`1/10^12` used by the historical replay. All fixed-vertex targets already had
the paper's binary64 interpretation.

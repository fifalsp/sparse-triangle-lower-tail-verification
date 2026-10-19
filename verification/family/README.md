# Certificate family

This module implements the computer-assisted part of Proposition `prop:family`
in the current Overleaf manuscript and Appendix `app:family`. It verifies
nonnegativity of the explicit three-variable certificate for every
`L ∈ [3.9, 9.5]`, and identifies its two ordered zero patterns. This is an
auxiliary analytic certificate, not a standalone formal verification of the
manuscript's graphon argument.

From the repository root:

```sh
python verification/family/verify_family.py
python verification/family/verify_family.py --quick
```

The first command performs the entire verification. The second checks rational
identities, elementary endpoint/tail inequalities, coefficient signs, and
independent Taylor-formula consistency tests. Its top-level status is
`quick_checks_passed`; it does **not** establish compact-domain positivity.

Outputs go to `results/family`, or to the directory passed as `--output-dir`.
`--max-nodes N` sets a separate node budget for each of `local1`, `local2`, and
`compact` (default 20,000,000). Budget exhaustion writes the unresolved boxes,
marks the run `incomplete`, and exits nonzero. Every full run recomputes the local
Hessian certificates before permitting their use in the compact cover. Existing
successful reports are never read as proof inputs. The output `family.json`
binds the result to the Python sources by SHA-256 and records the numerical
library version.

## Map to the manuscript

- `core.coefficients`: equations `eq:branch`, `eq:certcoef`, `eq:certpsi`.
- `symbolic.py`: exact rational tangency identities, determinant, mean-sign
  identity and both rational identities in the tail lemma.
- `core.Jet` and `core.enclosure`: normalized Taylor coefficients through order
  three and the `L`-interval enclosures in Appendix `app:family`.
- `core.hessian(..., scaled=True)`: equation `appA3:hessian` after the specified
  diagonal congruence. `core.positive_definite` verifies the Gershgorin test.
- `verify_family.subdivide('local', ...)`: Lemma `appA3:hess` for the two moving
  cubes with radius equal to the exact binary64 value `0.1`.
- `core.compact_test`: membership test (C1) and Taylor lower bound (C2), including
  all three valid choices of each scalar quadratic lower bound `beta_i`.
- `verify_family.subdivide('compact', ...)`: the ordered compact cover in
  Proposition `appA3:compact`.

## Inclusion and arithmetic conventions

All acceptance decisions use strict outward-rounded Arb ball inequalities at
128 bits. Python floats specify exact dyadic endpoints, split points and the
local radius. The binary64 `3.9` lies below the exact decimal `39/10`, while
`9.5` is exact, so the initial parameter interval contains the one in the draft.
The midpoint-radius construction explicitly includes binary64 midpoint rounding.
Local symmetry is imposed on displacements from the moving zero, while the
compact cover imposes symmetry on the actual `q` coordinates.

NumPy only proposes a congruence matrix from a midpoint eigendecomposition. Each
entry of the proposed matrix is reinterpreted as its exact binary64 value, and
Arb verifies strict diagonal dominance of the transformed interval matrix. No
numerical eigenvalue is itself an acceptance condition. Floating-point selection
among several already valid lower bounds or subdivision directions changes only
search efficiency.

`selfcheck.py` additionally compares the custom Taylor recurrences with FLINT's
independent `arb_series` implementation, and checks the gradient and Hessian via
directional series. These checks supplement the explicit interval formulas;
they are not the reason a positive box is accepted. The mathematical reduction
from the unbounded domain to the compact cube, and from the certificate to a
graphon minimizer classification, remain in the manuscript.

The first fresh full replay of this implementation completed all three stacks:
59 nodes for `local1`, 168,785 for `local2`, and 70,271 for `compact`. Node counts
can depend on platform and numerical-library versions; success requires an
empty stack, not a particular count. Source and manuscript provenance are in
`provenance.json`.

# Lean 4 formalization: progress toward Theorem 1.3

**Status: partial formalization. The main theorem has not been proved in Lean.**
The target is the variational theorem `thm:main` in the manuscript recorded in
[`data/manuscript.json`](../data/manuscript.json), checked against the October 19,
2026 PDF. This is Theorem **1.3**, not Theorem 1.8. The probabilistic sparse-LDP
and conditional-structure results are additional, later formalization tasks.

At the authors' request, the intended proof may use **explicitly stated external
and classical results as hypotheses**. Our own arguments remain obligations.
See [ASSUMPTIONS.md](ASSUMPTIONS.md) for the exact scope and named inputs.
Passing an axiom audit does not discharge an external hypothesis.

## What the target actually says

For every target 0 < r < 1, the infimum of the sparse entropy over **all
measurable graphons** with triangle density at most r³ equals the balanced
SBM infimum. Above the transition the optimizer is constant; at the transition
both the constant and one balanced SBM occur; below it the balanced pair is
unique and all graphon optimizers have that form, up to null sets and relabeling.

[`MainStatement.lean`](SparseLowerTail/MainStatement.lean) encodes these claims
as the proposition `SparseLowerTail.MainTheorem`. **Defining this proposition
is not a proof of it.** There is no axiom asserting it and no theorem producing
an inhabitant of it. The target includes the exact rational bracket for r*;
the decimal brackets for a* and b* have not yet been encoded.

The definitions use Lebesgue measure on [0,1] and its product measures, with
almost-everywhere symmetry and bounds. Graphons are not restricted to block
models. `IsBalanced` uses a measurable partition of mass one half. Its
integral formulas are proved; its equivalence to the paper's
measure-preserving-relabeling formulation still requires `lem:relabelB`.

## Completed proof components

| Paper content | Lean file / declarations | Scope |
| --- | --- | --- |
| h(x) = x log x − x + 1; definitions of F, t, V, and the balanced problem | [`Basic.lean`](SparseLowerTail/Basic.lean) | Definitions use actual Lebesgue integrals; h(0) = 1 is checked. |
| Elementary well-posedness | [`Foundations.lean`](SparseLowerTail/Foundations.lean): `cost_integrable`, `cost_nonneg`, `cost_le_one`, `value_nonneg`, `value_le_entropy`, `isMinimizer_iff` | Entropy cost is integrable and lies in [0,1]. The optimizer definition agrees with feasible plus F = V. Parallel facts hold for the balanced infimum. |
| Triangle density and null sets | [`Triangle.lean`](SparseLowerTail/Triangle.lean): `triangle_integrable`, `triangle_nonneg`, `triangle_le_one`, `triangle_congr_ae`, `isMinimizer_congr_ae` | The triangle integral is well-defined and in [0,1]; changing a representative on a null set preserves cost, density, and optimizer status. |
| Equation `eq:Bdens` for F and t | [`Balanced.lean`](SparseLowerTail/Balanced.lean): `cost_twoBlock`, `triangle_twoBlock`, `IsBalanced.cost_eq`, `IsBalanced.triangle_eq` | Proven by integration for **any measurable partition of mass 1/2**, not just by counting formal labels. |
| Easy direction of Theorem 1.3(a) | [`Balanced.lean`](SparseLowerTail/Balanced.lean): `value_le_balancedValue` | V(r) ≤ V_SBM(r) for 0 ≤ r ≤ 1. Also V(r) ≤ 1/2 using the actual bipartite graphon. **The reverse inequality is not proved.** |
| Attainment in the balanced problem | [`BalancedExistence.lean`](SparseLowerTail/BalancedExistence.lean): `exists_balancedMinimizer`, `balancedValue_attained` | Compactness gives a minimizing pair. This establishes neither uniqueness nor existence of an unrestricted graphon minimizer. |
| Section 8, proof of `thm:main`, Steps 1–4 | [`Continuation.lean`](SparseLowerTail/Continuation.lean): `classification_on_interval` | The infimum/continuation argument is proved with explicit assumptions for the small-target range, openness, seed near the transition, and boundary exclusion. Those graphon-specific assumptions remain to be discharged. |
| Rational tangency calculations in `lem:certcoef` | [`CertificateAlgebra.lean`](SparseLowerTail/CertificateAlgebra.lean): `value_aaa`, `gradient_aaa`, `value_abb`, `gradient_abb_a`, `gradient_abb_b` | All five exact normalized identities, with explicit nonzero-denominator assumptions. The coefficients match `verification/family/symbolic.py`. |
| `lem:branch`, `s4:eq:EL` | [`Branch.lean`](SparseLowerTail/Section04/Branch.lean), [`Codegree.lean`](SparseLowerTail/Section04/Codegree.lean), [`BalancedStationary.lean`](SparseLowerTail/Section04/BalancedStationary.lean) | Both directions of the explicit stationary branch parametrization, connected to the a.e. graphon equation. Codegrees are computed for any measurable equal partition. |
| `lem:ray`, parts (a)–(d) | [`Ray.lean`](SparseLowerTail/Section04/Ray.lean) | Ray normalization and its converse, cost scaling, positivity, regularity, and the exact derivative of the ray cost gap. |
| Complete `cor:Vbal` | [`BalancedPhase.lean`](SparseLowerTail/Section04/BalancedPhase.lean), using [`BalancedClassification.lean`](SparseLowerTail/Section04/BalancedClassification.lean) and [`EntropyGeometry.lean`](SparseLowerTail/Section04/EntropyGeometry.lean) | Values and all minimizing balanced pairs below, at, and above the transition; the crossing equals the main statement's supremum threshold. This is the balanced problem only. |
| `lem:active` | [`ActiveConstraint.lean`](SparseLowerTail/Section04/ActiveConstraint.lean): `minimizer_triangle_eq` | Every unrestricted graphon minimizer at 0 < r < 1 has triangle density exactly r³. No external hypothesis is needed. |
| `eq:Bdens` for edge density; full `lem:Bderivative` | [`BalancedStationary.lean`](SparseLowerTail/Section04/BalancedStationary.lean), [`BalancedDerivative.lean`](SparseLowerTail/Section04/BalancedDerivative.lean), [`CrossingDelta.lean`](SparseLowerTail/Section04/CrossingDelta.lean) | Edge-density and multiplier identities; C¹ cost on the actual inverse branch, with derivative −μr². |
| Transfer step in `prop:smalldata` | [`ExternalReduction.lean`](SparseLowerTail/Section07/ExternalReduction.lean) | Given the explicitly assumed KP26 reduction and a supporting balanced penalized minimizer, prove constrained global optimality and its value. Identifying the supported range and equality rigidity remain open obligations. |

The normalized rational tangency identities are now connected to the actual
logarithms, coefficients, and derivatives by
[`CertificateBridge.lean`](SparseLowerTail/Section08/CertificateBridge.lean).
[`CertificateSigns.lean`](SparseLowerTail/Section08/CertificateSigns.lean)
completes the **stated conclusion of `lem:certcoef`** for every 0 < z ≤ 1/40:
the coefficient signs, negative c̄, and all contact values and partial derivatives.
The required decimal bounds on log 40 are proved in Lean. The determinant
uniqueness assertion inside the paper's proof is not separately formalized;
it is unnecessary for this conclusion. **Global certificate positivity is still
unproved in Lean.**

[`Unimodal.lean`](SparseLowerTail/Section04/Unimodal.lean),
[`BranchInverse.lean`](SparseLowerTail/Section04/BranchInverse.lean), and
[`Crossing.lean`](SparseLowerTail/Section04/Crossing.lean), together with
`CrossingDelta.lean` and `CrossingShape.lean`, prove the complete unimodality and
crossing theorems. The inverses and unique crossing are constructed from proved
facts, not supplied as hypotheses.

[`StrictImprovement.lean`](SparseLowerTail/Section05/StrictImprovement.lean)
proves `thm:threshold`(iii): below the threshold, the unrestricted value is strictly
less than h(r), and every minimizer is nonconstant. It does not establish the
reverse value inequality or the above/at-threshold classification.

## Remaining dependencies of the main theorem

The goal is to connect these components in the same order as the paper's proof.
An unchecked item is not supplied as an axiom.

- [ ] Unrestricted graphon minimizer existence, compactness, and regularity.
- [x] Section 4: stationary branch, ray calculus, entropy geometric reduction,
      and activity of the graphon triangle constraint.
- [x] Section 4: unimodality, actual inverse branches, unique crossing, and the
      full balanced optimizer classification (`cor:Vbal`).
- [ ] Certified threshold intervals (`lem:digits`).
- [ ] Threshold global inequality and equality classification (`thm:threshold`).
- [ ] Openness and the seed near the transition (`cor:open`, `cor:seed`).
- [ ] Small-target classification (`thm:smalltail`). KP26 is now an explicit
      external hypothesis; the paper's supporting-branch and rigidity arguments
      must still be proved.
- [ ] Boundary comparison (`lem:boundary`), the Euler–Lagrange equation, and the
      certificate expectation identity (`s8:expect`).
- [x] Analytic bridge and sign estimates for the certificate (`lem:certcoef`).
- [ ] A Lean proof-producing version of the interval certificates, including
      the cover and family positivity checks (`prop:cover`, `prop:family`).
- [ ] Tie exclusion and equality-case rigidity (`lem:tieexclusion`).
- [ ] Equivalence between balanced partitions and relabelings (`lem:relabelB`).
- [ ] Assemble the graphon-specific inputs and prove `MainTheorem`.

**Next mathematical bottleneck:** prove the global lower bound and its equality
conditions. The existing Python/Arb reports are computational evidence used by
the paper, but are not Lean proof terms. Loading their success flags would not
close the missing Lean obligations.

## Stable links to the manuscript

[`proof-map.json`](proof-map.json) records 32 stable LaTeX labels, their statement
and proof fingerprints, checked scope, Lean declarations, and explicit inputs.
Displayed theorem numbers are historical metadata, not identifiers. Thus a
renumbering does not require renaming Lean declarations.

From the repository root:

```sh
python3 tools/check_manuscript_map.py /path/to/revised/arxiv_v1.tex
python3 tools/check_lean_map.py
python3 -m unittest discover -s tests -p test_manuscript_map.py
```

The first command flags changed statements, changed adjacent proofs, and missing
labels for review without accepting them automatically. The second checks the
mapped files and asks Lean to resolve every mapped declaration. Neither check
establishes that a mathematical translation is faithful. Shared macro changes
and unmapped statements also require review; see the assumptions guide.

## Build and audit

Install Lean's `elan` toolchain manager, then from this directory run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean is pinned to **4.24.0** in `lean-toolchain`. Mathlib is pinned to its matching
release; `lake-manifest.json` records exact dependency commits. Do not replace
these with a floating `master` branch. The cache supplies precompiled library
artifacts; the project sources are compiled by `lake build`.

[`Audit.lean`](Audit.lean) traverses the imported project declarations and their
transitive axiom dependencies. It rejects `sorryAx`, custom axioms, and compiler-
trust axioms from `native_decide`. The only allowed axioms are Lean/mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound`. This audit checks proof
trust, **not** whether our target proposition faithfully translates the paper;
the translation and the remaining dependency list still require mathematical review.

## Progress log

### 2026-10-19 — first formalization milestone

- Pinned a reproducible Lean/mathlib project and transcribed the main variational
  statement, including the transition and optimizer equality cases.
- Proved the foundational integral and infimum lemmas and constructed balanced
  SBMs as genuine graphons.
- Proved the balanced density/cost formulas, finite-dimensional attainment,
  V ≤ V_SBM, and the continuation argument with its assumptions exposed.
- Replaced the five symbolic rational identity checks with Lean proof terms.
- Added a transitive axiom audit. No completed theorem uses a proof placeholder,
  a new mathematical axiom, or a Python verification result as a premise.
- **Not achieved:** a Lean proof of Theorem 1.3, its hard lower bound, or its
  global optimizer classification. This log must retain that distinction until
  those proofs actually compile.

### 2026-10-19 — graphon library survey (user suggestion)

Our pinned Mathlib 4.24.0 source contains no graphon/cut-norm development; its
`Set.graphOn` is the graph of a function and is unrelated. A search of the
current upstream module index also found no graphon or cut-norm module.
There are, however, separate libraries built **on top of Mathlib**:

| Candidate | Useful components | Verification / compatibility status |
| --- | --- | --- |
| [Cameron Freer's `graphon`](https://github.com/cameronfreer/graphon/tree/9f7be59fa754d260a544b4cfd83d6a5b94f7552e) | `Graphon.Basic` uses a.e. equivalence classes; `Graphon.CutNorm`, `CutDistance`, `Counting`, `Regularity`, `Compactness` provide the relevant infrastructure. | Source inspected at commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`. Lean/Mathlib **4.32.0**, Apache-2.0. Its audit list includes `Graphon.complete` and `Graphon.compact`; upstream reports only the three standard axioms for those audited declarations. **Not yet built or independently axiom-audited here; not yet a dependency.** |
| [`math-commons/graphons`](https://github.com/math-commons/graphons) | Cut norm/distance, counting, weak regularity, step graphons. | Its [axiom audit](https://github.com/math-commons/graphons/blob/main/AXIOM_AUDIT.md) explicitly retains additional mathematical axioms, including two used by compactness/completeness. Those global axioms would fail our audit; classical results may instead be stated as explicit hypotheses under the authors' revised scope. |

The preferred candidate for further evaluation is Freer's library. The inspected
source gives sequential compactness as `Graphon.compact` and supplies cut-distance
control of homomorphism densities. These could replace a large amount of
foundational work, but **do not themselves prove our entropy lower bound or
optimizer classification**.

Integration needs three checks: compile and audit the exact imported theorems;
bridge our representative-based graphons to its `AEEqFun`-based graphons while
preserving F and triangle density; and prove the entropy lower semicontinuity
needed to turn compactness into existence of a minimizer. The version difference
requires a controlled toolchain upgrade, not an untested change of the current pin.
No external source files have been copied into this repository and no external
mathematical axioms have been added.

### 2026-10-19 — branch analysis and explicit assumptions

- Integrated the cooperatively developed entropy, branch, ray, codegree and
  graphon stationary modules, plus the full active-constraint lemma.
- Proved the constrained consequence of the named external KP26 reduction.
  The external theorem is an explicit parameter, not a project axiom.
- Added stable-label tracking, manuscript change detection, and Lean declaration
  link checks. Changing statement numbers alone does not invalidate the map.
- Corrected the target's threshold enclosure to a **closed** rational interval,
  matching the wording of `lem:digits`. This is a statement correction, not a
  newly proved numerical bound.
- **Still incomplete:** unique crossing, global lower bound, equality rigidity,
  proof-producing numerical certificates, and assembly of `MainTheorem`.

### 2026-10-19 — complete balanced phase classification

- Proved the complete unimodality, inverse-branch, and crossing analysis. The
  endpoint limits, unique crossing, and cost-gap signs all have Lean proofs.
- Completed `cor:Vbal` and identified its transition with `threshold`. Proved
  the strict order of the two branch values around their triangle target.
- Completed `lem:Bderivative` for the actual inverse branch.
- Completed the stated coefficient-sign and tangency conclusion of
  `lem:certcoef`, including kernel-checked logarithmic numerical bounds.
- Derived the unrestricted strict improvement and exclusion of constant
  minimizers below the threshold (`thm:threshold`(iii)).
- **Still incomplete:** the unrestricted global lower bound and rigidity,
  numerical threshold brackets, global certificate positivity, and the main
  theorem assembly. The scalar classification alone does not prove the main
  graphon theorem.

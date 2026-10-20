# Lean 4 formalization: progress toward Theorem 1.3

The project formalizes the authors' arguments in the paper, with cited external
and standard classical results supplied as explicit hypotheses.

**Verified:** 34 nonapex full-domain certificates and apex fans F2, F3, F4, F5 and
F6 have passed Lean builds and axiom audits. The main variational theorem's
assembly and the proof components below are checked; the remaining certificates
and combined integration are in progress.

The live Overleaf source was downloaded through Google Chrome on October 20.
Its certificate tables match the running jobs. The
[current manuscript inventory](manuscript-coverage.json) tracks all labeled
results, including the probabilistic rate and conditioned-structure arguments
in Section 3. The [revision comparison](manuscript-review-20261019.json) records
35 changed or renamed mapped labels for review. Build records below retain their
original manuscript baseline until the corresponding changes are checked.

The [current root build and full axiom audit](data/current-root-check-20261020-0715.json)
passed with 24,019 project declarations and 17,550 theorems, including the
Section 3 proofs. All 98 proof-map labels and 580 declaration links resolve.

See [ASSUMPTIONS.md](ASSUMPTIONS.md) for named inputs and
[proof-map.json](proof-map.json) for declaration links.

## What the target actually says

For every target 0 < r < 1, the infimum of the sparse entropy over **all
measurable graphons** with triangle density at most r³ equals the balanced
SBM infimum. Above the transition the optimizer is constant; at the transition
both the constant and one balanced SBM occur; below it the balanced pair is
unique and all graphon optimizers have that form, up to null sets and relabeling.

[`MainStatement.lean`](SparseLowerTail/MainStatement.lean) encodes these claims
as the proposition `SparseLowerTail.MainTheorem`. **Defining this proposition
is not a proof of it.** There is no axiom asserting it. A conditional theorem constructs
an inhabitant from two explicitly named, still-unproved internal certificate inputs. The target includes the exact rational bracket for r*;
the decimal brackets for a* and b* are proved separately in `ThresholdDigits`.

The definitions use Lebesgue measure on [0,1] and its product measures, with
almost-everywhere symmetry and bounds. Graphons are not restricted to block
models. `IsBalanced` uses a measurable partition of mass one half. Its
integral formulas and equivalence to measure-preserving pullbacks are proved;
the latter uses the explicit classical CDF transform in `lem:relabelB`.

[Proof-simplification notes](../docs/PROOF-SIMPLIFICATIONS.md) record shorter
arguments separately for future manuscript revisions.

## Completed proof components

- **Discrete variational comparison (`lem:discrete`), both parts:**
  [DiscreteComparison.lean](SparseLowerTail/Section03/DiscreteComparison.lean)
  proves convergence of the normalized finite minimum for every sequence
  n → ∞ and p → 0. This includes finite minimum attainment, the exact step
  formulas (`s3:step`), clipping, the finite lower bound, and recovery vectors
  with eventual feasibility for every large n. The recovery proof uses balanced
  copies of the finite colors. [Build and 70 declaration audits](data/discrete-comparison-check.json) passed.
  The latest `lem:existence` and `lem:lsc` were also
  [reviewed with 12 declaration audits](data/section02-variational-review-20261020.json).

- **Triangle decorrelation (`lem:decorrelation`):**
  [Decorrelation.lean](SparseLowerTail/Section03/Decorrelation.lean) proves the
  revealed-edge selection and conditional product-error bound using the two
  cited generic KS23 inputs. The actual triangle hypergraph, counts, codegrees,
  conditional laws, sparse threshold and energy algebra are proved here.
  [Build and 36 declaration audits](data/decorrelation-check.json) passed.

- **Cut concentration and step kernels (`lem:cutconc`, `lem:stepcut`):**
  [BernoulliConcentration.lean](SparseLowerTail/Section03/BernoulliConcentration.lean)
  proves the exponential moments, signed tails and finite union bound with the
  paper's exact constant. [StepMatrixCut.lean](SparseLowerTail/Section03/StepMatrixCut.lean)
  proves matrix–graphon cut-norm equality, the interval-cell masses, binary
  maximizers and invariance under any measure-preserving map. The target build
  and [36 declaration audits](data/cut-concentration-check.json) passed.

- **Harris conditioning (`lem:harris`):** [HarrisConditioning.lean](SparseLowerTail/Section03/HarrisConditioning.lean)
  proves increasing-event domination, revealed conditional sections and the
  pinned-coordinate bound, using the cited Harris inequality as an explicit
  hypothesis. It also proves hypergraph lower-tail events decrease under edge
  deletion. [Target build and 19 declaration audits](data/harris-conditioning-check.json) passed.

- **Conditional entropy (`lem:entropy`), both finite-law parts:**
  [ConditionedProductEntropy.lean](SparseLowerTail/Section03/ConditionedProductEntropy.lean)
  combines the actual conditional laws, entropy chain rule, product-marginal
  decomposition, Bernoulli costs and conditioning cost. It also proves probability
  and null-event transfer for these conditional laws. [Target build and all 30 declaration audits](data/conditioned-product-entropy-check.json) passed.
  The edge-coordinate identification is an application in `thm:reduction`.

- **Sparse Bernoulli entropy (`lem:fp`):** [SparseEntropy.lean](SparseLowerTail/Section03/SparseEntropy.lean)
  proves the full uniform bound, including both endpoints, using the checked
  Bregman integral remainder. [Build and three declaration audits](data/sparse-entropy-check.json) passed.

- **Section 3 near-minimizer stability (`lem:stability`):** the limiting-minimizer
  argument and the uniform proximity theorem with a genuine measure-preserving
  bijection are proved in [NearMinimizers.lean](SparseLowerTail/Section03/NearMinimizers.lean).
  The target build and both declaration audits passed; only the existing four
  classical inputs are used. [Verification record](data/near-minimizers-check.json).

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
| Transfer step in `prop:smalldata` | [`ExternalReduction.lean`](SparseLowerTail/Section07/ExternalReduction.lean) | Given the explicitly assumed KP26 reduction and a supporting balanced penalized minimizer, prove constrained global optimality and its value. The supporting range is now proved in `SmallData.lean`; equality rigidity remains separate. |

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

## Further completed graphon and numerical components

- **`lem:digits`:** [`ThresholdDigits.lean`](SparseLowerTail/Section04/ThresholdDigits.lean)
  proves the two strict sign tests and all printed intervals for a*, b*, μ*, r*.
  [`threshold_digits`](SparseLowerTail/Section04/ThresholdDigits.lean) applies
  to the actual variational threshold. Rational proposals are generated by
  [`generate_threshold_digits.py`](tools/generate_threshold_digits.py); Lean
  checks the bounds using proved logarithm/exponential Taylor estimates and
  exact rational arithmetic. Regenerate from `lean/` with
  `python3 tools/generate_threshold_digits.py`, then build and audit. The
  generator's numerical proposals are not trusted premises.
- **`lem:scaling`, `lem:truncation`, `s3:rescale`:**
  [`Rescaling.lean`](SparseLowerTail/Section04/Rescaling.lean) constructs bounded
  nonnegative kernels, proves their integrability, scaling and truncation facts,
  then derives the actual normalized first variation on one- and two-sided
  intervals. [`KernelVariational.lean`](SparseLowerTail/Section04/KernelVariational.lean)
  proves equality of the extended kernel and graphon infima.
- **`s8:expect`:** [`CertificateExpectation.lean`](SparseLowerTail/Section08/CertificateExpectation.lean)
  proves the certificate expectation formula under the paper's stated lower
  bound, Euler–Lagrange equation, and triangle-density hypotheses. The Fubini,
  integrability, and cyclic-symmetry facts are proved in
  [`GraphonIntegration.lean`](SparseLowerTail/Section08/GraphonIntegration.lean).
  [`MinimizerExpectation.lean`](SparseLowerTail/Section08/MinimizerExpectation.lean)
  now discharges those analytic hypotheses for actual minimizers. Matching cost
  and edge data give zero expectation; conditional on certificate nonnegativity,
  this forces almost-everywhere vanishing. Certificate nonnegativity is still
  an internal obligation.
- **`lem:J`, `prop:bipodal`:** the modules `BipodalAlgebra`, `BipodalDefinitions`,
  `BipodalKernel`, and [`BipodalIntegral.lean`](SparseLowerTail/Section04/BipodalIntegral.lean)
  prove positivity of J by the paper's integral method and the resulting
  scalar stationary-system rigidity.
  [`BipodalGraphon.lean`](SparseLowerTail/Section04/BipodalGraphon.lean) handles
  arbitrary two-block partitions, including zero-mass blocks. Its minimizer
  interface discharges positivity, the Euler equation and multiplier positivity;
  [`BipodalMinimizers.lean`](SparseLowerTail/Section04/BipodalMinimizers.lean)
  now also discharges the vertex identity. Only the explicit classical sampling
  theorem remains as an input; the conclusion is in measurable-partition form.

## Remaining dependencies of the main theorem

The goal is to connect these components in the same order as the paper's proof.
An unchecked item is not supplied as an axiom.

- [x] Unrestricted minimizer existence and entropy lower semicontinuity,
      relative to the named classical dyadic approximation, compactness and
      counting inputs. Full cut-distance infrastructure is still partial.
- [x] Section 4: stationary branch, ray calculus, entropy geometric reduction,
      and activity of the graphon triangle constraint.
- [x] Section 4: unimodality, actual inverse branches, unique crossing, and the
      full balanced optimizer classification (`cor:Vbal`).
- [x] Certified threshold intervals (`lem:digits`), including a*, b*, μ*, r*.
- [ ] Threshold global inequality and equality classification (`thm:threshold`).
- [x] Sequential stability and openness (`prop:stability`, `cor:open`).
- [ ] Unconditional seed near the transition (`cor:seed`): the assembly is proved, but critical classification remains internal.
- [x] Complete small-target classification (`thm:smalltail`), relative to KP26,
      classical sampling and the positive Hilbert–Schmidt spectral theorem.
      The relabeling formulation additionally uses classical CDF transport.
- [x] Scaling, truncation, rescaled first variation, and the certificate
      expectation identity (`lem:scaling`, `lem:truncation`, `s3:rescale`, `s8:expect`).
- [x] Scalar two-block rigidity (`lem:J`, `prop:bipodal`).
- [x] Full insertion lemma, functional two-well theorem and local graphon
      rigidity (`lem:insertion`, `thm:twowell`, `thm:rigidity`).
- [x] Complete Euler–Lagrange proposition (`prop:euler`), including positive
      unique multiplier and the quantitative upper/lower bounds.
- [x] Sharp Bregman estimate, mean gap, and downward propagation
      (`lem:bregman`, `lem:meangap`, `lem:push`).
- [x] Boundary comparison (`lem:boundary`), value continuity, quantitative
      isolation, variance/entropy and Goodman bounds.
- [x] Vertex identity and two-block minimizer classification in partition
      form, relative only to classical inverse-transform sampling.
- [x] Four triangle patterns plus the balanced edge density force an actual
      equal-measure partition (`lem:patterns`(c), partition form).
- [x] Analytic bridge and sign estimates for the certificate (`lem:certcoef`).
- [ ] A Lean proof-producing version of the interval certificates, including
      the cover and family positivity checks (`prop:cover`, `prop:family`).
- [ ] Tie exclusion and equality-case rigidity (`lem:tieexclusion`).
- [x] Equivalence between balanced partitions and relabelings (`lem:relabelB`),
      relative to the explicit classical nonatomic CDF transform.
- [ ] Assemble the graphon-specific inputs and prove `MainTheorem`.

**Next mathematical bottleneck:** prove the global lower bound and its equality
conditions. The existing Python/Arb reports are computational evidence used by
the paper, but are not Lean proof terms. Loading their success flags would not
close the missing Lean obligations.

## Stable links to the manuscript

[`proof-map.json`](proof-map.json) records 73 stable LaTeX labels, their statement
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

### 2026-10-19 — numerical bounds and first-variation infrastructure

- Proved the complete printed threshold and parameter enclosures in Lean.
  Regenerating the threshold certificate gives identical content; the full
  project build checks every resulting numerical inequality.
- Completed scaling, truncation (including the extended infimum), and the
  rescaling first-variation lemma for actual bounded nonnegative kernels.
- Proved the actual graphon certificate expectation identity and the measure
  identities it uses.
- Completed the integral positivity lemma J and the scalar bipodal rigidity
  proposition. No internal J-positivity hypothesis remains in that proposition.
- **Still incomplete:** global graphon optimality and rigidity, the remaining
  graphon first-order/continuation arguments, and global positivity of the
  cover/family certificates. The numerical threshold bounds alone do not
  establish those positivity statements.

### 2026-10-19 — minimizer Euler equation and threshold reduction

- [`EulerLagrange.lean`](SparseLowerTail/Section04/EulerLagrange.lean) proves
  every part of `prop:euler` directly from minimizer optimality. The proof uses
  a toward-one perturbation for positivity and bounded exponential tilts for
  the first variation. These replace the manuscript's additive cutoff tests;
  neither route introduces an extra mathematical assumption.
- [`Bregman.lean`](SparseLowerTail/Section02/Bregman.lean),
  [`MeanGap.lean`](SparseLowerTail/Section02/MeanGap.lean), and
  [`Push.lean`](SparseLowerTail/Section02/Push.lean) prove the sharp entropy
  estimate, actual graphon variance bound, strict mean gap, and downward push.
- [`ThresholdReduction.lean`](SparseLowerTail/Section05/ThresholdReduction.lean)
  proves all conclusions of `thm:threshold` **conditional on the internal
  `CriticalClassification` proposition**. That proposition records `prop:critical`
  in measurable-partition form and remains unproved. The below-threshold
  improvement continues to be unconditional. No minimizer-existence assumption
  is needed for this reduction.
- Connected the arbitrary two-block graphon construction to scalar rigidity,
  and the actual minimizer Euler equation to the certificate expectation.
  The vertex condition, global positivity and zero-pattern rigidity remain
  necessary before these bridges give global classification.
- **Still incomplete:** `MainTheorem`, critical classification, vertex
  variation, global certificate positivity, and the remaining graphon
  existence/continuation arguments. Conditional deductions are not counted as
  proofs of their internal premises.

### 2026-10-19 — vertex variation, isolation and boundary comparison

- [`VertexReweighting.lean`](SparseLowerTail/Section04/VertexReweighting.lean)
  constructs the graphon vertex perturbation and proves its weighted integral
  formulas. [`VertexIdentity.lean`](SparseLowerTail/Section04/VertexIdentity.lean)
  proves every identity in `prop:vertex`. The single classical input is the
  exact inverse-transform sampling proposition recorded in `ASSUMPTIONS.md`.
- [`BipodalMinimizers.lean`](SparseLowerTail/Section04/BipodalMinimizers.lean)
  completes `cor:bipodalmin` in measurable-partition form, with no unproved
  internal first-order hypotheses. This classifies a minimizer already known
  to be two-block; it does not show all minimizers are two-block.
- [`ValueContinuity.lean`](SparseLowerTail/Section02/ValueContinuity.lean)
  proves `lem:existence`(b), directly from competitors and infima, without
  assuming that an unrestricted minimizer exists.
- [`TriangleL2.lean`](SparseLowerTail/Section02/TriangleL2.lean),
  [`Isolation.lean`](SparseLowerTail/Section02/Isolation.lean), and
  [`Goodman.lean`](SparseLowerTail/Section02/Goodman.lean) prove the actual
  integral bounds required by `lem:isolation`, `lem:FB1`, and `lem:goodman`.
- [`Boundary.lean`](SparseLowerTail/Section08/Boundary.lean) proves all of
  `lem:boundary`. A scaled-competitor argument proves both the endpoint cost
  equality and edge-density comparison, simplifying the manuscript's route by
  avoiding a separate minimizer-existence or value-continuity premise.
- [`Patterns.lean`](SparseLowerTail/Section02/Patterns.lean) recovers a
  measurable partition from the four triangle patterns and forces equal block
  masses from the edge density. The certificate-to-partition deduction is now
  connected, but still explicitly requires the unproved global certificate
  nonnegativity/zero-set and matching-data statements.
- **Still incomplete:** unrestricted minimizer existence, critical global
  classification, local rigidity/openness/seed, supporting penalized range,
  global cover/family certificates, relabeling equivalence, and final assembly.

- The same milestone also completes the sharp support bound (`lem:support`)
  and the parameter identities and bounds (`cor:identities`) in
  [`SupportBounds.lean`](SparseLowerTail/Section05/SupportBounds.lean), relative
  only to classical sampling. The cell interface turns a proved upper bound
  on Q into the support lower bound needed by the cover; it does not assert
  any unverified cell bound. The parity lemma is proved in partition form.

### 2026-10-19 — existence, triangle-law relaxation and penalized calculus

- [Existence.lean](SparseLowerTail/Section02/Existence.lean) proves attainment
  over unrestricted graphons. The actual finite-block Jensen, entropy L¹
  continuity and cut lower-semicontinuity proofs are in the adjacent Section02
  modules. Three exact classical inputs are recorded in `ASSUMPTIONS.md`.
- [RelabelBalanced.lean](SparseLowerTail/Section02/RelabelBalanced.lean)
  proves full partition/pullback equivalence using a constructed piecewise CDF.
  [CutDistance.lean](SparseLowerTail/Section02/CutDistance.lean) defines the
  actual bijective-relabeling infimum and selects converging representatives.
- [MinimizerLimits.lean](SparseLowerTail/Section05/MinimizerLimits.lean)
  proves minimizer, cost, mean and multiplier convergence under cut-distance
  convergence. The critical left-limit conclusion still explicitly depends
  on the unproved `CriticalClassification`; it is not a completed premise.
- [CriticalRegion.lean](SparseLowerTail/Section05/CriticalRegion.lean) proves
  every part of `lem:region`, including the numerical bounds and compactness.
  The actual triangle pushforward law, all permutation symmetries, Hoeffding
  decomposition and all T1–T5 conditions are proved in `TriangleLaw`,
  `TriangleLawSymmetry`, `Hoeffding`, and `RelaxedLaw`. The vertex moment
  argument uses only the classical sampling input already recorded.
- [CoverCertificate.lean](SparseLowerTail/Section05/CoverCertificate.lean)
  proves full `lem:weakdual` for arbitrary relaxed laws, including integrability,
  exclusion and the measure-one zero set. [CertificateConcavity.lean](SparseLowerTail/Section05/CertificateConcavity.lean)
  proves the exact mixing identity and finite-vertex interpolation. These
  results do not assume or prove the still-pending numerical positivity checks.
- Section07 `PenalizedScalar`, `ConstantRootCalculus`, `PenalizedGap`, `Fold`
  and `PenalizedHessian` prove `lem:stationary`, `lem:tie`, and `lem:fold`.
  The Hessian condition follows from actual line variations at a minimum;
  numerical sign tests use Lean proofs, not imported Python success flags.
- **Still incomplete:** global cover/family positivity, critical classification,
  local rigidity and continuation inputs, the full supporting penalized range,
  and assembly of `MainTheorem`. Classical inputs remain hypotheses, and
  internal conditional results remain distinguished from completed proofs.

### 2026-10-19 — critical assembly and unique penalized crossing

- `SingleCrossing` and `PenalizedCrossing` prove `lem:zc` with no internal
  transversality or numerical hypotheses: the unique crossing lies below
  1/1000 and the gap signs hold through the fold endpoint.
- `FiniteCover` proves the convex-cell argument in `cor:cover`; `CriticalAssembly`
  connects it to unrestricted minimizer existence and actual triangle-law
  patterns, yielding critical classification **conditional on the remaining
  cover and apex certificate obligations**. These are own-paper obligations,
  not permitted external inputs. No completed critical classification is claimed.
- Approximate completion estimate: **25% of total effort (20–30% range)**.
  This is a subjective planning estimate, not theorem coverage or mathematical
  certainty. The global certificate and local rigidity work remains substantial.
- Gaps and potential manuscript issues are tracked in [PROOF-ISSUES.md](PROOF-ISSUES.md).

Validation for this checkpoint: full root build passed (3215 jobs); axiom audit
passed for 1909 project declarations (including generated/private declarations),
allowing only `propext`, `Classical.choice`, and `Quot.sound`. All 66 stable-label
entries and 274 declaration links resolve; manuscript fingerprints and six map
tests pass. These counts are not a percentage of mathematical completion.

### 2026-10-19 — insertion, two wells and the penalized supporting range

- `Section06/InsertionLemma.lean` proves all of `lem:insertion`: construct an
  actual inserted graphon, compute entropy/edge/triangle polynomials, take the
  constrained one-sided variation, and obtain global minimality of almost
  every row. Null-set representatives are handled explicitly. The only input
  is the recorded classical inverse-transform sampling theorem.
- `Section06/TwoWellGrowth.lean` proves scalar two-well quadratic growth on
  the whole unit square. Boundary points and the diagonal critical point are
  excluded; strict Hessian positivity and compactness give a uniform constant.
  Functional coercivity and local graphon rigidity are still in progress.
- `Section07/PenalizedPhase.lean` and `PenalizedValue.lean` prove `prop:pen`,
  including the actual attained infimum and all phase values. `SmallData.lean`
  proves `lem:order` and `prop:smalldata` relative to the explicit KP26 input.
  This establishes the entire supported range, not only a conditional transfer
  at an unspecified supporting point. It does not prove `thm:smalltail` rigidity.
- `Section07/PenalizedQuadratic.lean` proves `lem:penalized` for every mean-zero
  L² function, using actual vertex variations and centered truncations.
- `Section02/CutDistanceIdentities.lean` proves the pseudometric identities;
  its general measure-preserving pullback result has the precisely recorded
  classical L¹ approximation input.

No mathematical error in the manuscript has been established in this checkpoint.
[PROOF-ISSUES.md](PROOF-ISSUES.md) lists the unresolved formal obligations.
The effort estimate remains about **25% (20–30%)**; remaining certificate and
rigidity proofs carry substantial work, so declaration counts are not coverage.

### 2026-10-19 — complete two-well theorem and recorded shorter proofs

`TwoWellRows.lean` now proves all of `thm:twowell` for actual measurable
profiles. `WeightedCut.lean` proves the sharp cut test bound by two positive-set
selections. `RowStability`, `RowPartition`, `UniformApproximation` and
`BlockBalance` prove Steps 1–3 of local rigidity, including an actual measurable
partition and the uniform graphon/mass estimates. Exact row identification
and final sequence assembly are still required.

`DegreeBounds.lean` proves the degree estimates using a direct positive-part
test. Both shorter arguments are written out in
[PROOF-SIMPLIFICATIONS.md](../docs/PROOF-SIMPLIFICATIONS.md), with stable labels,
complete hypotheses and Lean links for future manuscript revisions.

`CoverS1FirstBox` proves the actual first S1 vertex certificate is >3 on
[0,1/1024]³ in logarithmic coordinates. `CoverS1Tail` proves it is >0.01 on
[8,6743/512]³. These are genuine subdomain proofs, not a full-domain certificate.
The generators produce rational proofs checked by Lean; numerical proposals
are not trusted assumptions. No new mathematical error has been established.

`RowRigidity.lean` also proves local stationary-row uniqueness using direct
log monotonicity and a positive quadratic form. The full shorter proof is
recorded as PS-003 in the companion note. Final sequence/bipodal assembly is
still separate; this checkpoint does not claim `thm:rigidity` in full.

### 2026-10-19 — complete local rigidity; spectral estimates; larger S1 regions

`Section06/LocalRigidity.lean` now proves the full `thm:rigidity` for unrestricted
graphon minimizers, relative only to classical inverse-transform sampling.
The sequential approximation, exact row-class identification and bijective
relabeling transfer are all proved. No internal rigidity hypothesis remains.

`Section07/CenteredCubic.lean` completes the kernel form of `lem:spectral`:
all graphon-specific trace, diagonal, degree, cubic and spectral-tail estimates
are proved. The generic Hilbert–Schmidt spectral expansion is an explicit
classical hypothesis, precisely described in ASSUMPTIONS.md. This development
uses concrete kernels, integrals and convergent spectral sums; it does not claim
that mathlib now has a general trace-class operator library.

`CoverS1Regions.lean` checks the full eight-leaf partition of [0,1/32]³,
proving Ψ>1/2 there. It also proves Ψ>1/100 on the sorted-domain region q₃≥8.
The complete 55,873-leaf search proposal is preserved for reproducibility in
`lean/data/s1-vertex0-subdivision-proposal.json`; it remains **untrusted**, is
not imported by Lean, and its unproved Taylor leaves do not count as verified.
Scalable checked Taylor evaluation remains necessary for full-domain S1.

The current effort estimate is **about 30%, with a 25–40% range**, not measured
statement coverage. Full cover/family certificates, small-target equality
rigidity, openness/seed and final main-theorem assembly remain. No mathematical
error has been established. Four complete shorter-proof arguments are recorded
in the companion note; the latest is the symmetric ±ε penalized variation.

### 2026-10-19 — stability and openness assembled

`Section06/Stability.lean` proves the manuscript sequential stability proposition
and openness of exact balanced classification among all graphons. The left seed
is proved conditional on `CriticalClassification`; its finite certificates are
still internal obligations. Compactness, dyadic approximation, triangle counting,
pullback approximation and sampling are the recorded classical inputs.

### 2026-10-19 — exact conditional main-theorem assembly

`Section08.mainTheorem_of_remaining_inputs` now constructs the existing
`MainTheorem` structure from the actual graphon continuation argument, relative
to three remaining internal propositions: critical classification, small-target
classification, and the pointwise intermediate certificate. No axiom asserts
these propositions. The complete tie-exclusion deduction is proved. The shorter
proof note now also gives a compact narrative of this final argument.

The spectral development additionally proves sign-block masses, residual
row/action estimates and the exact codegree expansion. A reusable rational
exponential endpoint checker passed generated checks at 0, 1, 6743/512 and 16;
its Python generator only proposes data, with all comparisons checked by Lean.
The remaining major proof obligations keep the effort estimate at about 30%
(25–40% range), despite completion of the final logical assembly.

### 2026-10-19 — full small-parameter bounds and row reduction

The complete `lem:smallparams` now compiles. Its scalar bounds hold uniformly
for 0 < z ≤ 8.36×10⁻⁵, and `SmallParameterErrors` instantiates every bound for
actual minimizers, including ε < 0.114, E_m < 0.003 and p₀ > 0.4987. No upper
bound on the diverging multiplier was assumed. `PenalizedUpper` directly proves
the needed z_c upper bound; it does not yet prove every displayed coexistence digit.

`RowMeans`, `ApproximateEuler` and `RowVertexBound` prove all of `lem:rowreduction`
for the actual eigenfunction sign blocks. `ScalarExclusion` proves `lem:scalar`
with its exact constants. Small-target exact block rigidity remains in progress.

`CertificateTail` proves all of `lem:certtail` and reduces the full family,
including its exact zero set, to an explicit internal compact certificate.
That finite certificate remains unfinished. `CoverS1TaylorLeaf` proves a full
Taylor2 box using checked expression reification, derivatives, endpoint
exponentials and remainder bounds. A sound dyadic interval evaluator is now
available to speed the remaining checks. Search proposals are still untrusted.

The companion shorter-proof document is maintained separately from the paper.
No mathematical error has been established; the missing formal certificates
and structural assembly continue to be recorded as gaps, not assumptions of
classical status. The effort estimate remains about 30% (25–40% uncertainty).

### 2026-10-19 — small-target theorem complete; two certificate inputs remain

`SmallTargetBipodal` derives actual bipodality from the spectral sign classes,
using certified row separation, the same-block cap and exact stationary-row
rigidity. `SmallTailAssembly.smallTarget_classification` proves both directions
of the balanced classification for every 0 < r ≤ r₋. Its relabeling wrapper
also compiles. The only inputs are the recorded KP26, sampling, spectral and
(for the wrapper) CDF theorems. This closes `prop:structural` and `thm:smalltail`.

`FamilyParameterRange` proves the needed [3.9,9.5] logarithmic parameter range.
`FiniteCertificateAssembly.mainTheorem_of_finite_certificates` reduces the main
theorem to only two internal inputs: critical classification via the cover/apex,
and the compact family certificate. Both numerical obligations remain unproved
in Lean; they must not be treated as classical assumptions.

The proof note now contains seven complete replacements, including the direct
small-tail row comparison. Cooperative review found no new mathematical gap.
`CoverTreeReplay` also proves a data-only subdivision checker sound: all leaf
boxes must exactly match separately proved table entries, and sorted-domain
normalization and midpoint coverage are justified at every node.

Updated subjective effort estimate: about **40% (30–55% range)**. This is not
a count of proved statements; the remaining numerical proof replay may dominate
runtime and development. Earlier dated estimates above describe earlier states.


### 2026-10-19 — full cover geometry and support; family interval bridge

The actual twelve-cell geometric cover now compiles in `CriticalCoverGeometry`,
including all 179 curved-boundary leaves and boundary points. `CoverSupportData`
proves the support and cutoff fields for all twelve exact cells and assembles
`VerifiedCertificateCover` from the remaining nonlinear positivity inputs.
These proofs are unconditional and use only the standard Lean foundations.

The family branch now has exact Phi/Hessian reification, local contact calculus,
finite-dimensional congruence and exponential diagonal scaling. The checked
`FamilyParameterCertificate.coefficient_contains` converts an L interval,
certified exponential endpoint enclosures, and rational interval calculations
into bounds on the actual seven coefficient combinations. These bridges do
not yet prove the numerical margins on the complete compact domain.

The first S1 replay batch (128 leaves) passed; a full 15,280-leaf replay is in
progress and is not imported into the release root until checked. The earlier
seventeen-leaf Taylor slab is already an unconditional checked subregion.
The main theorem still has two internal certificate inputs. The effort estimate
remains about 40% (broad range 30–55%); leaf counts are not completion percentages.

### 2026-10-19 — full-parameter local AAA certificate

`FamilyAAACover.local_nonnegative_and_unique_zero` proves that the actual
family Phi is nonnegative, with equality only at the AAA contact, on the
closed logarithmic cube of radius 1/10 around that moving contact, for every
L in [3.9,9.5]. Five exact leaves cover [3.9,4.25], [4.25,4.6], [4.6,5.3],
[5.3,6.7], and [6.7,9.5]. Each exponential endpoint, coefficient enclosure,
and Hessian margin is checked by the Lean kernel. The actual Hessian is
connected to the numerical expression by `FamilyHessianExpr.entry_eval`.
Factoring q²−4q+2 as (q−2)²−2 gives tighter interval bounds without changing
the Hessian. See PS-008 in the simplification notes for the argument.

Reproduce the source with `python3 tools/generate_family_aaa_cover.py` from
this directory, then `lake build SparseLowerTail.Section08.FamilyAAACover`.
Python only proposes rational data; all proof obligations are checked in Lean.
The main theorem still needs the two internal certificate inputs. In
particular, the mixed contact and exterior compact-domain certificate remain.
The effort estimate remains about 40% (30–55% uncertainty).

**Resource correction:** bulk S1 replay is stopped at the user's request to
limit storage. Earlier entries describing it as running are historical.
No parallel agents or bulk replay jobs are used for this milestone.

Validation: full root build passed (3373 jobs); axiom audit passed for 8811
project declarations / 5445 theorems with only `propext`, `Classical.choice`,
and `Quot.sound`. All 86 mapped manuscript labels are unchanged; 371 Lean
links resolve, and all six mapping tests pass. Regeneration reproduces the
checked AAA source byte-for-byte.

Next numerical issue: a diagnostic with the factored raw Hessian and a
midpoint rational shear still gives an inconclusive interval margin on the
whole radius-0.1 mixed-contact box near L=3.9, even at parameter width 0.001.
This negative lower bound is inconclusive; it supplies neither a counterexample
nor a proved failure of positive definiteness. Spatial subdivision or a stronger algebraic bound is
needed; the AAA proof must not be extrapolated to ABB. No bulk job was started.

### 2026-10-19 — common apex determinant and all six exact tangencies

`ApexTangencyDeterminant` checks the sixteen entries of the actual tangency
matrix and encloses its determinant in
[5186330326774856, 5186330397267159] / 2^60, approximately
[0.004498424486, 0.004498424548]. This positive enclosure removes the
invertibility hypothesis. The nine primitive bounds follow from proved
critical digits and endpoint logarithm bounds.

`ApexFanTangency` defines the exact coefficients for F1–F6 from the published
fixed rational slots and Cramer's rule. It proves uniqueness of the four
corrections, preservation of every fixed slot, and zero value and gradient
at both actual logarithmic contacts. The coefficient data generator reads
`data/cover.json`; null slots are placeholders only until the exact solve.
The added proof-map anchor `s5:tangency` records the logarithmic-coordinate
scope explicitly. This follows the Appendix's coordinate convention.

Each costly symbolic matrix entry is interval-checked once; `MatrixInterval4`
then checks the determinant from the sixteen small interval bounds. This
reduces repeated symbolic evaluation and avoids bulk replay. The full main
theorem still needs critical/family global certificates; neither their
positivity nor their exact zero sets follows from tangency alone. No new
mathematical error was established. Effort estimate remains about 40%
(30–55% uncertainty), not measured theorem coverage.

Validation: full root build passed (3387 jobs). Axiom audit passed for
9181 project declarations / 5728 theorems, using only `propext`,
`Classical.choice`, and `Quot.sound`. All 87 manuscript anchors are unchanged,
377 declaration links resolve, and all six mapping tests pass. Regenerating
`CoverCoefficientData.lean` reproduces its source byte-for-byte. The local
build directory is about 767 MiB; bulk replay remains stopped.


### 2026-10-19 — all twelve apex contact neighborhoods

[`ApexFanLocal.lean`](SparseLowerTail/Section05/ApexFanLocal.lean),
`apexFan_local_nonneg_zero_iff`, proves local nonnegativity and a unique
contact zero for **each of F1–F6, at both AAA and ABB**, on the entire closed
logarithmic cube with the radius recorded in `data/cover.json`. The radii
have not been reduced to make verification easier.

The proof follows the paper's `lem:taylor` application:

1. [`ApexFanIntervals.lean`](SparseLowerTail/Section05/ApexFanIntervals.lean)
   encloses all 24 exactly solved coefficients using the already certified
   common determinant, actual right-hand sides, and Cramer's rule. The remaining
   coefficient slots retain their published rational values.
2. [`ApexTaylorLocal.lean`](SparseLowerTail/Section05/ApexTaylorLocal.lean)
   proves the actual directional third derivative and the local Taylor argument.
   It derives positivity from a center Hessian lower bound and uniform absolute
   bounds on all 27 third partials throughout the stated cube.
3. [`ApexTaylorIntervals.lean`](SparseLowerTail/Section05/ApexTaylorIntervals.lean)
   turns these into exact integer interval obligations. A rational congruence
   certifies positivity of the symmetric center Hessian minus `ell * I`;
   the third-partial bounds satisfy `radius * S3 < 3 * ell`.
4. The twelve files in [`ApexLocalReplay/`](SparseLowerTail/Section05/ApexLocalReplay/)
   check those obligations with `decide +kernel`, certified exponential endpoint
   bounds, and the actual critical constants and fan coefficients. The final
   statements require only membership in the contact cube.

The Taylor formalization proves the consequence needed here for the actual
apex expression. It does not claim the full generic C³ lemma or every displayed
quantitative inequality in `lem:taylor`. The proof map records that distinction.
No new manuscript error was identified. The complete critical cover and
compact intermediate family remain internal proof obligations; **the main
theorem is still incomplete**. These twelve neighborhoods do not certify
positivity on their complements.

Reproduce the proposed source data from `lean/`:

```bash
python3 tools/generate_apex_fan_intervals.py
python3 tools/propose_apex_local_boxes.py
python3 tools/generate_apex_local_taylor.py
lake build SparseLowerTail.Section05.ApexFanLocal
```

The first command reuses the saved right-hand-side proposals. To regenerate
those proposals from the expressions instead, run
`lake env lean tools/ProposeApexFanRhs.lean > /tmp/apex-rhs.txt`, then pass
`/tmp/apex-rhs.txt` to `generate_apex_fan_intervals.py`. These scripts are
untrusted proposal generators: every number used by the theorems is checked
again by Lean. No Python floating-point eigenvalue estimate is a proof premise.
The Python diagnostics can fail to certify a whole-box Hessian even when the
Taylor certificate succeeds; this is not evidence of a mathematical error.

All fourteen generated Lean files reproduce byte for byte from the saved
proposals. Local neighborhood builds were run sequentially to limit resource
use; the large unfinished S1 replay was not resumed.

Validation for this milestone: full root build passed (3406 jobs); the axiom
audit checked 9798 project declarations / 6177 theorems and allowed only
`propext`, `Classical.choice`, and `Quot.sound`. All 88 stable manuscript
anchors remain unchanged, all 384 declaration links resolve, and the six
mapping tests pass. Local build artifacts total about 793 MiB, compared with
about 767 MiB before this milestone.


### 2026-10-19 — shared checker for all nonapex jobs

[`CoverJobIntervals.lean`](SparseLowerTail/Section05/CoverJobIntervals.lean)
provides actual environment enclosures for all 36 nonapex jobs. Fan vertices
use `apexFanTheta`, including the exact four solved coefficients; the stored
zero placeholders are never substituted for those coefficients. Mean and cost
are the exact rational vertex coordinates, and the multiplier enclosure is
proved using `(1 - cost - mean) / criticalTriangle`.

[`CoverJobTaylorBox.lean`](SparseLowerTail/Section05/CoverJobTaylorBox.lean)
proves one reusable Taylor-leaf theorem for all 36 jobs. It shares the symbolic
expression and derivatives through `CoverGenericEnvironment`,
`CoverGenericCalculus`, and `CoverGenericTaylor`. The historical
`S1TaylorBoxData` type is reused only for its box geometry and exponential
endpoint data; the theorem itself uses each requested job's actual parameters.

[`CoverNearOne.lean`](SparseLowerTail/Section05/CoverNearOne.lean) kernel-checks
all 36 jobs on `[0,1/512]^3` in logarithmic coordinates. Regenerate it with
`python3 tools/generate_cover_near_one.py`. This is a checked starting region,
not a completed cover of any job's full domain.

**Precision finding before bulk apex replay:**
`python3 tools/diagnose_apex_precision.py` reproduces the untrusted diagnostic
in `data/apex-exterior-precision-diagnostic.json`. At a single rational sample
two published ABB radii away in the first coordinate, the current direct
interval evaluation straddles zero for F1–F5. For example, F1 gives roughly
[-1.52e-7, 1.60e-7]. This does not show that the function is negative, nor does
it contradict the proved local certificates. It shows that these enclosures
cannot certify the sampled points using direct evaluation alone. Subdivision
of the spatial box cannot eliminate the uncertainty in the fixed coefficients.
Next work should tighten the critical-constant/solved-coefficient bounds or
preserve tangency cancellations in the exterior evaluator before bulk replay.

Validation: full root build passed (3412 jobs). The axiom audit checked
9914 declarations / 6271 theorems with only the three standard axioms;
88 manuscript anchors and 388 declaration links pass, as do all six mapping
tests. No bulk replay or additional agent was started.


### 2026-10-19 — refined crossing bracket

[`RefinedThresholdDigits.lean`](SparseLowerTail/Section04/RefinedThresholdDigits.lean)
proves that the actual unique crossing parameter lies strictly between
`5013857763720581 / 250000000000000000` and
`20055431054882327 / 1000000000000000000`: a bracket of width `3e-18`.
The proof rechecks the opposite endpoint signs and uses the already proved
crossing classification. It also proves tighter branch ranges on this entire
bracket: widths approximately `3.09e-18` for a, `2.69e-17` for b, and
`1.22e-15` for the multiplier.

Regenerate with `python3 tools/generate_refined_threshold_digits.py` from
`lean/`. Decimal bisection only proposes endpoints; Lean verifies all signs,
logarithm/exponential bounds and rational arithmetic. The existing printed
digit theorem and its source generator are preserved. This is the first step
toward removing the recorded apex interval-precision limitation; the refined
ranges still need to be propagated through the nine primitive constants,
common matrix and six coefficient vectors before an exterior replay benefits.

Validation: full root build passed (3413 jobs); audit passed for 9940 project
declarations / 6295 theorems using only the standard three axioms. All 88
manuscript anchors and 390 declaration links pass, along with six mapping
tests. Regeneration is byte-identical and leaves the original digit source
unchanged.


### 2026-10-19 — refined nine-constant apex environment

[`ApexRefinedPrimitives.lean`](SparseLowerTail/Section05/ApexRefinedPrimitives.lean)
proves enclosures for all nine actual primitives from the refined crossing:
`qa, qb, a, b, triangle, omega, multiplier, mean, cost`. It uses exact branch
logarithm identities and the exact critical balanced-pair cost/triangle
identities, so it does not re-round a and b to the older printed decimal bounds.
The interval widths are approximately 1.81e-16, 3.17e-17, 3.09e-18,
2.69e-17, 2.26e-18, 1.12e-16, 1.22e-15, 1.50e-17, and 3.85e-17,
respectively.

Regenerate with `python3 tools/generate_apex_refined_primitives.py` from
`lean/`. The accompanying JSON is proposal data; the Lean theorem establishes
containment of the actual constants. The existing coarse interval tables and
the twelve checked local certificates remain available. The refined matrix, right-hand-side and all 24 solved-coefficient enclosures
now also pass kernel checks in `ApexRefinedSystem.lean` and
`ApexRefinedFanIntervals.lean`. The largest solved-coefficient interval width
is below 4.77e-14. `ApexRefinedBoxIntervals.lean` connects these tables to
the same actual certificate and proves a generic interval-box positivity
implication. Full exterior coverage remains unfinished.

Regenerate the system tables with `python3 tools/generate_refined_apex_intervals.py`.
To independently repropose the matrix/RHS tables, first run
`lake env lean tools/ProposeRefinedApexSystem.lean > /tmp/apex-system.txt`,
then pass that file to the generator. The proposal calculation is not trusted.

`python3 tools/diagnose_apex_precision.py --refined` compares the same twelve
exterior samples used by the coarse diagnostic. All now have positive interval
lower bounds (smallest about 1.345e-9), with widths around 2e-14. This Python
diagnostic is not a Lean proof of any exterior region; it shows that the
previous constant-precision obstruction is removed at these samples.

Validation: root build passed (3417 jobs); axiom audit passed for 10065
project declarations / 6409 theorems, with only the standard three axioms.
All 88 manuscript anchors / 394 declaration links and six mapping tests pass.
Generated refined Lean sources reproduce byte-for-byte.

`ApexRefinedTaylorBox.lean` additionally proves the factored Taylor leaf rule
for all six actual apex fans using the refined intervals. This reuses the
shared endpoint/box geometry and actual first/second derivative identities.
Its numerical margin must still be discharged for every exterior leaf and
the leaves must be proved to cover the required domain.
Validation of the Taylor addition: root build 3418 jobs; axiom audit 10067
project declarations / 6410 theorems, using only the standard three axioms.

### Bouchet full S1 replay preparation

The untrusted S1 subdivision proposal and its generators are now versioned
for remote replay. `tools/run_s1_cluster.py` generates all leaves and exact
coverage, compiles a full-edge-cube theorem for S1's first parameter vertex,
and runs the standard axiom audit. The proposed workload is not yet a
completed proof. Its generated modules stay outside the public root until
the full build, audit and statement review pass. See `../hpc/README.md`.

### 2026-10-19 — full F1 apex proposal and checked replay entry points

`ApexContactBox.lean` proves an exact rational containment test from a
subdivision box to any of the twelve already proved contact neighborhoods.
`ApexCoverAssembly.lean` carries nonnegativity and the zero-to-contact
implication through coordinate sorting back to the full edge cube, with the
four required triangle patterns. The full sorted-domain premise is still
an internal verification obligation.

`tools/propose_apex_cover.py` now produces a complete F1 proposal on the
published domain: 31,180 exterior Taylor leaves, 14 AAA contact leaves and
69 ABB contact leaves (62,525 tree nodes). The proposal and its success flag
are untrusted. It is saved in `data/apex-f1-subdivision-proposal.json`.
The bounded search can save and resume its frontier; no incomplete proposal
is accepted by the replay parser.

`tools/generate_apex_replay.py` writes exact box data, exponential endpoint
proofs, numerical leaf inequalities, geometric coverage proofs and the final
whole-cube implication. Its `--smoke` mode deliberately omits a global theorem.
Five representative F1 leaves, including exterior boxes adjacent to both
contact types, are checked in `ApexReplay/F1Smoke`. The full-cube wrapper was
separately type-checked with an explicit ordered-domain hypothesis; this
checks the wrapper, not that hypothesis. The full replay belongs on Bouchet
through `tools/run_apex_cluster.py`, followed by the unchanged axiom audit.

Validation: full root build passed (3428 jobs); audit passed for 10,171 project
declarations / 6,485 theorems, using only `propext`, `Classical.choice` and
`Quot.sound`. Manuscript/map checks and all six mapping tests pass. No new
manuscript error was established. The global critical and intermediate-family
certificates remain unfinished; effort estimate remains roughly 40–45%.

`criticalApexCertificate_of_ordered` now also discharges the support cutoff
and multiplier sign, connecting a complete fan replay directly to the apex
hypothesis in `criticalClassification_of_verifiedCover`. Its sorted-domain
premise remains unproved until a full replay succeeds.
Final validation after the support bridge: root build 3428 jobs; audit 10,172
project declarations / 6,486 theorems, standard three axioms only; 88 labels
and 404 distinct declaration links pass.

### 2026-10-19 — full ABB proposal and checked scaled-Hessian replay

A complete **untrusted** subdivision now covers L in [3.9,9.5] and all three
ABB offsets in [-1/10,1/10]: 216,903 nodes and 108,452 leaves, no frontier.
The compressed proposal is
[`data/family-abb-subdivision-proposal.json.gz`](data/family-abb-subdivision-proposal.json.gz).
It occupies about 7.2 MB; the much larger generated Lean replay has not been
created on the desktop. A separate Python consistency pass reconstructed every
split, moving-contact enclosure and rational congruence margin. Its
[report](data/family-abb-proposal-consistency.json) is **not a Lean proof**.

New kernel-checked components:

- `ExpEndpoints`: exp(-q) certificates now work on [-16,16], with the same
  proved Taylor remainder and exact rational comparisons. Negative coordinates
  are needed for the full local ABB cube near the large-L endpoint.
- `FamilyScaledIntervals`: enclosures of the actual exponentially scaled
  Hessian, including separately checked half-sum exponential endpoints and
  the transfer from positive congruence margins to the actual Hessian form.
- `Numerics/BoxReplay`: exact midpoint-tree coverage in arbitrary dimension;
  missing leaf indices are rejected, and every root-box point reaches a
  proved leaf. The family uses four dimensions (L and three offsets).
- `FamilyOffsetCover`: checks that each offset box encloses the moving ABB
  contact, then assembles local nonnegativity and the unique contact zero
  **conditional on the complete checked leaf table and coverage tree**.
- `FamilyScaledSmoke`: two selected boxes pass endpoint, coefficient,
  congruence-margin and moving-contact-enclosure checks. The second has
  L in [9.49,9.5] and negative small logarithmic coordinates. These two boxes
  are not the full local certificate.

Reproduce the small checked milestone from `lean/`:

```sh
python3 tools/generate_family_scaled_smoke.py
lake build
lake env lean Audit.lean
```

Reconstruct the complete proposal and its separate consistency check:

```sh
python3 tools/propose_family_abb_cover.py --scaled --budget 250000 --seconds 180 --output /tmp/family-abb.json.gz
python3 tools/check_family_abb_proposal.py data/family-abb-subdivision-proposal.json.gz --report /tmp/family-abb-check.json
```

The search may be resumed with `--resume`; its budget is the total node count.
Floating-point arithmetic only proposes the rational change of basis. All
accepted formal leaves must pass Lean's integer arithmetic and analytic bridge.
The experimental `--factored` search is untrusted and has no Lean replay yet.

Validation: full root build **3,432 jobs**, axiom audit **10,486 project
declarations / 6,673 theorems**, with only `propext`, `Classical.choice`, and
`Quot.sound`. The stable map checks pass for 88 labels and 413 declaration links, and all
six map tests pass. Full ABB replay, all critical cover jobs, and the exterior
family remain unfinished. The effort estimate remains about **40–45%**, not a count
of declarations or proposed boxes.

### 2026-10-19 — shared ABB replay and bounded build driver

The full ABB generator now shares the **93 distinct parameter intervals** and
reuses exponential endpoint proofs. Only a small smoke target is generated
on the desktop: 21 actual proposal leaves, one complete subdivision subtree,
and the final leaf at the large-L end. Its leaf margins, moving-contact boxes,
lookup table and exact coverage all compile. This checks the generation and
assembly path, **not the full 108,452-leaf neighborhood**.

`tools/build_bounded.py` builds project modules in import order, with at most
two Lake processes by default. It waits for each dependency to succeed, stops
scheduling after a failure, and records per-module logs. The 97-module smoke
closure passed with two workers in about 112 seconds, including cached imports.
This is not an estimate for the full workload.

```sh
python3 tools/generate_family_abb_replay.py data/family-abb-subdivision-proposal.json.gz --smoke
python3 tools/build_bounded.py SparseLowerTail.Section08.FamilyABBReplay.Smoke.CheckedSubtree --logs /tmp/abb-smoke --workers 2
```

For the full cloud workload, `tools/run_family_abb_cluster.py` generates every
leaf and coverage chunk, runs the bounded builder, and applies the unchanged
axiom audit to `FamilyABBReplay.Full.FullNeighborhood`. It reports success only
after both checks pass. The `familyabb` workload of the staged Bouchet runner
uses two build workers with two Lean threads each. Full generated sources are
exported only on success. See `hpc/README.md` for deployment state.

Validation of this milestone: root build **3,441 jobs**, axiom audit
**11,195 project declarations / 7,230 theorems**, only the standard three axioms;
88 manuscript labels and 418 declaration links pass, with six map tests.
The generator reproduces the checked smoke source byte-for-byte.

Full ABB deployment: Yale job **30052586**, source `7bbeae8`, is running on
a separate node with four CPUs and bounded build concurrency. Its full proof
and audit remain pending; deployment details are recorded under `hpc/`.

### 2026-10-19 — checked parameter calculus for the exterior family bound

`FamilyParameterCalculus` now proves the actual L-derivative chain for all seven
coefficients. The primitive curve is `(exp(-L), L, b(exp(-L)))`; its velocity is
rational in the same variables. `RationalExprCalculus` proves the chain rule
once for every rational expression, and successful interval evaluation proves
all denominator nonvanishing obligations. No numerical derivative oracle or
new hypothesis about our coefficients is introduced.

`TaylorParameter` proves the second-order Taylor expansion with an absolute
third-order remainder for a displacement of either sign. The lower-bound
variant retains `min(0,f''(center))*width²/2`, matching the signed quadratic
term in the paper's code. `FamilyParameterTaylor.phi_parameter_taylor_lower`
applies this result to the actual logarithmic certificate, combining the seven
coefficient contributions before taking the absolute remainder bound.

`FamilyParameterSmoke` kernel-checks **all seven coefficients through derivative
order three** (28 intervals) uniformly for L in [39/10,2503/640]. These are
bounds on actual derivatives. It is a diagnostic interval, not a full exterior
cover. To reproduce the untrusted numerical proposal, from `lean/` run:

```sh
lake env lean tools/FamilyParameterProposal.lean
lake build SparseLowerTail.Section08.FamilyParameterSmoke
```

The proposed integers are independently checked by `decide +kernel`. The
full checked root build has **3,447 jobs**; the axiom audit passes for
**11,319 project declarations / 7,324 theorems**, with only `propext`,
`Classical.choice`, and `Quot.sound`. All 88 mapped manuscript statements are
unchanged; 425 declaration links and all six map tests pass.

Remaining work: parameter variation of q-gradients, numerical assembly of the
exterior Taylor leaves, their complete cover, and the full critical certificate
jobs. The three Yale jobs were still running at the last scheduler check; no
full certificate success is claimed. No mathematical counterexample or new
manuscript error was found in this step. The effort estimate remains roughly
40–45%; additional helper theorems do not by themselves discharge a certificate.

### 2026-10-19 — gradient variation and analytic exterior-leaf assembly

`FamilyGradientParameter.gradientParameterDerivative_zero` identifies the
weighted coefficient expression with the actual q-gradient for each coordinate.
Its `gradient_parameter_variation` theorem gives the paper's L-error bound:
the center first derivative times the parameter width, plus a uniformly
bounded second derivative times half the width squared. Both signs of the
parameter displacement are covered.

`QuadraticAxisBounds` proves all three scalar choices in `compact_test`:

- The interval-safe bound, valid for any sign of the diagonal curvature.
- The unconstrained minimum when the diagonal curvature is positive.
- The interval-endpoint bound when a certified lower bound on the gradient
  magnitude places the stationary point outside the allowed interval.

`familyPhi_exterior_lower` assembles the actual center value, coordinate
gradients, signed diagonal Hessian lower bounds, and absolute cross-term
bounds along the segment. It permits any numerically certified choice of the
three scalar bounds. Thus the analytic exterior-leaf inequality is now proved;
its explicit scalar enclosure hypotheses still require checked numerical data.
**No complete exterior cover or final family certificate is claimed.**

Validation: root build **3,450 jobs**; axiom audit **11,344 project declarations /
7,346 theorems**, only the standard three axioms; stable map **88 labels / 430
Lean declarations**. The earlier manuscript snapshot and six map tests remain
unchanged. No manuscript counterexample or mathematical error was found.

Next work is to assemble the parameter-center and q-center interval data into
an executable exterior-leaf checker, check its numerical margins, and produce
a complete covered region. Full critical classification also remains open in
the formalization. These missing computations are internal obligations, not
allowed external assumptions.

### 2026-10-19 — first complete checked exterior Taylor leaf

The exterior leaf checker now takes finite numerical data all the way to an
actual uniform certificate bound:

- `FamilyWeightIntervals` checks the seven signed value and gradient weights
  from the three q-center exponential certificates.
- `FamilyTaylorData` checks the parameter center, the whole interval, derivative
  tables, and both directions of the parameter width. It derives the actual
  value lower bound and upper/lower gradient magnitude bounds.
- `FamilyExteriorLeaf.margin_le` combines those bounds with the whole-box
  Hessian intervals, coordinate radii, and any of the three quadratic choices.
  An accepted positive margin proves strict positivity everywhere in the box.

`FamilyExteriorSmoke` checks one complete box:
**L ∈ [39/10,2503/640], q₁,q₂,q₃ ∈ [99/100,101/100]**. Its rational margin is
**greater than 1/1000**, checked by the Lean kernel. All 21 additional center
coefficient/derivative intervals are checked independently of their proposal
program. This box lies away from the prescribed contacts. It verifies the
complete leaf pipeline, **not coverage of the whole exterior region**.

Reproduce from `lean/`:

```sh
python3 tools/generate_family_exterior_smoke.py
lake build SparseLowerTail.Section08.FamilyExteriorSmoke
```

The temporary `#eval` proposes interval endpoints only; every accepted equality
and inequality is checked with `decide +kernel`. Regeneration is byte-identical
(SHA256 `5297eae3e2f527ac6485c8544d0308a262796e16c76b99c3606b9e23e3599e46`).
No bulk replay or new dependency cache was created on the desktop.

Validation: root build **3,455 jobs**; axiom audit **11,565 project declarations /
7,482 theorems**, only `propext`, `Classical.choice`, and `Quot.sound`; all
**88 manuscript labels / 439 Lean declaration links** and six map tests pass.
No new manuscript gap or mathematical counterexample was found.

Remaining: generate and check a complete exterior subdivision, assemble it
with both contact neighborhoods, and discharge every critical cover/apex job.
The two internal hypotheses of the main theorem therefore remain unproved.
The rough effort estimate is still 40–45%, not a percentage of proposed boxes.
The next numerical search must reproduce the checked evaluator's arithmetic;
its proposals and a successful search flag cannot replace the coverage proof.

At the latest cloud check, the ABB bounded build had completed 255/7459 modules
with no failures reported. The scheduler marked S1, F1 and ABB running at
elapsed times 00:56:13, 00:56:13 and 00:25:16 respectively. An extra monitoring
step on the S1/F1 node could not start; this is not evidence that either batch
job finished or failed. No full cloud certificate is counted as checked yet.

### 2026-10-19 — complete exterior proposal and zero-preserving assembly

`FamilyCompactAssembly` proves that a certificate for sorted logarithmic
coordinates gives exactly `CompactFamilyCertificate`, including all zero
patterns and ties between coordinates. `FamilyCompactReplay` supplies the
common leaf property for positive Taylor boxes, local contact boxes, and
boxes disjoint from the sorted domain. Its final theorem converts a checked
finite table and subdivision into the required compact-family certificate.
The ABB local result is an explicit internal premise, still awaiting its full
remote replay; it has not been introduced as an external axiom.

The new search exports the actual Lean expression trees and shares only
identical subexpressions (1,568 DAG nodes). Exact dyadic arithmetic reproduces
all 49 derivative intervals and the baseline margin of the already checked
exterior sample. No floating-point acceptance criterion is used.

The saved proposal `data/family-exterior-subdivision-proposal.json.gz` covers
L in [39/10,19/2] and sorted q in [0,12]^3 with an exact midpoint tree:

| Leaf kind | Proposed count |
| --- | ---: |
| Positive Taylor | 44,776 |
| Disjoint from sorted domain | 11,057 |
| ABB contact | 4,096 |
| AAA contact | 4,717 |
| Total | 64,646 |

The tree has 129,291 nodes and no unresolved frontier. The separate Python
consistency traversal checks every split, box and acceptance, while sharing
the arithmetic evaluator with the search. It is therefore a consistency
check, **not an independent proof or a Lean verification**. The smallest
proposed Taylor margin is 347707219617049/75557863725914323419136000.
The SHA256 of the uncompressed proposal is
`48420ce188ba0e8993c3febf8b678c86552a43cb8fb94efbd973a5be785d7aa7`.

Reproduce from `lean/` after building the existing exterior sample:

```sh
python3 tools/export_family_expressions.py
python3 tools/propose_family_exterior_cover.py --budget 250000 --seconds 60 --output /tmp/family-exterior-proposal.json.gz
python3 tools/check_family_exterior_proposal.py data/family-exterior-subdivision-proposal.json.gz
lake build SparseLowerTail.Section08.FamilyCompactReplay
```

A time-limited search may leave a frontier; resume with `--resume` and the
same output path. Search completion is not proof completion. The full Lean
leaf generation/replay and the full ABB local proof are still required.
Critical classification also remains open. No new manuscript counterexample
has been found; the effort estimate remains 40–45%.

Validation: root build **3,457 jobs**; audit **11,605 declarations / 7,509
theorems**, only the three standard logical axioms; **88 manuscript labels /
448 declaration links** pass, as do five arithmetic-regression tests and six
manuscript-map tests. The complete Python proposal replay passes again.


### 2026-10-19 — generated exterior replay checks all leaf types

The actual proposal now generates Lean endpoint, parameter, derivative, leaf,
and coverage proofs with shared data. The small test has **14 actual leaves**:
ten Taylor, two ordered-empty, one AAA, and one ABB. It includes all three
quadratic choices and one complete ten-leaf subdivision subtree. All 16
generated modules compile. The contact and table conclusions explicitly
retain `FamilyABBLocal`; the ten Taylor positivity checks are unconditional.
This is not a completed full-domain replay.

From `lean/`:

```sh
python3 tools/generate_family_exterior_replay.py data/family-exterior-subdivision-proposal.json.gz
lake build SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.CheckedSubtree
```

The full generator uses `--full` and is intended for Yale. Its cluster runner
builds the full conditional compact certificate and applies the unchanged
axiom audit. A separate proved ABB neighborhood is still needed to remove
that internal premise. The new Slurm runner checkpoints completed project
artifacts on a controlled timeout. See `hpc/README.md` for deployment status.

The smoke test exposed two source-generation bugs (a missing namespace import
and Lean structure-field indentation). Both are fixed; neither was a failed
mathematical inequality. Six parser tests also reject duplicate, missing,
misbounded and out-of-scope coverage data; they are not a formal proof.

Validation: root build **3,473 jobs**; audit **12,244 declarations / 8,043
theorems**, with only the three standard logical axioms; **88 labels / 453
Lean declaration links** pass. All eleven exterior arithmetic/parser tests
and six manuscript-map tests pass. Regenerating all sixteen smoke modules
and their manifest is byte-identical. The full theorem remains conditional
on the two internal certificates; the effort estimate stays roughly 40–45%.

The full exterior workload is now submitted on Yale as **30056868**, from
checked commit `a9491f2`, with four CPUs and 64 GiB. Both uploaded checksums
matched. The job must finish its complete Lean build and axiom audit before
any full exterior result is counted; its ABB premise remains separate.
The scheduler subsequently reported the new job RUNNING at 13 seconds,
with the source hash accepted and dependency-cache restoration underway.
The original S1, F1 and ABB jobs were still RUNNING at 1h26m58s, 1h26m58s
and 56m01s respectively. No full cloud success is asserted.


### 2026-10-19 — all-job critical assembly and wider endpoints

`CoverJobsAssembly.criticalClassification_of_ordered_jobs` (declaration
namespace `SparseLowerTail.Section05`) connects the exact **36 nonapex jobs
and six apex fans** to critical classification. It checks the actual vertex
inventory, including which cells contain the exceptional apex, then applies
the proved cover, support and zero-pattern arguments. The job results remain
explicit internal premises. This does not assert that those jobs have passed.

`CoverRefinedJobIntervals` and `CoverRefinedJobTaylorBox` provide the sharper
proved critical constants and solved fan coefficients to every nonapex job.
The mathematical certificates are unchanged. In particular, missing fan
coefficient slots never become the table's zero placeholders.

A genuine implementation limitation was found: B1 and B2 require logarithmic
cutoffs 9009/512 and 4629/256, exceeding the endpoint checker's former limit 16.
A proved thirty-two-scale alternative now handles [-32,32]. The old
sixteen-scale data remain accepted unchanged. `WideExpSmoke` kernel-checks
both B-cell cutoffs and -32, 0, 16, 32. `all_cell_cutoffs_in_wide_range` checks
that all twelve actual cutoffs fit the new range. This is a repaired verifier
restriction, not a counterexample to the manuscript.

Validation: the complete 336-module project dependency closure passed with
at most two build workers. The axiom audit passed **12,299 declarations /
8,079 theorems**, with only the standard three logical axioms. All **88
labels / 463 declaration links** and the eleven exterior-regression and
six manuscript-map tests pass. The numerical job premises remain unproved;
the effort estimate is still roughly 40–45%.

The next step is to check the generic search evaluator against exported Lean
intervals for all 36 jobs, then generate and formally replay full subdivisions.
The raw input export is running separately and is not counted as a proof.

### 2026-10-19 — generic full-domain nonapex replay and concrete completion gates

The main README now records completed full-domain gates instead of treating the
subjective 40–45% effort estimate as a measured progress bar. Neither internal
certificate is discharged yet. Job submissions and search success do not count.

`tools/ExportCoverJobs.lean` exports the actual common value, three gradients,
nine Hessian entries, and the refined constants for all 36 nonapex jobs. A
structurally shared expression DAG has 1,149 nodes; Python reproduces all 36
Lean near-one reference intervals exactly. This is a regression check for the
**untrusted search**, not proof of full-domain positivity. The exporter
normalizes closed finite-table lookups before serialization: interpreted
nested finite-index evaluation had caused a severe performance bottleneck.

Two bounded searches completed on their entire prescribed domains:

| Job | Paper cell | Cutoff Q | Proposed leaves | Search time |
| --- | --- | --- | --- | --- |
| 0 | F1, first nonapex vertex | 3287/512 | 15,963 Taylor | 22.2 seconds |
| 35 | B2, last nonapex vertex | 4629/256 | 28,486 Taylor + 36 direct | 40.1 seconds |

The data are `data/cover-job-00-subdivision-proposal.json.gz` and
`data/cover-job-35-subdivision-proposal.json.gz`. Neither has an unresolved
frontier. **Neither is a completed formal certificate.**

`tools/generate_cover_job_replay.py --full` generates every margin proof,
finite table, exact subdivision coverage, and the actual full ordered-domain
positivity theorem for any indexed nonapex job. Default mode checks only a
small subset plus a complete small subtree. The direct positivity invocation
now explicitly supplies `edgeCoordinate q`; omitting it caused a costly
implicit-argument unification search. No theorem statement was weakened.

`tools/run_cover_job_cluster.py` requires the full generated target to build
and the unchanged axiom audit to pass before writing a success marker.
`hpc/bouchet-cover-job.sbatch` keeps the bulk replay on a CPU node, with bounded
workers and a resumable project-build checkpoint. The separate
`hpc/bouchet-certificate-search.sbatch` searches the remaining 36 nonapex and
five apex exterior jobs, at most two single-CPU tasks concurrently. Its outputs
are explicitly untrusted proposals; it does not claim proof success.

Reproduce the two searches and inspect the replay interface:

```sh
cd lean
python3 tools/export_cover_jobs.py
python3 tools/propose_cover_job.py --job 0 --seconds 45 --budget 100000 \
  --output data/cover-job-00-subdivision-proposal.json.gz
python3 tools/propose_cover_job.py --job 35 --seconds 45 --budget 100000 \
  --output data/cover-job-35-subdivision-proposal.json.gz
python3 tools/generate_cover_job_replay.py data/cover-job-00-subdivision-proposal.json.gz
# Full generation/build belongs on the cluster:
python3 tools/run_cover_job_cluster.py --job 0 --logs /path/to/logs
```

Full critical classification still requires all 36 nonapex and six apex
full-domain results. Full compact-family positivity still requires the ABB
and exterior replays. No new mathematical error in the paper was established.

Performance experiment: `CoverJobProgram` proves all thirteen symbolic output
identities for a 1,149-instruction shared-register program.
`CoverJobProgramTaylor.margin_eq_job` proves exact equality with the existing
margin, including diagonal square bounds. On one identical job-0 leaf,
separate single-thread Lean runs took 5.80 seconds for the register version
versus 3.69 seconds for the original expression evaluator (including startup).
This is not a broad benchmark. The full replay generator therefore retains
the original checker; the proved alternative is kept for reproducibility.
The fixed direct B2 leaves each compiled in 3.3 seconds after explicit
coordinate arguments and their three endpoint-bound conversions were supplied.

Validation for this milestone: full root build **3,492 jobs**; axiom audit
**12,535 project declarations / 8,249 theorems**, with only `propext`,
`Classical.choice`, and `Quot.sound`. All ten selected nonapex leaves and both
small coverage subtrees compile. The 13 generated smoke modules reproduce
byte-for-byte. Nine nonapex regression tests, eleven exterior regression tests,
and six manuscript-map tests pass. The 88 mapped manuscript statements remain
unchanged. The full job-0 and job-35 proposals still require full replay.
Proof-map links also pass: **88 labels / 477 Lean declarations**.

Deployment verified: source commit `38d5c740f691792bd19cf545d18565c5b216bd9a`
was uploaded with matching archive and runner SHA256 checksums. Full job-0
replay **30060676** is running on Bouchet. Search array **30060923** has two
tasks running and the remainder queued. Its 41 tasks cover all nonapex jobs
and apex fans F2–F6, with bounded CPU use. See
`hpc/bouchet-cover-jobs-20261019.json` for resource limits and provenance.
No full-domain certificate completion is claimed from these running states.


### 2026-10-19 — Full replay progress and bounded remaining apex fans

Thirteen completed nonapex search proposals (jobs 0–12) were downloaded from
Yale array 30060923. Their recorded source, exit status, expression export,
entire ordered subdivision geometry and first/last arithmetic classifications
were checked locally. The existing job-0 proposal was preserved after confirming
identical geometry. Job 35 was already saved. These are untrusted proposals,
not completed full-domain Lean proofs; provenance is in the HPC search record.

Full nonapex array 30061427 was confirmed submitted; tasks 1–4 were running
and task 6 queued. A diagnostic snapshot of job 0 had 136/1873 modules built,
ABB had 943/7459, and the exterior had 1165/12872, without reported failures.
Counts are heterogeneous build modules, not percentages of the main theorem.
The older S1/F1 jobs remained running with increasing CPU consumption; a failed
diagnostic step is not evidence that the jobs stopped. No full region is
claimed integrated here.

The apex runner now accepts all six fans and uses bounded build workers.
Endpoint/leaf modules are split into smaller independent groups, and malformed
or incomplete proposals fail before generation. The same five F1 sample leaves
compile under this layout. The direct-leaf application supplies the three
coordinate bounds explicitly, avoiding the expensive implicit conversion seen
in the nonapex generator. No positivity obligation has been removed.

Validation: root build passes (3492 jobs); audit still reports 12535 declarations
and 8249 theorems with only the three permitted foundational axioms. All 88
paper labels and 477 Lean links pass, with unchanged mapped manuscript statements.
Five apex parser tests and nine nonapex tests pass. The main theorem still needs
both internal certificate inputs; this is an execution improvement and a durable
record of search results, not a new full-domain theorem.


### 2026-10-19 — Smaller complete regions and incomplete search frontiers

Yale searches for jobs 24–26 produced complete subdivisions with 1611, 952,
and 865 leaves. Their full Lean replays were submitted as array 30062473,
with two concurrent four-CPU tasks. No completed region is claimed yet.
Jobs 14 and 15 instead retained six and ten frontier boxes after their first
bounded searches; they need resumption rather than formal replay of an
incomplete tree. The new resume runner keeps the previous proposal and source
provenance, and writes a fresh result directory.

A literal-constant checker was proved equal to the existing numerical margin
for job 0 in a local experiment. A four-leaf timing comparison showed only a small
single-run difference, so it was not adopted or added to the public proof
root. This experiment did not identify a mathematical error or close a region.


The resumed searches subsequently finished with no frontier: 62,205 nodes for
job 14 and 72,687 for job 15. Their full replays are queued as 30062956 behind
the smaller-region array. Fourteen other complete regions are queued as
30062736 behind the first nonapex array, keeping concurrent workers bounded.
The smallest running job (25) reported 112/241 build modules completed without
reported failures; its final ordered-domain theorem and audit remain pending.


### 2026-10-19 — Complete nonapex proposals and faster cache validation

Complete search proposals now exist for all 36 nonapex jobs; every full replay
is running or queued, including the original S1 job. Full region proofs are
still pending and are not inferred from search completion. Four of the five
remaining apex searches are complete; F4 is being resumed.

The bounded build scheduler now validates cached project modules in Lake
batches instead of one Lake process per cached module. It accepts only
successful batches and a dependency-closed set, and retains the ordinary
bounded build path for everything else. Warm-root validation covered 351
modules in 8.55 seconds; a mixed test reused 141 and built one new module.
A changed-source probe was rejected without rebuilding its artifact. Six
cache regression tests and the unchanged axiom audit pass. No numerical
acceptance condition, statement, or mathematical assumption changed.


### 2026-10-19 — All 42 complete proposals saved; remaining apex replays submitted

Every critical-region search proposal is now present in `lean/data/`: all 36
nonapex jobs and all six apex fans. Their full ordered subdivision geometry
was parsed locally. The downloaded raw archives, source revisions and input
hashes are preserved in the HPC records. Superseded incomplete searches remain
in that raw archive; they are not selected for replay. No positivity claim is
inferred from this geometry check.

Full apex array 30064252 now covers F2–F6 using the tested bounded runner,
eight single-thread workers per job and at most two concurrent jobs. F1 remains
on its existing allocation. Every critical-region full replay is now running
or queued; full theorem builds, audits and integration remain required.


### 2026-10-19 — First complete critical-region proof integrated

`CoverJobReplay.Job25Full.ordered` proves positivity throughout the actual
ordered logarithmic domain of nonapex job 25. All 952 numerical leaves and
43 coverage chunks were checked on Yale. Its 106 generated source files
match regeneration from the saved proposal byte for byte. The transferred
region-only artifacts were accepted by Lake without rebuilding.

The root now imports this theorem. Validation: 3,599 build jobs; the combined
audit passes for 23,501 project declarations and 17,106 theorems using only
`propext`, `Classical.choice`, and `Quot.sound`. The stable map links
`prop:cover` to the complete theorem; all 88 labels and 482 declarations pass.
The manuscript baseline is unchanged. This closes one of 36 nonapex jobs,
not the entire cover or the main theorem. Archived logs and checksums are in
`hpc/bouchet-job25-completion-20261019.json`.

`CheckedCoverJobs.lean` provides stable names for the set of completed
nonapex jobs and the remaining obligations. Its assembly theorem supplies
job 25 automatically; callers now need only the other 35 nonapex regions.
It also transfers each completed ordered-domain proof to positivity of the
original certificate on the entire edge cube. The six full apex results
and the compact-family certificate are still required.


### 2026-10-19 — Direct replay-to-main assembly and literal relabeling clauses

[`MainReplayAssembly.lean`](SparseLowerTail/MainReplayAssembly.lean) proves
`mainTheorem_of_remaining_replays`. The seven recorded external/classical
inputs stay separate from four internal replay inputs: the remaining 35
nonapex regions, all six apex regions, the full ABB neighborhood, and the
full exterior replay conditional on ABB. The checked job-25 import is applied
automatically. This connects the numerical job outputs directly to the target
`MainTheorem`; it does not discharge an unfinished numerical proof.

[`MainRelabeling.lean`](SparseLowerTail/MainRelabeling.lean) proves the literal
at-transition and subcritical relabeling conclusions from `MainTheorem` and
`ClassicalCDFTransport`. They retain both directions of the optimizer
characterization, all parameter inequalities, and uniqueness of the scalar
pair below the transition. This makes the paper-to-Lean formulation bridge
explicit at the main theorem, beyond the existing general partition lemma.

Validation: full root build **3,601 jobs**; transitive axiom audit **23,504
project declarations / 17,109 theorems**, allowing only the three standard
axioms. The stable map passes for **88 labels / 485 declarations**; the
manuscript baseline is unchanged. No whole-region completion count increased.
The assumptions ledger also corrects an outdated note: small-target
rigidity is already proved relative to the recorded external/classical inputs.

Browser-control requests currently time out, so remote jobs cannot be observed
or their outputs retrieved. The latest successful Slurm observation remains
**2026-10-19 21:25 UTC, 43 running jobs and 200 allocated cores**. This is not
a current-state claim. No job was resubmitted or stopped because of the
connection failure. Local storage remains at about 21 GiB free; no bulk replay
or full remote-cache download was started locally.


### 2026-10-20 — Probability-rate deduction

`Section03.LowerTailRate` proves part (a) of `thm:reduction`: the actual
triangle lower-tail log probability is asymptotic to (n²p/2)V(η^(1/3))
when p → 0 and √n p → ∞. The result holds along arbitrary n → ∞ sequences.
The generic KS23 Theorems 5 and 6 are ordinary external hypotheses; their
triangle application and the limiting argument are proved here. The named
graphon approximation, compactness and counting inputs are unchanged.

All 23 new public theorems pass the axiom audit. The
[check record](data/lower-tail-rate-check.json) records source hashes and
checks. Conditioned structure in part (b), the remaining certificate replays,
and the latest manuscript review remain to be completed.


The finite-law good-event estimates for part (b) are also checked:
Markov's inequality, the positive cost excess, the residual dependence
entropy, the four-event union bound, and the quantitative baseline `s3:v0`.
[ConditionalCostBounds.lean](SparseLowerTail/Section03/ConditionalCostBounds.lean)
and its import contain eight audited public theorems. The actual
revealed-edge law applications and the full conditioned-structure and
rounding conclusions remain. The [combined check](data/conditional-cost-check.json)
records their integrated root build and audit.


### 2026-10-20 — Actual revealed-edge laws and the first two good events

The edge configuration is now split by an explicit equivalence into its
revealed and unrevealed coordinates. The product reference, conditioning,
revealed-pattern mass, conditional moments and entropy budget all agree
under this equivalence. Harris gives the actual marginal bounds [0,p],
including zero-mass patterns.

For the actual triangle law, the relaxed-triangle failure probability is at
most β/ζ. The erased vector's entropy is its unrevealed entropy cost plus
the cost of zeroing the revealed edges, bounded by 2p per edge. The discrete
variational lower bound then gives the cost baseline used in part (b).
The actual excess-cost probability and the mean remaining dependence
entropy satisfy the manuscript's bounds under its stated finite parameter
conditions.

All 40 public theorems are audited in the
[revealed-law check](data/revealed-laws-check.json). The full conditioned
cut-distance conclusion, parameter-limit choices, and rounding remain.


`RevealedEntropyTransfer.lean` additionally proves the exact disintegration
of events in the original edge space over the revealed-pattern law. An
exponential event bound under each actual product marginal law transfers
to a bound under the conditioned law in terms of its mean dependence
entropy. The constants give the manuscript's 384ω/ε² estimate. Its six
public theorem audits are in the [transfer check](data/revealed-transfer-check.json).
The cut-event specialization to matrix concentration remains.


### 2026-10-20 — Finite conditioned-structure probability bound

The actual matrix cut-error estimate and the revealed-edge exponential tail
are now proved. Ordered endpoint sums equal the unordered-edge adjacency
matrices, including deletion of the revealed edges. The actual conditional
mean graphon satisfies the required triangle and entropy bounds.

On the four good events, the normalized adjacency kernel is within ε of
an actual minimizer after a genuine measure-preserving bijection. In the
original conditioned edge space, the probability of failure is at most
β/ζ + ω/γ + 384ω/ε² + exp(−αpn²), under the displayed finite parameter
conditions. An explicit choice of the relaxed cube-root target also
satisfies both required slack bounds.

All 36 new public theorem audits are recorded in the
[finite structure check](data/conditioned-structure-finite-check.json).
The remaining tolerance choices and eventual scalar bounds must still be
combined to conclude asymptotic part (b); rounding and manuscript review
also remain.


### 2026-10-20 — Complete probabilistic reduction

Both parts of `thm:reduction` are now checked. The normalized log probability
has the stated multiplicative asymptotic. For every ε > 0, the actual
conditioned probability of admitting a graphon minimizer and a
measure-preserving bijection with cut error < ε tends to one.

The proof chooses all finite tolerances and proves the eventual scalar
bounds throughout n → ∞, p → 0 and √n p → ∞. Only the named external KS23
and standard classical results are explicit hypotheses. The combined
`triangle_reduction` theorem contains both conclusions.

The [check record](data/conditioned-structure-check.json) contains 13 public
theorem audits and the full root audit of 17,817 theorems. Rounding, the
remaining manuscript review and certificate integration remain.


### 2026-10-20 — Vertex partition rounding

`lem:rounding` is proved for arbitrary real matrices on any equal-mass
measurable partition, including measure-preserving pullbacks. The rounded
vertex set has imbalance ≤16δn/(b−a) and matrix cut error ≤33δ. Two signed
tests give the projection deficit; exact cell-average correlations and
sign rounding give the balance and tensor L¹ bounds. No additional
external or classical input is required. The [check record](data/rounding-check.json)
contains 35 public audits and the full root audit of 17,896 theorems.


### 2026-10-20 — Probability-rate corollary

The deduction of `thm:rate` is checked: the rate uses `balancedValue`, and
the entropy-value asymptotic holds exactly when η≥threshold³. A direct
wrapper takes the same remaining numerical replays as the main theorem's
assembly. The [check record](data/probability-rate-check.json) contains four
public theorem audits and a full root audit of 17,900 theorems.


### 2026-10-20 — Conditioned matrix structures

All three cases of `thm:structure` are deduced from the main classification
and the complete reduction. The actual conditional probability tends to one
for the constant matrix above threshold³, the unique minimizing balanced
bipod below it, and their union at coexistence. The matrix errors are εp
and the partition imbalance is εn. The direct assembly wrapper exposes
the same remaining numerical replays as the main theorem.

The [check record](data/conditioned-phases-check.json) contains 11 public
theorem audits and the full root audit of 17,923 theorems.


### 2026-10-20 — Manuscript identities and criteria

The complete trilinear lemma, the one-variable maximum characterization
of the threshold, every pointwise identity of the critical graphon, the
restricted-row bipodality criterion, and branch-and-bound soundness are
checked and mapped to the current manuscript. The current relabeling,
scaling and first-variation arguments were also reviewed against their
proved interfaces. The [check record](data/manuscript-identities-check.json)
contains 46 public audits and the full root audit of 17,961 theorems.


### 2026-10-20 — Interval Cholesky soundness

`lem:comp-chol` is checked for actual real symmetric 3×3 matrices. Positive
Cholesky radicands give an exact sum-of-squares decomposition and
`Matrix.PosDef`. The square-root inclusion rule and an executable dyadic
LDL checker are proved; every accepted box certifies every matrix inside it.
Kernel-evaluated examples accept the identity and reject a zero pivot and
an indefinite matrix. The [check record](data/cholesky-check.json) contains
15 public audits and the full root audit of 17,994 theorems.

# Formalization scope and assumptions

Updated 2026-10-19 following the authors' explicit instructions: assume cited
external theorems and standard classical results; verify all of the paper's own arguments, including the probabilistic rate,
conditioned structure, finite-to-graphon transfer and rounding arguments. The final deliverable is therefore a **formal proof relative to
explicit external/classical inputs**, not a reproof of all mathematics used by
the paper.

We retain three different statuses:

1. **Proved here:** Lean proof terms checked using mathlib and any named inputs
   visible in the theorem's type.
2. **Assumed external/classical:** an exact statement with a stable identifier,
   source reference and explicit role in the proof. Such an input is passed as
   a hypothesis; it is not silently installed as a global axiom.
3. **Still to prove:** an obligation in this paper. Having a definition, a
   numerical report, or a conditional theorem does not discharge it.

The axiom audit still allows only `propext`, `Classical.choice`, and `Quot.sound`.
An assumed theorem appears as an ordinary hypothesis of the final result; the
audit alone cannot certify that the hypothesis has been proved. This file and
the final theorem's type provide that separate provenance information.

## Explicitly encoded external and classical inputs

### `external:KP26:1.6`

- Reference: KP26, Theorem 1.6, with the specialization justified in the paper
  immediately before equation `eq:KP`.
- Exact Lean proposition:
  `SparseLowerTail.Section07.KP26PenalizedReduction` in
  [`ExternalReduction.lean`](SparseLowerTail/Section07/ExternalReduction.lean).
- Meaning: for γ > 0, a minimizing balanced pair for F + γt gives a lower bound
  for F(U) + γt(U) for **every graphon U**.
- Status: **assumed external**, never asserted by an axiom or claimed proved.
- Proved consequences: scalar penalized minimizer existence (independent of
  KP26), transfer to constrained optimality at a supported target, the value
  identity, and the active constraint/penalized optimality of every constrained
  minimizer at that target.
- The supporting pair and full range r ≤ r₋ are proved in
  `SmallData.lean`. Equality-case rigidity is now proved in
  `SmallTailAssembly.lean`, using the separately recorded classical sampling
  and positive-kernel spectral inputs. The KP26 transfer lemma alone does
  not supply that rigidity.

### `classical:inverse-transform-sampling`

- Classical theorem: every Borel probability measure on the real line is the
  distribution of a measurable function of a uniform random variable on [0,1]
  (inverse-transform sampling). This is the probability-integral transport used
  in the manuscript's proof of `prop:vertex`.
- Exact Lean proposition: `SparseLowerTail.Section04.UniformSampling` in
  [`VertexReweighting.lean`](SparseLowerTail/Section04/VertexReweighting.lean):
  for every probability measure ν on ℝ there exists Q with
  `MeasurePreserving Q unitMeasure ν`.
- Status: **assumed classical**, as an ordinary proposition parameter, not an
  axiom. No graphon optimizer conclusion is included in this assumption.
- Proved here: the perturbed probability measure, actual reweighted graphon,
  product-measure transport, all weighted integral identities and derivatives,
  and the resulting vertex and two-block-minimizer conclusions.
- Current uses: `prop:vertex`, the measurable-partition version of
  `cor:bipodalmin`, and their dependents. Relabeling equivalence is still tracked
  separately; this sampling theorem does not silently supply it.

### `classical:dyadic-l1-approximation`

- Exact input: `Section02.ClassicalDyadicL1Approximation` in
  [BlockAveraging.lean](SparseLowerTail/Section02/BlockAveraging.lean).
- Every integrable real kernel on the unit square converges in L¹ to its
  averages over the defined dyadic square partitions. This is the standard
  dyadic conditional-expectation approximation theorem, used in `lem:lsc`.
- It contains no entropy, graphon minimizer, or optimization conclusion.
  Finite-block Jensen, entropy continuity, lower semicontinuity, and the
  minimizing-sequence argument are proved here.

### `classical:graphon-cut-compactness`

- Exact input: `Section02.ClassicalGraphonCompactness` in
  [Relabeling.lean](SparseLowerTail/Section02/Relabeling.lean).
- Every graphon sequence admits a subsequence and measure-preserving vertex
  maps whose pullbacks converge in the actual rectangle cut norm.
- This is the weaker vertex-map consequence of the bijective compactness in
  `lem:cut`(c), citing BCLSV08 Proposition 3.6, LS07 Theorem 5.1 and Lov12
  Theorem 9.23. It assumes no cost or minimizer conclusion.

### `classical:counting-lemma`

- Exact input: `Section02.ClassicalTriangleCounting` in
  [Relabeling.lean](SparseLowerTail/Section02/Relabeling.lean): for all actual
  graphons U, W, `|triangle U - triangle W| ≤ 3 * cutNorm (U - W)`.
- This is the triangle specialization of `lem:cut`(b), citing Lov12 Lemma
  10.23. Its convergence consequence is proved here.

### `classical:nonatomic-cdf-transport`

- Exact input: `Section02.ClassicalCDFTransport` in
  [RelabelBalanced.lean](SparseLowerTail/Section02/RelabelBalanced.lean).
- For any finite nonatomic real measure ν and real c, the function
  `x ↦ c + ν.real (Iic x)` transports ν to Lebesgue measure restricted to
  `[c, c + ν.real univ]`. This is the probability-integral transform, with
  scaling and translation; it includes the zero-mass case.
- The paper uses this CDF construction in `lem:relabelB`. The actual piecewise
  map for a half partition, its preservation of unit measure, its a.e. block
  membership, and both directions of the graphon equivalence are proved here.
  No graphon relabeling conclusion is assumed as part of this classical input.

### `classical:pullback-l1-approximation`

- Exact input: `Section02.ClassicalPullbackApproximation` in
  [CutDistanceIdentities.lean](SparseLowerTail/Section02/CutDistanceIdentities.lean).
- For every integrable real kernel K, every measure-preserving vertex map φ,
  and ε > 0, there is a measure-preserving measurable bijection ψ such that
  the L¹ distance between K pulled back by ψ and by φ is less than ε.
- This is the standard approximation underlying the zero-cut-distance
  pullback assertion in `lem:cut`(d). It assumes no entropy or optimization
  claim. Norm invariance, distance symmetry, the triangle inequality and the
  deduction of zero cut distance are proved here.

### `classical:positive-hilbert-schmidt-spectrum`

- Exact input: `Section07.PositiveKernelSpectralTheorem`, returning
  `KernelSpectralExpansion`, in
  [ClassicalKernelSpectrum.lean](SparseLowerTail/Section07/ClassicalKernelSpectrum.lean).
- For every symmetric positive real L² kernel on the atomless unit interval,
  supplies measurable orthonormal eigenfunctions, nonnegative decreasing
  eigenvalues, genuine integral eigen-equations, square-summability, L²
  convergence of finite kernel sums, positive residual quadratic forms, and
  the standard square/cube trace identities. Its rowwise Parseval formulation
  is the corresponding classical almost-everywhere L²-section identity.
- This is the compact positive self-adjoint spectral theorem and its
  Hilbert–Schmidt kernel realization, the classical decomposition invoked in
  `lem:spectral`. The pinned mathlib spectrum module explicitly lists compact
  self-adjoint spectral theory as future work.
- It asserts **no** trace-class conclusion, bound on the sum of eigenvalues,
  graphon diagonal/degree bound, leading-eigenvalue estimate, residual bound,
  or optimizer classification. Those are paper-specific deductions proved
  internally. In particular, the trace bound follows from positivity and
  Lebesgue differentiation, using mathlib's differentiation theorem.
- Concrete kernel/spectral-sum statements encode the estimates; this does not
  claim a new fully formalized general trace-class operator API.

### `classical:harris-positive-association`

- Reference: the Harris inequality, cited as `Har60` in manuscript `lem:harris`.
- Exact input: `Section03.ClassicalHarrisPositiveAssociation` in
  [HarrisConditioning.lean](SparseLowerTail/Section03/HarrisConditioning.lean).
  For independent Bernoulli coordinates with means in [0,1], the probability
  of the intersection of two increasing events is at least the product of
  their probabilities.
- Proved consequences: increasing/decreasing correlation, conditional
  increasing-event domination, pinned-coordinate product bounds, the actual
  conditional law after revealing coordinates, and decreasing hypergraph
  lower-tail sections. The input is an ordinary theorem hypothesis.

## Classical infrastructure eligible to be assumed when needed

Compactness and triangle counting are now encoded above. Remaining optional
inputs require exact Lean statements and review at the point of use.

| Stable identifier | Classical result and paper location | References in the paper |
| --- | --- | --- |
| `classical:graphon-cut-compactness` | Sequential compactness modulo measure-preserving relabelings; `lem:cut`(c). | BCLSV08 Proposition 3.6; LS07 Theorem 5.1; Lov12 Theorem 9.23. |
| `classical:cut-distance-representation` | Coupling/relabeling descriptions of cut distance and their equivalence; `lem:cut`(d). | BCLSV08 Lemma 3.5. |
| `classical:counting-lemma` | Continuity of triangle density in cut norm; `lem:cut`(b). | Lov12 Lemma 10.23. |
| `classical:measure-analysis` | Standard Fubini, dominated convergence, Jensen, compactness, differentiation, and inverse-function results. | Use existing mathlib theorems where available; add a precise explicit input only when necessary. |

The paper's own Euler–Lagrange/vertex arguments, branch and crossing analysis,
rigidity, boundary comparison, certificate verification, and final assembly
must be proved here; completed items are recorded in the proof map. They are not
reclassified as classical merely because
proving them in Lean is difficult. The numerical certificates remain part of the
new argument and are not covered by the permission to assume external theorems.

## Internal hypotheses are not external results

`SparseLowerTail.Section05.CriticalClassification` in
[`ThresholdReduction.lean`](SparseLowerTail/Section05/ThresholdReduction.lean)
is the paper's own `prop:critical`, stated in measurable-partition form. The
threshold theorem has been deduced from it. `CriticalAssembly` now derives it
from explicit finite-cover and apex-certificate hypotheses, but these internal
positivity/geometric obligations remain unproved. It must be discharged, not retained among the final external inputs.
Likewise certificate positivity, matching-data and continuation hypotheses
remain internal proof obligations. The vertex identity has now been proved
relative only to the classical sampling input above. The completed
Euler–Lagrange proposition requires none of these hypotheses.

## Changing the manuscript

[`proof-map.json`](proof-map.json) uses LaTeX labels as identifiers. Displayed
numbers are optional historical metadata. Each entry has a normalized statement
fingerprint and, when present, a fingerprint of its adjacent proof.

After exporting a revised draft, run from the repository root:

```sh
python3 tools/check_manuscript_map.py /path/to/revised/arxiv_v1.tex
```

Intro edits and automatic renumbering leave the mapped statements unchanged.
A changed statement, changed proof, missing label or renamed label requires
review. The checker never updates proof status or accepts a new baseline.
Update the corresponding Lean declaration and affected dependents, rebuild and
audit, then deliberately update the map baseline and progress log. Keep stable
labels through revisions where possible; if a label is renamed, record its old
name as an alias in the map rather than silently treating it as a new theorem.

This is a focused textual tracker, not a full TeX parser or semantic-equivalence
checker. Changes to shared macro definitions or unmapped statements also require
manual review. A clean comparison does not prove that a revised paper is correct.


## Main theorem: exact remaining replay inputs

`SparseLowerTail.mainTheorem_of_remaining_replays` in
[`MainReplayAssembly.lean`](SparseLowerTail/MainReplayAssembly.lean) separates
seven permitted external/classical inputs from four internal inputs:

- `RemainingNonapexJobResults`: every full nonapex domain except the proved
  job 25, supplied by `CheckedCoverJobs`.
- `ApexJobResults`: all six full apex domains, including their zero patterns.
- `FamilyABBLocal`: the full moving ABB neighborhood and its unique zero.
- `FamilyABBLocal → CompactFamilyCertificate`: exactly the conditional output
  of the complete exterior replay; applying it to the preceding input removes
  the ABB premise.

This theorem proves the deduction, not these four inputs. The two corollaries
in [`MainRelabeling.lean`](SparseLowerTail/MainRelabeling.lean) express the
at-transition and subcritical classifications as actual measure-preserving
pullbacks up to almost-everywhere equality. They additionally take
`ClassicalCDFTransport`, as does the existing partition-to-pullback bridge.

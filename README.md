# Verification for *The Lower Tail of Triangle Counts in Sparse Random Graphs*

This repository accompanies the paper *The Lower Tail of Triangle Counts in
Sparse Random Graphs* by Dong Huang and Shuangping Li. It contains two kinds
of verification.

- **Computer-assisted proofs.** Two propositions of the paper, and the
  numerical constants used with them, reduce to explicit inequalities for
  functions of at most three variables and one parameter. Python programs
  prove these inequalities in validated interval arithmetic.
- **A Lean 4 formalization** of the paper's own arguments, including a replay
  of the computer-assisted certificates in Lean.

Theorem and lemma numbers below refer to the current version of the paper.
The LaTeX label of each statement is given in parentheses.

## Computer-assisted proofs

| Statement | What the computation proves | Code | Results |
| --- | --- | --- | --- |
| Lemma 3.11 (`lem:digits`), threshold constants | Encloses the crossing point and the printed values of $a_*$, $b_*$, $\mu_*$ and $r_*$, including $0.2096696762 < r_* < 0.2096696763$. | [`endpoint_common.py`](verification/cover/endpoint_common.py) (`setup_constants()`) | [Constant enclosures](certificates/release/cover/endpoint_inputs_verified.json) |
| Lemma 6.7 (`lem:penconstants`), penalized constants | Encloses the coexistence parameter and the printed values of $\gamma_c$, $C(\gamma_c)$, $r_-$ and $r_+$. | [`verify_penalized_constants.py`](verification/cover/verify_penalized_constants.py) | [Penalized constants](certificates/release/cover/penalized_constants_verified.json) |
| Proposition 4.17 (`prop:cover`), twelve-cell cover at the threshold | Checks that the twelve cells cover the region, validates their support bounds and tangency coefficients, and proves all required positivity inequalities. | [`endpoint_common.py`](verification/cover/endpoint_common.py), [`planar_coverage.py`](verification/cover/planar_coverage.py), [`verify_endpoint.py`](verification/cover/verify_endpoint.py) | [Cover reports](certificates/release/cover/) |
| Proposition 7.4 (`prop:family`), certificate family below the threshold | Proves the certificate inequality uniformly for every $L \in [3.9, 9.5]$, with the prescribed zero patterns. | [`verify_family.py`](verification/family/verify_family.py), [`core.py`](verification/family/core.py), [`symbolic.py`](verification/family/symbolic.py) | [Family report](certificates/release/family/family.json) |

The full run covers all 42 cover regions, both Hessian neighborhoods of the
family, and the compact family domain, with no unresolved boxes
([run record](certificates/release/run.json)). A separate
[table comparison](certificates/manuscript-table-match.json) checks the twelve
cells against the tables printed in the paper.

## Lean formalization

The Lean source is in [`lean/SparseLowerTail`](lean/SparseLowerTail). The
main theorem is stated in
[`MainStatement.lean`](lean/SparseLowerTail/MainStatement.lean) and assembled
in [`MainTheoremAssembly.lean`](lean/SparseLowerTail/MainTheoremAssembly.lean).
The folders `Section02` to `Section08` follow the section numbering of an
earlier draft of the paper. In the current version `Section03` is Appendix A,
the folders `Section04` to `Section08` are Sections 3 to 7, and `Numerics`
holds the interval arithmetic of Appendix B.

The Lean development formalizes the paper's own arguments, from the
reduction in Appendix A to the main result, Theorem 1.3 (`thm:main`), and its
consequences, Theorems 1.1 and 1.2. It assumes the cited results of Kozma and
Samotij and of Kwan and Pham, together with a few classical facts such as the
Harris inequality, compactness of graphons in the cut distance, and the
counting lemma. Each assumption enters the final theorem as an explicit
hypothesis, and [ASSUMPTIONS.md](lean/ASSUMPTIONS.md) lists them with their
sources. The axiom audit allows only `propext`, `Classical.choice` and
`Quot.sound`. The [proof map](lean/proof-map.json) links each statement of the
paper to its Lean declarations.

| Part of the paper | Main statements | Lean code | Build and audit records |
| --- | --- | --- | --- |
| Reduction to the variational problem (Appendix A) | Theorem A.1 (`thm:reduction`), Lemmas A.3–A.10 (`lem:fp`, `lem:discrete`, `lem:stability`, `lem:stepcut`, `lem:harris`, `lem:decorrelation`, `lem:entropy`, `lem:cutconc`) | [`Section03/`](lean/SparseLowerTail/Section03), [`LowerTailRate.lean`](lean/SparseLowerTail/Section03/LowerTailRate.lean), [`ConditionedStructure.lean`](lean/SparseLowerTail/Section03/ConditionedStructure.lean), [`DiscreteComparison.lean`](lean/SparseLowerTail/Section03/DiscreteComparison.lean), [`Decorrelation.lean`](lean/SparseLowerTail/Section03/Decorrelation.lean), [`ConditionedProductEntropy.lean`](lean/SparseLowerTail/Section03/ConditionedProductEntropy.lean), [`HarrisConditioning.lean`](lean/SparseLowerTail/Section03/HarrisConditioning.lean) | [rate](lean/data/lower-tail-rate-check.json), [structure](lean/data/conditioned-structure-check.json), [discretization](lean/data/discrete-comparison-check.json), [decorrelation](lean/data/decorrelation-check.json), [entropy](lean/data/conditioned-product-entropy-check.json), [Harris](lean/data/harris-conditioning-check.json), [cut concentration](lean/data/cut-concentration-check.json), [sparse entropy](lean/data/sparse-entropy-check.json), [near minimizers](lean/data/near-minimizers-check.json) |
| Main theorems | Theorems 1.1 and 1.2 (`thm:rate`, `thm:structure`), Lemma A.11 (`lem:rounding`) | [`MainStatement.lean`](lean/SparseLowerTail/MainStatement.lean), [`MainTheoremAssembly.lean`](lean/SparseLowerTail/MainTheoremAssembly.lean), [`ProbabilityRate.lean`](lean/SparseLowerTail/Section03/ProbabilityRate.lean), [`ConditionedPhases.lean`](lean/SparseLowerTail/Section03/ConditionedPhases.lean), [`Rounding.lean`](lean/SparseLowerTail/Section03/Rounding.lean) | [rate](lean/data/probability-rate-check.json), [structure](lean/data/conditioned-phases-check.json), [rounding](lean/data/rounding-check.json) |
| Graphon preliminaries (Section 2) | Lemmas 2.1 and 2.2 (`lem:trilinear`, `lem:cut`) and related identities | [`Section02/`](lean/SparseLowerTail/Section02), [`Trilinear.lean`](lean/SparseLowerTail/Section02/Trilinear.lean), [`CutNorm.lean`](lean/SparseLowerTail/Section02/CutNorm.lean), [`CutDistance.lean`](lean/SparseLowerTail/Section02/CutDistance.lean) | [cut metric](lean/data/kernel-cut-check.json), [identities](lean/data/manuscript-identities-check.json) |
| Two block graphons and first order conditions (Sections 3 and 6) | Proposition 3.2 (`prop:euler`), Theorem 3.7 (`thm:crossing`), Lemma 3.11 (`lem:digits`), Proposition 6.6 (`prop:pen`), Lemma 6.7 (`lem:penconstants`) | [`Section04/`](lean/SparseLowerTail/Section04), [`EulerLagrange.lean`](lean/SparseLowerTail/Section04/EulerLagrange.lean), [`Crossing.lean`](lean/SparseLowerTail/Section04/Crossing.lean), [`ManuscriptThresholdDigits.lean`](lean/SparseLowerTail/Section04/ManuscriptThresholdDigits.lean), [`PenalizedValue.lean`](lean/SparseLowerTail/Section07/PenalizedValue.lean), [`PenalizedDigits.lean`](lean/SparseLowerTail/Section07/PenalizedDigits.lean) | [two block minimizers](lean/data/final-manuscript-review-check.json), [Euler–Lagrange and penalized gap](lean/data/analytic-review-check.json), [threshold constants](lean/data/manuscript-digits-check.json), [penalized constants](lean/data/penalized-digits-check.json) |
| Certificates at the threshold (Section 4, Appendix B) | Lemmas 4.14–4.16 (`lem:patterns`, `lem:apex`, `lem:taylor`), Proposition 4.17 (`prop:cover`), Lemmas B.1, B.2 and B.4 (`lem:comp-box`, `lem:comp-chol`, `lem:fan`) | [`Section05/`](lean/SparseLowerTail/Section05), [`PatternDerivatives.lean`](lean/SparseLowerTail/Section05/PatternDerivatives.lean), [`CriticalApex.lean`](lean/SparseLowerTail/Section05/CriticalApex.lean), [`ApexTaylorLocal.lean`](lean/SparseLowerTail/Section05/ApexTaylorLocal.lean), [`ApexCoverAssembly.lean`](lean/SparseLowerTail/Section05/ApexCoverAssembly.lean), [`PolygonFan.lean`](lean/SparseLowerTail/Section05/PolygonFan.lean), [`BoxLowerBounds.lean`](lean/SparseLowerTail/Numerics/BoxLowerBounds.lean), [`Cholesky3.lean`](lean/SparseLowerTail/Numerics/Cholesky3.lean) | [patterns](lean/data/patterns-check.json), [apex](lean/data/critical-apex-check.json), [Taylor bound](lean/data/taylor-cube-check.json), [polygon fan](lean/data/polygon-fan-check.json), [box bounds](lean/data/box-lower-bounds-check.json), [interval Cholesky](lean/data/cholesky-check.json), [all 42 regions](hpc/results-20261021-0620/verified-regions.json) |
| Certificates below the threshold (Section 7, Appendix B) | Lemmas 7.2 and 7.5 (`lem:certcoef`, `lem:tieexclusion`), Proposition 7.4 (`prop:family`), Proposition B.5 (`appA3:compact`) | [`Section08/`](lean/SparseLowerTail/Section08), [`CertificateUniqueness.lean`](lean/SparseLowerTail/Section08/CertificateUniqueness.lean), [`TieExclusion.lean`](lean/SparseLowerTail/Section08/TieExclusion.lean), [`FiniteCertificateAssembly.lean`](lean/SparseLowerTail/Section08/FiniteCertificateAssembly.lean), [`FamilyCompactAssembly.lean`](lean/SparseLowerTail/Section08/FamilyCompactAssembly.lean), [`ManuscriptCompactConclusion.lean`](lean/SparseLowerTail/Section08/ManuscriptCompactConclusion.lean) | [coefficients](lean/data/certificate-uniqueness-check.json), [weak duality](lean/data/certificate-summary-check.json), [tie exclusion](lean/data/paper-tie-check.json), [exterior replay](hpc/results-20261021-0635/exterior-completion.json), [contact neighborhood](hpc/results-20261021-0635/abb-completion.json), [radius extension](lean/data/family-hessian-perturbation-check.json), [binary64 radius](lean/data/family-binary64-radius-check.json), [compact conclusion](lean/data/compact-conclusion-laptop-pilot-check.json) |

## Status

All checks listed above are complete. The final combined Lean build and
axiom audit, which includes the exact-radius contact neighborhood for
Proposition 7.4, is running on the Yale Bouchet cluster. The
[cluster record](hpc/README.md) has the current state of the runs, and the
[coverage inventory](lean/manuscript-coverage.json) tracks any remaining
obligations.

## Reproducing the numerical checks

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py --jobs 2
```

Use Python 3.11 or newer, with assertions enabled. The command writes reports
under `results/` and ends with `"status": "complete"` when every check
passes; the recorded full run took about five minutes. For a quick
installation check, run `python verify.py --quick`. The computations use
FLINT/Arb ball arithmetic and exact rational geometry, and the saved reports
include hashes of the sources and inputs.

## Reproducing the Lean checks

The [Lean build guide](lean/README.md) gives the pinned toolchain, the build
commands, the theorem map and the axiom audit. To inspect an archived set of
regional results, run

```sh
python3 hpc/audit_result_archives.py \
  hpc/triangle-verification-results-20261020-0238.tar.gz \
  --output /tmp/verified-regions.json
```

## Repository layout

- [`verification/cover`](verification/cover/README.md) checks the twelve-cell
  cover and the threshold constants.
- [`verification/family`](verification/family/README.md) checks the
  certificate family, uniformly in $L$.
- [`certificates`](certificates/) holds the saved reports of the full run.
- [`lean/SparseLowerTail`](lean/SparseLowerTail) holds the Lean source, and
  [`lean`](lean/README.md) also holds the build guide, the proof map and the
  list of assumptions.
- [`hpc`](hpc/README.md) holds the cluster scripts, logs and run records.
- [`AUDIT.md`](AUDIT.md) describes how the release was reviewed, and
  [`docs/PROOF-SIMPLIFICATIONS.md`](docs/PROOF-SIMPLIFICATIONS.md) collects
  notes on simplified arguments.

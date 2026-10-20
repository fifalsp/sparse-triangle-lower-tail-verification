# The Sparse Triangle Lower Tail: verification

Computational verification and Lean 4 proofs for **The Sparse Triangle Lower
Tail: Threshold and Minimizers**, by Dong Huang and Shuangping Li.

## Verified results

Updated October 20, 2026.

| Check | Completed result | Evidence |
| --- | --- | --- |
| Python interval verification | All 42 cover regions, both family Hessian neighborhoods, and the full compact family domain; zero unresolved boxes | [Full run](certificates/release/run.json) |
| Lean full-domain nonapex certificates | **34 of 36 regions** | [Build and axiom-audit records](hpc/results-20261020-0238/verified-regions.json) |
| Lean full-domain apex certificates | **5 of 6 fans: F2, F3, F4, F5, F6** | [Build and axiom-audit records](hpc/results-20261020-0238/verified-regions.json) |
| Euler equation and penalized gap | Positive unique multiplier and quantitative bounds; Δ(10⁻³)>0.028 | [Lean build and 30 axiom audits](lean/data/analytic-review-check.json) |
| Cut metric (`lem:cut`) | Sharp weighted bound, counting bounds, bijective compactness and real-kernel pseudometric identities | [Lean build and 26 axiom audits](lean/data/kernel-cut-check.json) |
| Penalized coexistence constants (`lem:penconstants`) | All five printed brackets for z_c, γ_c, C(γ_c), r₋ and r₊ | [Lean build and 56 axiom audits](lean/data/penalized-digits-check.json) |
| Current threshold bracket (`lem:digits`) | Exact manuscript bracket of width 2×10⁻²⁵ and all four printed parameter ranges | [Lean build and 28 axiom audits](lean/data/manuscript-digits-check.json) |
| Crossing and tie exclusion | Unique penalized crossing and full-interval tie relabeling, with the family certificate input explicit | [Lean build and 25 axiom audits](lean/data/paper-tie-check.json) |
| Certificate coefficients (`lem:certcoef`) | Printed determinant, unique coefficient solution, and the original value/partial-derivative equations | [Lean build and 26 axiom audits](lean/data/certificate-uniqueness-check.json) |
| Certificate and support identities | All four weak-duality conclusions, sharp minimizer support data, real-block codegrees and branch contact identity | [Lean build and 52 axiom audits](lean/data/certificate-summary-check.json) |
| Triangle patterns (`lem:patterns`) | Four-atom law, symmetric partial derivatives, and relabeling from pattern support and balanced mean | [Lean build and 20 axiom audits](lean/data/patterns-check.json) |
| Critical apex (`lem:apex`) | The actual relaxed triangle law, sharp support, zero Hoeffding expectation, and universal two-contact certificate identity | [Lean build and 27 axiom audits](lean/data/critical-apex-check.json) |
| General cube Taylor estimate (`lem:taylor`) | The full infinity-norm cubic remainder, Euclidean quadratic term, and strict positivity at the stated radius | [Lean build and 15 axiom audits](lean/data/taylor-cube-check.json) |
| Box lower bounds (`lem:comp-box`) | All four bounds from actual gradient and Hessian enclosures, including the quadratic supporting-plane bound | [Lean build and 18 axiom audits](lean/data/box-lower-bounds-check.json) |
| Interval matrix positivity (`lem:comp-chol`) | Positive-radicand criterion and a checked 3×3 interval LDL test proving every represented matrix positive definite | [Lean build and 15 axiom audits](lean/data/cholesky-check.json) |
| Trilinear and transition identities | Full trilinear lemma, maximum formula R(z), critical graphon identities, row criterion, and branch-and-bound soundness | [Lean build and 46 axiom audits](lean/data/manuscript-identities-check.json) |
| Structure corollary (`thm:structure`) | Constant above threshold³, the unique balanced bipod below, and their union at coexistence, each with conditional probability →1; remaining certificate inputs explicit | [Lean build and 11 axiom audits](lean/data/conditioned-phases-check.json) |
| Matrix rounding (`lem:rounding`) | An explicit vertex partition with imbalance ≤16δn/(b−a) and matrix cut error ≤33δ | [Lean build and 35 axiom audits](lean/data/rounding-check.json) |
| Conditioned structure (`thm:reduction` part b) | For every ε > 0, the actual conditioned probability of proximity to a minimizer tends to one | [Full reduction build and 13 axiom audits](lean/data/conditioned-structure-check.json) |
| Rate corollary (`thm:rate`) | Balanced-value rate and the replica-symmetric threshold criterion, deduced from the main classification; remaining certificate inputs explicit | [Lean build and four axiom audits](lean/data/probability-rate-check.json) |
| Probability rate (`thm:reduction` part a) | Actual triangle log probability asymptotic to (n²p/2)V(η^(1/3)), using the cited generic KS23 bounds | [Lean build and 23 axiom audits](lean/data/lower-tail-rate-check.json) |
| Discrete variational comparison (`lem:discrete`) | Attained finite minimum, the finite lower bound, and convergence to the graphon value as n → ∞ and p → 0 | [Lean build and 70 axiom audits](lean/data/discrete-comparison-check.json) |
| Triangle decorrelation (`lem:decorrelation`) | Revealed-edge set and conditional product-error bound, using the cited generic KS23 inputs | [Lean build and 36 axiom audits](lean/data/decorrelation-check.json) |
| Cut concentration and step-kernel cut norms (`lem:cutconc`, `lem:stepcut`) | Exact exponential tail bound; matrix–graphon norm equality and binary maximizers | [Lean build and 36 axiom audits](lean/data/cut-concentration-check.json) |
| Harris conditioning (`lem:harris`) | Increasing-event and pinned-coordinate bounds, including revealed coordinates, using the cited Harris inequality | [Lean build and 19 axiom audits](lean/data/harris-conditioning-check.json) |
| Conditional entropy (`lem:entropy`) | Entropy budget and event-probability transfer for the actual finite conditional laws and their product marginals | [Lean build and 30 axiom audits](lean/data/conditioned-product-entropy-check.json) |
| Sparse Bernoulli entropy (`lem:fp`) | Uniform comparison with the sparse entropy, including the sharp quadratic upper bound | [Lean build and axiom audit](lean/data/sparse-entropy-check.json) |
| Near-minimizer stability (`lem:stability`) | Approximate feasibility and optimality imply proximity to an actual minimizer after a measure-preserving bijection | [Lean build and axiom audit](lean/data/near-minimizers-check.json) |
| Lean family AAA neighborhood | Nonnegativity and the unique AAA zero for every L ∈ [3.9, 9.5] | [Formalization record](lean/README.md) |
| Current Lean project root | Full build and standard-axiom audit of **18,257 theorems** passed | [Root build and audit](lean/data/analytic-review-check.json) |

Apex fan **F4** is the latest completion, bringing the full-region
Lean total to **39 of 42**. Completed nonapex indices are 1–11 and 13–35 (indices start at zero).

The Lean development also checks the balanced phase classification, printed
threshold intervals, Euler–Lagrange equations, local rigidity, small-target
classification, and the deduction of the main theorem from the remaining
finite certificates. The [proof map](lean/proof-map.json) links each paper
statement to its Lean declarations; [named inputs](lean/ASSUMPTIONS.md) lists
the external and classical results used.

**CPU work remaining:** 2 nonapex regions, apex fan F1, the family ABB and
exterior replays, and the combined build importing all completed certificates.
The [cluster record](hpc/README.md) tracks running jobs and recovery.
The [current manuscript inventory](lean/manuscript-coverage.json) lists
the author arguments that still need formalization or review.

## Which parts of the paper does the code verify?

| Statement in the paper | What the computation establishes | Verification code | Saved results |
| --- | --- | --- | --- |
| **Lemma 4.12** — threshold constants (`lem:digits`; Appendix A.4) | Brackets the crossing point and certifies the displayed intervals for a\*, b\*, μ\*, and r\*, including **0.2096696762 < r\* < 0.2096696763**. | [`endpoint_common.py`](verification/cover/endpoint_common.py), function `setup_constants()` | [Constant enclosures](certificates/release/cover/endpoint_inputs_verified.json) |
| **Lemma 7.7** — penalized coexistence constants (`lem:penconstants`; Appendix A.4) | Brackets the coexistence parameter and certifies the displayed values of γ_c, C(γ_c), r_−, and r_+. | [`verify_penalized_constants.py`](verification/cover/verify_penalized_constants.py) | [Penalized constants](certificates/release/cover/penalized_constants_verified.json) |
| **Proposition 5.19** — the twelve-cell cover (`prop:cover`; Appendix A.2) | Checks that the cells cover the required region, validates their support bounds and tangency coefficients, and proves the required positivity inequalities. | [`endpoint_common.py`](verification/cover/endpoint_common.py), [`planar_coverage.py`](verification/cover/planar_coverage.py), and [`verify_endpoint.py`](verification/cover/verify_endpoint.py) | [Cover reports](certificates/release/cover/) |
| **Proposition 8.4** — the certificate family (`prop:family`; Appendix A.3) | Verifies the certificate uniformly for **every L ∈ [3.9, 9.5]**, including its prescribed zero patterns. | [`verify_family.py`](verification/family/verify_family.py), with formulas in [`core.py`](verification/family/core.py) and exact identities in [`symbolic.py`](verification/family/symbolic.py) | [Family report](certificates/release/family/family.json) |

The statement numbers were checked against the Overleaf PDF on October 19, 2026.
The LaTeX labels are included so that the correspondence remains clear if the
paper is renumbered. The exact manuscript snapshot is recorded in
[`data/manuscript.json`](data/manuscript.json).

## Reproduce the numerical checks

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py --jobs 2
```

Use Python 3.11 or newer. The command writes reports under `results/` and
finishes with `"status": "complete"` when every check passes. The recorded full
run took 293 seconds. Use `python verify.py --quick` for an installation check.
Run Python with assertions enabled.

The computations use FLINT/Arb interval bounds and exact rational geometry.
Source and input hashes accompany the saved reports. The
[manuscript comparison](certificates/manuscript-table-match.json) checks all
twelve cells against the paper's tables.

## Reproduce the Lean checks

See the [Lean build guide](lean/README.md) for the pinned toolchain, build
commands, theorem map and axiom audit. The latest archived regional results can
be inspected with:

```sh
python3 hpc/audit_result_archives.py \
  hpc/triangle-verification-results-20261020-0238.tar.gz \
  --output /tmp/verified-regions.json
```

Each completed region has a successful full-target Lean build and an axiom
audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

## Code and reports

- [Cover verification](verification/cover/README.md): geometry, support bounds,
  coefficients, and the 42 positivity checks.
- [Family verification](verification/family/README.md): the two Hessian
  neighborhoods and the compact domain, uniformly in L.
- [Lean formalization](lean/README.md): checked proofs and file-to-paper mapping.
- [Cluster runs](hpc/README.md): deployment scripts, logs and recovery records.
- [Audit methods](AUDIT.md) and [proof simplifications](docs/PROOF-SIMPLIFICATIONS.md).

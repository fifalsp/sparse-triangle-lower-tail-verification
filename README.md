# The Sparse Triangle Lower Tail: verification

Computational verification and Lean 4 proofs for **The Sparse Triangle Lower
Tail: Threshold and Minimizers**, by Dong Huang and Shuangping Li.

## Verified results

Updated October 19, 2026.

| Check | Completed result | Evidence |
| --- | --- | --- |
| Python interval verification | All 42 cover regions, both family Hessian neighborhoods, and the full compact family domain; zero unresolved boxes | [Full run](certificates/release/run.json) |
| Lean full-domain nonapex certificates | **27 of 36 regions** | [Build and axiom-audit records](hpc/results-20261019-2330/verified-regions.json) |
| Lean full-domain apex certificates | **4 of 6 fans: F2, F3, F5, F6** | [Build and axiom-audit records](hpc/results-20261019-2330/verified-regions.json) |
| Sparse Bernoulli entropy (`lem:fp`) | Uniform comparison with the sparse entropy, including the sharp quadratic upper bound | [Lean build and axiom audit](lean/data/sparse-entropy-check.json) |
| Near-minimizer stability (`lem:stability`) | Approximate feasibility and optimality imply proximity to an actual minimizer after a measure-preserving bijection | [Lean build and axiom audit](lean/data/near-minimizers-check.json) |
| Lean family AAA neighborhood | Nonnegativity and the unique AAA zero for every L ∈ [3.9, 9.5] | [Formalization record](lean/README.md) |
| Combined Lean project | Full nonapex job 25 imported; combined build and axiom audit passed | [Integration record](hpc/bouchet-job25-completion-20261019.json) |

The latest completed nonapex jobs are **18 and 19**, bringing the full-region
Lean total to **31 of 42**. Completed nonapex indices are 1–11, 16–29, 32 and
33 (indices start at zero).

The Lean development also checks the balanced phase classification, printed
threshold intervals, Euler–Lagrange equations, local rigidity, small-target
classification, and the deduction of the main theorem from the remaining
finite certificates. The [proof map](lean/proof-map.json) links each paper
statement to its Lean declarations; [named inputs](lean/ASSUMPTIONS.md) lists
the external and classical results used.

**Remaining:** 9 nonapex regions, apex fans F1 and F4, the family ABB and
exterior replays, and the combined build importing all completed certificates.
The [cluster record](hpc/README.md) tracks running jobs and recovery.
The [current manuscript inventory](lean/manuscript-coverage.json) also tracks
the authors’ probabilistic deductions and alignment with the latest Overleaf source.

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
  hpc/triangle-verification-results-20261019-2330.tar.gz \
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

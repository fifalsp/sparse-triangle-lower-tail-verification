# The Sparse Triangle Lower Tail: computational verification

This repository contains the numerical verification used in **The Sparse Triangle
Lower Tail: Threshold and Minimizers**, by Dong Huang and Shuangping Li.

The paper identifies **four statements that require finite computations** at the
start of Appendix A. The table below tells you what is checked and where to find
the code. The mathematical arguments reducing the main theorem to these checks
are in the paper.

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

### What is inside the two proposition checks?

**Proposition 5.19** requires **42 positivity jobs**: 36 checks at the nonapex
vertices and six checks at the fan apex. Each job has its own
`verified_CELL_VERTEX.json` report in the [cover results directory](certificates/release/cover/).
The exact twelve-cell inputs are in [`data/cover.json`](data/cover.json).
The geometric covering check is recorded separately in
[`planar_coverage.json`](certificates/release/cover/planar_coverage.json).

**Proposition 8.4** includes the following two computations from Appendix A.3.
Both are performed by [`verify_family.py`](verification/family/verify_family.py).

| Appendix statement | What is verified | Relevant functions | Saved results |
| --- | --- | --- | --- |
| **Lemma A.6** (`appA3:hess`) | The Hessian is positive definite throughout the neighborhoods of both moving zero patterns, uniformly in L. | `local_check()` and `subdivide('local', ...)`; matrix formulas and tests in `core.hessian()` and `core.positive_definite()` | [`local1.json`](certificates/release/family/local1.json), [`local2.json`](certificates/release/family/local2.json) |
| **Proposition A.5** (`appA3:compact`) | Nonnegativity and the exact zero set throughout L ∈ [3.9, 9.5] and 0 ≤ q₃ ≤ q₂ ≤ q₁ ≤ 12. | `subdivide('compact', ...)` and `core.compact_test()` | [`compact.json`](certificates/release/family/compact.json) |

The family verifier also checks the symbolic identities and the numerical
inequalities used in the paper's reduction from the unbounded domain to this
compact region. See the [family guide](verification/family/README.md) for details.

## Reproduce all checks

After cloning or downloading this repository, open a terminal in its directory:

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py --jobs 2
```

Use Python 3.11 or newer; the recorded run used Python 3.14. The dependency
versions are pinned in [`requirements.txt`](requirements.txt).

The last command runs **all four groups above**, together with additional
consistency checks. It creates a new directory under `results/`, containing a
`run.json` summary, detailed reports, and logs. A successful full run ends with:

```json
"status": "complete"
```

Any unresolved box, exhausted search budget, or failed inequality prevents this
success status. Saved reports are not used to bypass computations. Do not use
`python -O`, `python -OO`, or `PYTHONOPTIMIZE`, which disable assertions.

For a short installation/preliminary check, use `python verify.py --quick`.
**Quick mode does not verify the full positivity statements.**

## Results of the recorded run

The [full run report](certificates/release/run.json) records a successful run in
**293 seconds** on the recorded environment. All **42 cover jobs**, both family
Hessian checks, the full family compact-domain check, and the additional
single-apex check finished with **zero unresolved boxes**. Runtime and node
counts may differ on another machine.

The reports include source and input hashes so the results can be traced to the
exact files used. The independent [manuscript input comparison](certificates/manuscript-table-match.json)
confirms that all twelve cells match the paper's tables.

## Further details

- **How the numerical bounds are rigorous:** the programs use FLINT/Arb interval
  enclosures and exact rational geometry. Floating-point proposals are accepted
  only after validated arithmetic checks. See the [cover guide](verification/cover/README.md)
  and [family guide](verification/family/README.md), including the documented
  differences between the implementation and the paper's presentation.
- **Additional checks:** [`verification/apex/`](verification/apex/) checks the
  single crossing-point certificate separately. It is an extra check, not a
  substitute for Proposition 8.4. [`check_fail_closed.py`](verification/check_fail_closed.py)
  deliberately tests failure cases, and [`audit_family_runtime.py`](tools/audit_family_runtime.py)
  checks the runtime formulas symbolically. See [AUDIT.md](AUDIT.md).
- **Comparing a later paper draft:** run
  `python tools/compare_draft.py /path/to/arxiv_v1.tex` to compare the exact
  certificate tables. Introductory prose edits do not change these inputs.
- **Scope:** this repository supplies the computational part of the proof. The
  graphon arguments, analytic reductions, and external Kwan–Pham theorem are
  supplied by the paper and its references. It is not a proof-assistant
  formalization of the whole paper.

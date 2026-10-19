# The Sparse Triangle Lower Tail: computational verification

This repository contains the numerical verification used in **The Sparse Triangle
Lower Tail: Threshold and Minimizers**, by Dong Huang and Shuangping Li.

The paper identifies **four statements that require finite computations** at the
start of Appendix A. The table below tells you what is checked and where to find
the code. The mathematical arguments reducing the main theorem to these checks
are in the paper.

A bounded CPU verification job is also deployed on Yale Bouchet. See
[`hpc/`](hpc/README.md) for the runner and
[deployment record](hpc/bouchet-run-20261019.json). Submission is not evidence
that the remote checks have passed.

## Lean 4 progress toward the main theorem

A partial Lean formalization is now in [`lean/`](lean/README.md). **Theorem 1.3
(`thm:main`) has a checked conditional assembly but is not yet fully proved in Lean.** The Python verification
and the Lean formalization have different scopes.

| Status | Progress |
| --- | --- |
| Proved in Lean | Entropy and triangle integrability, basic bounds, and invariance under changes on null sets. |
| Proved in Lean | Balanced SBM cost/density formulas for arbitrary measurable equal partitions, existence of a balanced minimizing pair, and **V(r) ≤ V_SBM(r)**. |
| Proved in Lean | Full balanced phase classification (`cor:Vbal`), including stationary branch, unimodality, actual inverse branches, unique crossing, and identification with the supremum threshold. |
| Proved for unrestricted graphons | Active constraint (`lem:active`); strict improvement below the threshold and exclusion of all constant minimizers there (`thm:threshold`(iii)). |
| Proved from a named external input | The full supporting range 0 < r ≤ r_−, value equality and optimizer data follow from the explicit KP26 input. |
| Conditional main theorem | The actual graphon continuation and final theorem assembly compile. Two internal inputs remain: critical classification (cover/apex certificates) and the compact intermediate certificate family. |
| Proved in Lean | Complete coefficient signs and value/derivative tangencies (`lem:certcoef`), including analytic substitutions and the required log 40 bounds. **Global certificate positivity remains unproved.** |
| Proved in Lean | All printed threshold/parameter intervals (`lem:digits`); scaling, truncation and rescaled first variation; the graphon certificate expectation identity; scalar two-block rigidity. |
| Proved in Lean | Full Euler–Lagrange proposition (`prop:euler`): positivity, unique positive multiplier, and quantitative graphon bounds. Sharp Bregman/mean-gap estimates and downward propagation (`lem:push`). |
| Proved with an unproved internal hypothesis | The full threshold theorem follows from `CriticalClassification` (`prop:critical`). That critical classification remains to prove; it is not an external assumption. |
| Proved relative to classical sampling | Vertex identity, sharp support bounds, and classification of every already-two-block minimizer (`prop:vertex`, `cor:bipodalmin`), in measurable-partition form. |
| Proved in Lean | Value continuity; quantitative isolation, variance/entropy and Goodman bounds; the full boundary comparison (`lem:boundary`); triangle-pattern-to-partition rigidity. |
| Proved relative to named classical inputs | Unrestricted minimizer existence and entropy lower semicontinuity; balanced partition/pullback equivalence; minimizer, cost, mean and multiplier convergence in cut distance. |
| Proved in Lean | Critical parameter region; actual triangle-law symmetry and Hoeffding decomposition; certificate expectation/weak duality and parameter concavity; full scalar penalized classification and values. Relaxed-law validity uses classical sampling. |
| Proved relative to classical sampling | Full insertion lemma: every minimizer row globally minimizes its row functional. The penalized mean-zero L² quadratic inequality is also proved. The complete functional two-well theorem is proved without external inputs. |
| Proved in Lean | Complete local rigidity (`thm:rigidity`), including measurable row classes, uniform approximation, exact row identification and bijective relabeling transfer, relative only to classical sampling. |
| Proved relative to named inputs | Full small-target theorem (`thm:smalltail`): every minimizer is the balanced branch, and conversely, for all 0 < r ≤ r_−. The proof derives bipodality from actual rows. |
| Proved with explicit classical spectral input | Centered-kernel positivity, trace/diagonal and degree estimates, exact cubic identity and spectral tail inequalities. The graphon-specific estimates are proved here. |
| Proved in Lean | The actual twelve-cell geometric cover, all 179 curved-boundary checks, and every support cutoff. Nonlinear certificate positivity remains separate. |
| Partially checked | Actual S1 vertex-0 positivity on near-one, tail and a seventeen-leaf Taylor slab. Family local Hessian/contact calculus and exact parameter-to-coefficient enclosures are proved. Five exact interval leaves prove local nonnegativity and the unique AAA zero in a logarithmic cube of radius 0.1 for every L in [3.9,9.5]. Full-domain cover/family certificates remain unfinished. |
| Proved relative to named inputs | All small-parameter bounds, actual row reduction and scalar exclusion (`lem:smallparams`, `lem:rowreduction`, `lem:scalar`). Exact small-target block rigidity and the full classification are now proved. |
| Proved relative to named classical inputs | Sequential stability and openness of the balanced-classification region. The left seed follows conditional on the still-unproved critical certificate. |
| Proved in Lean | Exact tangency coefficients for all six fan cells: one certified common determinant, unique corrections in the four missing slots, and zero values/gradients at both contacts. Positivity remains separate. |
| Proved in Lean | All twelve apex contact neighborhoods (AAA and ABB for each fan F1–F6), at the full published radii: exact coefficient enclosures, positive shifted center Hessians, third-derivative bounds, nonnegativity and a unique contact zero. Global positivity outside these neighborhoods remains unfinished. |
| Partially checked | A shared verifier handles all 36 nonapex jobs with their actual coefficients; positivity is checked on the small logarithmic cube [0,1/512]^3. Full-domain positivity is still required. Refined kernel-checked constants and all 24 tangency coefficients remove the recorded precision obstruction at the diagnostic samples; full exterior coverage remains unfinished. |
| Remaining | Discharge the two internal certificate inputs: critical classification and the compact intermediate certificate. The final conditional continuation assembly is proved. |

The [formalization README](lean/README.md) records the file-to-paper mapping,
remaining dependencies, build instructions, axiom audit, and dated progress log.
The earlier **40–45% effort estimate** is subjective, not measured theorem
coverage. The completion gates below are the more useful progress record. [Proof issues](lean/PROOF-ISSUES.md)
distinguish missing formal proofs from suspected mathematical errors.
[Shorter proof notes](docs/PROOF-SIMPLIFICATIONS.md) collect complete replacement
arguments found during formalization, with stable manuscript labels and Lean links.
Current completion gates (only full imported Lean proofs count):

| Gate | Checked completion | What remains |
| --- | --- | --- |
| Main-theorem deduction from the two internal certificates | Proved | Supply both certificates |
| Critical classification: 36 nonapex full-domain jobs | 0/36 integrated | Full replays; complete search proposals for all 36 jobs are saved |
| Critical classification: six apex full-domain jobs | 0/6 integrated | All six full replays are running or queued; complete proposals are saved |
| Compact family: AAA neighborhood | Proved on the full parameter interval | None for this neighborhood |
| Compact family: ABB neighborhood and exterior | Neither full replay integrated | Both full replays running on Yale |

Search proposals, sample leaves, and job submissions are **not** completed gates.
The latest source milestone includes a generic full-domain nonapex replay generator;
its complete job-0 replay is running on Yale as job **30060676**. The bounded
search array **30060923** is exploring the other critical jobs, with at most
two single-CPU searches at a time. Full nonapex array **30061427** additionally
checks jobs 1–4 and 6, with at most four jobs running together. Thirteen search
results from Yale have been downloaded, checked for complete subdivision geometry,
and saved with source/hash provenance. None of these submissions or search
results is counted as a proof. Three smaller complete regions (jobs 24–26)
were submitted as **30062473**. Fourteen more completed proposals are queued
as **30062736**, dependent on the first full array ending, to keep concurrency
bounded. Searches 14 and 15 finished after resumption as **30062715**; their
full replays are queued as **30062956**, behind the smaller-region array.

Complete proposals for all **42 critical-region jobs** are now saved with
[raw search provenance](hpc/bouchet-complete-searches-20261019.json). Their
subdivision geometry has been parsed locally; this does not establish positivity.
Full apex array **30064252** checks fans F2–F6 with at most two concurrent
eight-CPU jobs. The existing full F1 run remains separate.

Latest apex progress: a complete F1 subdivision is proposed, and five representative
leaves plus the sorting/zero-pattern assembly pass Lean. **The full F1 replay is
still pending**, so this does not close the critical certificate.

Latest family progress: a complete 108,452-box ABB neighborhood subdivision
is proposed for every L in [3.9,9.5]. Lean checks the scaled-Hessian verifier,
four-dimensional coverage theorem, moving-contact bridge and two selected
boxes. **The full ABB replay remains pending.** See the
[dated progress record](lean/README.md#2026-10-19--full-abb-proposal-and-checked-scaled-hessian-replay).

The actual parameter-derivative chain and the paper's signed Taylor lower
bound are now proved in Lean. A kernel-checked sample encloses all seven
coefficient derivatives through order three on L ∈ [3.9, 2503/640].
The gradient parameter bound and complete analytic exterior Taylor inequality
also compile, including all three scalar quadratic bounds used in the paper.
The numerical leaf checker now proves positivity throughout one full box,
L ∈ [39/10,2503/640] and each qᵢ ∈ [0.99,1.01], with a checked margin
greater than 1/1000. A complete 64,646-leaf subdivision is now proposed and
passes exact Python consistency checks. Lean proves the general assembly,
including the equality cases after sorting, but **the full numerical replay
is still missing**. A generated test now checks 14 actual leaves, all leaf
types and quadratic choices, and one complete small subtree. Contact and
coverage conclusions still require the internal ABB local theorem. The
proposal is not a completed formal certificate.

The exact 36-job nonapex and six-fan apex results now have a direct checked
assembly into critical classification. Sharper interval bounds are available
for every nonapex job. The endpoint checker also covers all cell cutoffs,
including B1/B2 beyond 16, through a proved scale-32 alternative. **These
reductions do not discharge the full numerical jobs.**

The target statement quantifies over all measurable graphons, not just SBMs.
At the authors' request, external/classical results may be explicit hypotheses;
[ASSUMPTIONS.md](lean/ASSUMPTIONS.md) distinguishes those inputs from our own
unproved obligations. The [stable-label proof map](lean/proof-map.json) and
[change-checking instructions](lean/README.md#stable-links-to-the-manuscript)
keep the code linked to the paper when its statements or numbering change.
The log also records a [survey of graphon/cut-norm libraries](lean/README.md#2026-10-19--graphon-library-survey-user-suggestion), including a promising existing compactness development; no external library has yet been imported.

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

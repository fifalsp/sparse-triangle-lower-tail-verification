# Lean verification

Updated October 26, 2026.

The full combined project built **94,032 modules**, and its original namespace
audit passed **10,450,946 theorems** with only `propext`, `Classical.choice`,
and `Quot.sound`. All source hashes are unchanged.
[Build and audit record](../hpc/results-20261026-combined-completion/completion.json).

The development covers the authors' variational and probabilistic arguments.
Cited external and standard classical results are explicit hypotheses, listed
in [ASSUMPTIONS.md](ASSUMPTIONS.md). The
[proof map](proof-map.json) has 112 manuscript labels and 1,080 declaration
links. The [latest manuscript review](manuscript-review-20261026-v2.json)
reconciles all changed statements and proofs with the existing Lean results;
the original textual baselines are preserved. The
[source numbering record](../data/manuscript-numbering-20261026.json) covers all
95 numbered results. The main variational theorem is **Theorem 1.3**;
the rate and structure results are **1.1–1.2**, and the reduction is **A.1**.

## Verified proof components

| Component | Checked result | Evidence |
| --- | --- | --- |
| Graphon foundations | Existence, lower semicontinuity, cut estimates, bijective compactness, relabeling and near-minimizer stability | [Kernel/cut review](data/kernel-cut-check.json), [variational review](data/section02-variational-review-20261020.json), [stability](data/near-minimizers-check.json) |
| Probabilistic reduction | Sparse entropy comparison, finite conditional-law entropy, Harris deductions, triangle decorrelation, cut concentration and discrete variational convergence | [Reduction](data/conditioned-structure-check.json), [decorrelation](data/decorrelation-check.json), [discrete comparison](data/discrete-comparison-check.json) |
| Rate and conditioned structure | Log-probability rate, proximity to minimizers, matrix rounding and phase deductions from the classification | [Rate](data/lower-tail-rate-check.json), [rounding](data/rounding-check.json), [phases](data/conditioned-phases-check.json) |
| Variational analysis | Euler equation, multiplier bounds, two-block relabeling, scalar phase classification and unique penalized crossing | [Analytic review](data/analytic-review-check.json), [phase review](data/final-manuscript-review-check.json) |
| Printed constants | Current threshold bracket of width 2×10⁻²⁵, all four parameter ranges and all five penalized coexistence brackets | [Threshold digits](data/manuscript-digits-check.json), [penalized digits](data/penalized-digits-check.json) |
| Certificate identities | Coefficient determinant and uniqueness, original contact equations, support identities, triangle patterns and critical apex law | [Coefficient review](data/certificate-uniqueness-check.json), [patterns](data/patterns-check.json), [apex](data/critical-apex-check.json) |
| Numerical proof machinery | Polygon fan, box lower bounds, cubic Taylor remainder, interval Cholesky and replay coverage | [Fan](data/polygon-fan-check.json), [box bounds](data/box-lower-bounds-check.json), [Taylor](data/taylor-cube-check.json), [Cholesky](data/cholesky-check.json) |
| Full critical-region replays | All 36 nonapex regions and all six apex fans: **42 of 42** | [Regional builds and audits](../hpc/results-20261021-0620/verified-regions.json) |
| AAA neighborhood | Hessian positivity, nonnegativity and the unique contact zero over the full parameter interval at the exact manuscript binary64 radius | [AAA radius proof](data/family-binary64-radius-check.json) |
| Exterior compact-domain replay | Full 64,646-leaf table; 12,872 modules and unchanged audit passed | [Full exterior replay](../hpc/results-20261021-0635/exterior-completion.json) |
| ABB logarithmic neighborhood | Nonnegativity and unique contact zero on the full radius-1/10 cube; 7,462 modules and unchanged axiom audit passed | [Full ABB replay](../hpc/results-20261021-0635/abb-completion.json) |
| ABB radius extension | Quantitative Hessian perturbation, retraction and padded-interval transfer; all 21 test leaves, including a complete 20-leaf subtree, pass the new checks | [112 declaration audits](data/family-hessian-perturbation-check.json) |

## Completed integration

The full padded ABB replay at the exact binary64 radius and its joint import
with every regional and family certificate passed the combined build,
unchanged source-hash checks and original axiom audit in Yale job **30819618**.

[MainReplayAssembly.lean](SparseLowerTail/MainReplayAssembly.lean) proves the
main variational theorem from explicit critical and compact-family
certificates. [MainStatement.lean](SparseLowerTail/MainStatement.lean) gives its
statement over all measurable graphons. The
[manuscript inventory](manuscript-coverage.json) and
[cluster record](../hpc/README.md) record their discharge. The
[generated aggregate](../hpc/results-20261026-combined-completion/CompletedReplays.lean)
is byte-identical to the source in the accepted manifest and supplies all
internal finite premises. Its main theorem retains seven named external and
classical inputs.

## Build and audit

Install `elan`, then run from this directory:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build SparseLowerTail
LEAN_NUM_THREADS=1 lake env lean Audit.lean
```

Lean and Mathlib are pinned to **4.24.0**. The root imports the completed local
proofs and checked test replays. Regional archives have their own full-target
builds and audits; the final combined target is generated by
[assemble_replays.py](../hpc/assemble_replays.py).

To repeat the new ABB radius checks:

```sh
python3 tools/generate_family_abb_radius_replay.py
LEAN_NUM_THREADS=1 lake build SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke.CheckedSubtree
LEAN_NUM_THREADS=1 lake env lean tools/audit_family_hessian_perturbation.lean
```

The generator reuses the original endpoint certificates and subdivision. Lean
checks the padded row margins, coefficient bounds, contact bounds and analytic
transfer. Its full mode is prepared for the completed ABB source replay.

From the repository root, check manuscript links with:

```sh
python3 tools/check_lean_map.py
```

Historical checks are retained in [data/](data/) and Git history.


## Historical laptop replay

The F1 sample checked 47 leaves and a complete 11-leaf subdivision under a
one-worker, one-thread, 8 GiB Lean memory cap. The
[record](data/compact-conclusion-laptop-pilot-check.json) also checks the
literal Proposition A.5 deduction from the remaining finite family replay.

The duplicate laptop worker is permanently retired; its cached work is
retained. The earlier command is recorded here for reproducibility and should
not be restarted for this verification:

```sh
python3 hpc/run_laptop_replay.py SparseLowerTail.Section05.ApexReplay.F1.FullCube --logs results/laptop-f1 --hours 24
```

The runner uses low priority, checks the full target, applies the unchanged
axiom audit, and verifies that its proof sources did not change during the run.
It allows one laptop runner at a time. Build logs retain partial progress if
the time or memory limit is reached.

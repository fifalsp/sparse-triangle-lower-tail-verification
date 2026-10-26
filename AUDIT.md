# Verification review

The release was traced from the Overleaf manuscript rather than from the older
broad investigation archive. The latest reviewed main source is
*The Lower Tail of Triangle Counts in Sparse Random Graphs*, `arxiv_v2.tex`,
SHA-256 `db811b1ff857dbbf8ba8d87b3ebd3e40bc62c61ce4753da54698f4dc95c32fa1`.
The [current review](lean/manuscript-review-20261026-v2.json) reconciles the
revised statements, proofs and numbering while preserving the original proof-map
baselines.

The full combined Lean target and original namespace audit passed in Yale job
30819618: 94,032 project modules and 10,450,946 theorems, unchanged source hashes,
and only `propext`, `Classical.choice` and `Quot.sound`.
[Checked build and audit evidence](hpc/results-20261026-combined-completion/completion.json).
All internal finite premises are discharged; the documented external and
classical results remain ordinary explicit hypotheses.

The current twelve-cell inputs match the historical endpoint rebuild exactly:
all 144 coefficient slots (including the 24 slots defined by exact linear
solves), vertices, multipliers, support bounds, targets, and radii agree.
`tools/compare_draft.py` independently parses the manuscript tables and checks
that match. It supports the current three coefficient tables and the earlier
two-table layout.

The current draft adds the full parameter-family statement. The standalone
crossing-point apex check from the older notes is retained only as an additional
special-case check. It is not substituted for the family computation.

Separate cooperative agents reviewed the input mapping, endpoint code, and
family implementation. The review checked the sorted-domain covering invariant,
interval enclosures, local-neighborhood tests, parameter Taylor remainders,
certificate scaling, and fail-closed exits. The family review also applied a
symbolic arithmetic adapter to the actual runtime functions, proving the jet
product, quotient and exponential recurrences; all 21 weight derivatives; and
all nine entries of both the ordinary and scaled Hessians. This optional check
is shipped as `tools/audit_family_runtime.py`.

For the standalone Python checks, the arithmetic package's inclusion guarantees,
Python execution and symbolic algebra engine remain trusted software. Those
reviews do not formally verify that software. The separate completed Lean
development replays the certificates and proves the analytic and probabilistic
deductions under its stated external hypotheses and audited foundations.

Release safeguards include refusal of optimized Python, strict checks at the
published local radii, explicit printed-constant enclosures, exact regeneration
of derivative templates, fresh output directories, source/input digests, and
nonzero exits for unresolved boxes. Negative controls deliberately exhaust
the node budgets and disable assertions; these runs must be rejected.

The full replay reports and command logs are included in `certificates/release/`.
Their run manifest identifies the exact source and input versions used.
Node counts and subdivision digests can vary with platform-dependent numerical
proposals; every accepted inequality must still pass the validated arithmetic
test. A new run must complete independently rather than trust the recorded
status fields.

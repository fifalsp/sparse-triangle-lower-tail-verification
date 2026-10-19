# Verification review

The release was traced from the current Overleaf manuscript rather than from
the older broad investigation archive. The current source is *The Sparse
Triangle Lower Tail: Threshold and Minimizers*, SHA-256
`84c55a798a1fc1492f319179eec89f340d27269916acd622d54707da185e17b7`.

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

The arithmetic package's inclusion guarantees, Python execution, and the
symbolic algebra engine remain part of the trusted software. The separate
reviews and successful computations are not a formal verification of that
software or of the paper's analytic arguments.

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

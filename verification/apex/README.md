# Apex inequality

This module checks the historical Proposition `prop:apex-ineq` from the earlier
notes. In the current Overleaf manuscript, the corresponding statement is a
single-parameter case of Proposition `prop:family`. This extra check does not
replace the required uniform family verification over `L` in `[3.9,9.5]`.
It reuses elementary formulas from the recorded investigations and runs the
single-parameter verification specified in those earlier notes: `Q=53`, local radii
`0.03` and `0.002`, and strict target `1e-12` outside the local neighborhoods.
The decimal radii and target are interpreted as exact binary64 inputs, as in
those notes. The crossing bracket is exact decimal rational data and is also
the bracket in the current manuscript.

From the repository root:

```sh
python verification/apex/symbolic.py
python verification/apex/verify_apex.py --quick
python verification/apex/verify_apex.py
```

The symbolic command proves the five exact value/gradient identities and the
closed coefficient formulas, plus the exact gradient, Hessian, and congruence
identities used by the interval checker. The quick command validates the crossing bracket,
the four-by-four ball solve, coefficient signs, the analytic tail bound, and
positive definiteness of the Hessian on both local boxes. This full-box test is
a stronger alternative to the earlier notes' center-Hessian plus third-derivative
Taylor test; the printed neighborhoods and certificate are unchanged. It is **not** the
remaining compact-domain verification. The final command covers the ordered
cube `0 <= q2 <= q1 <= q0 <= 53`, using symmetry, direct interval bounds and
first/second-order Taylor bounds. Positive definiteness is checked using strict
Arb pivots after an exact fixed congruence. No floating-point sign proposal is
used as proof. All three Python modules reject optimized execution (`-O`,
`-OO`, or `PYTHONOPTIMIZE`) because it would disable assertions.

For the local argument, write `q=P+v` at one of the two exact zeros. Tangency
gives `Phi(P)=0` and `grad Phi(P)=0`, so Taylor's integral formula is
`Phi(P+v) = integral_0^1 (1-t) v^T H(P+t v) v dt`. The segment remains in the
checked box. A positive definite Hessian at every point of that box makes the
integral strictly positive for `v != 0`. The code checks this property after
the fixed invertible change of basis with columns `e1`, `e2-e3`, `e2+e3`;
strict interval LDL pivots imply positive definiteness by congruence.

The default full run has a node budget of two million. An unresolved box or
exhausted budget produces `status: incomplete` and a nonzero exit code. Increase
`--max-nodes` if necessary. Reports are written to `results/apex/`; use
`--output-dir` to select a different location. No source, certificate input, or
historical report is overwritten.

`provenance.json` records original script hashes. `core.py` retains the formula
functions from the original broader family verification. `symbolic.py` removes
that program's old write-beside-source behavior. `verify_apex.py` is a new,
self-contained replay of the earlier notes' stated data. A successful quick report
must never be described as a completed global positivity verification.

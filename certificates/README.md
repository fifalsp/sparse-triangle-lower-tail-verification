# Recorded verification results

`release/` is the unmodified output of a fresh `python verify.py --jobs 2` run.
The top-level `run.json` has status `complete` and binds the combined runner's
source/input files and numerical reports by SHA-256. The 42 cover jobs and all
three family searches finished with zero pending boxes. Command logs are
included under `release/logs/`.

`manuscript-table-match.json` records the independent exact comparison with the
current Overleaf source snapshot. `family-runtime-audit.json` records the
additional exact symbolic audit of the actual runtime functions. Neither report
is used as an input by the positivity searches.

These files document a completed run. To reproduce the computational claims,
run the code yourself; the verifier creates a new results directory and does
not trust these saved status fields. Runtime, node counts and partition digests
can vary with platform and numerical proposals while all rigorous tests remain
mandatory.

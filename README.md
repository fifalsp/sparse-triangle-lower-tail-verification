# Sparse triangle lower tail: verification code

Reproducible computational checks for *The Sparse Triangle Lower Tail: Threshold and Minimizers*
by Dong Huang and Shuangping Li, from the Overleaf project
`large_deviation_lower_tail`. The source snapshot is identified by SHA-256 in
[`data/manuscript.json`](data/manuscript.json). The manuscript itself is not
distributed in this code repository.

The current manuscript identifies four computer-assisted assertions:

| Manuscript label | Check | Code |
| --- | --- | --- |
| `lem:digits` | Crossing bracket and the four printed enclosures | `verification/cover/endpoint_common.py` |
| `lem:penconstants` | Penalized coexistence constants | `verification/cover/verify_penalized_constants.py` |
| `prop:cover` | Twelve-cell cover, support bounds, exact tangency solves, and 42 positivity jobs | `verification/cover/` |
| `prop:family` | Certificate family on the parameter interval, including local Hessians and compact-domain positivity | `verification/family/` |

The additional `verification/apex/` module verifies the single crossing-point
certificate separately. It also checks exact symbolic identities used by the
family. It is useful as an independent special-case check, but does not replace
the parameter-family verification.

The recorded full release run passed in 293 seconds on the recorded environment:
all 42 cover jobs, both family Hessian checks, the family compact-domain check,
and the additional apex check completed with zero unresolved boxes. See
[`certificates/release/run.json`](certificates/release/run.json) for the source
hashes, dependency versions, commands, and individual reports. The independent
input comparison and runtime-formula audit are also stored under `certificates/`.

## Run the checks

Use Python 3.11 or newer. The recorded release run uses Python 3.14; dependency
versions are pinned to the versions used in that run.

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python verify.py --jobs 2
```

Each run creates a fresh directory under `results/` with `run.json`, detailed
JSON reports, and command logs. A completed full run ends with
`"status": "complete"`. An unresolved box, exhausted node budget, failed
inequality, changed input, or subprocess error prevents this success status.
The output directory cannot be reused, so old reports cannot silently supply
missing checks. Source and input hashes are recorded in the run manifest.

For preliminary checks only:

```sh
python verify.py --quick
```

The quick command does **not** verify the global positivity statements. Its
status is `quick_checks_passed`, never `complete`. Do not run verification with
`python -O`, `python -OO`, or `PYTHONOPTIMIZE`: assertions are verification
conditions, and optimized modes are explicitly rejected.

The failure controls can also be run separately:

```sh
python verification/check_fail_closed.py
```

An additional independent symbolic check applies exact arithmetic to the actual
family runtime functions, checking their Taylor recurrences, weight derivatives,
and Hessians:

```sh
python tools/audit_family_runtime.py
```

## Inputs and arithmetic

[`data/cover.json`](data/cover.json) contains the twelve cells. Each printed
binary64 input is stored as its exact rational value; the support bounds
`Q=N/1024` are exact rationals. The 24 starred coefficient slots are solved
from exact tangency conditions with validated ball linear algebra. They are
not replaced by rounded decimal approximations.

The release uses FLINT/Arb ball arithmetic for numerical inclusions and exact
rational arithmetic for planar geometry. NumPy supplies candidate eigenvalue
bounds or support points in the cover code; every acceptance condition is
then checked with Arb. SymPy generates exact derivative templates and checks
the symbolic identities. A template regeneration check compares the generated
source with the shipped file before positivity checks run.

The cover templates evaluate `3*Psi`, and the numerical positivity targets
are multiplied by three accordingly. Local neighborhoods are checked using
the radii printed in the manuscript. See the module READMEs for the precise
local and Taylor tests and their relationship to the manuscript's presentation.

To compare the certificate tables with a later manuscript export:

```sh
python tools/compare_draft.py /path/to/arxiv_v1.tex
```

This checks the exact table data; it is not an audit of changes to the surrounding
mathematical argument. The original research code and historical reports were
traced before packaging. Their source hashes and the portable changes are
recorded in the provenance files. The release reports are fresh computations
from this repository, not relabeled historical output.

## Scope

These programs verify the finite computational assertions used by the paper.
The graphon arguments, analytic reductions, equality arguments, and external
Kwan–Pham theorem remain mathematical inputs supplied by the manuscript and
its cited references. This is a computer-assisted verification package, not
a proof-assistant formalization of the full theorem.

Exploratory optimization, dense-case investigations, unrelated notes, and
manuscript drafts are outside this repository. Generated working results are
ignored by Git; the designated release reports are stored under `certificates/`.

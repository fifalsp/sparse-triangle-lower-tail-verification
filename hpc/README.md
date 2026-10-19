# Running the Lean checks on Yale Bouchet

The first job builds the committed Lean root on Linux, runs `Audit.lean`, and
independently recomputes the 40 refined apex matrix/right-hand-side intervals.
This is a remote replay and benchmark, not completion of the main theorem.

It requests one CPU node, 8 CPU cores, 64 GiB RAM and at most four hours in the
`day` partition. No GPU or paid priority tier is requested. Compilation runs
inside a Slurm allocation, not on a login node.

Use a Git source archive of a checked commit, with its full revision recorded in
`SOURCE_COMMIT`. Do not upload local `.lake`, toolchains, authentication files,
or unrelated manuscript folders. The source archive does not need GitHub
credentials on the cluster. Its pinned Lake manifest downloads public mathlib
dependencies and their matching cache.

From the extracted repository root:

```bash
mkdir -p logs
sbatch --account=YOUR_ACCOUNT hpc/bouchet-bootstrap.sbatch
```

The script installs official elan into `../lean-runtime` if absent. It does not
change shell startup files, and it uses the repository's pinned Lean toolchain.
Only one job should bootstrap or build this shared checkout at a time.

Each run writes `logs/job-JOBID/`: source revision, host, timestamps, full build
and audit logs, timings and `exit-code.txt`. `SUCCESS.txt` appears only after all
three checks return success. A Slurm kill can prevent the EXIT trap, so also
check `sacct -j JOBID --format=JobID,State,ExitCode,Elapsed,MaxRSS`.

Keep source and logs in project storage and a separate copy off-cluster;
Yale documents that project storage is not backed up. Scratch is temporary and
subject to Yale's purge policy. Keep a single dependency cache and toolchain;
submit later certificate jobs against that prepared environment.

## Staged runner (preferred after the first storage test)

A trial source extraction on 2026-10-19 created only 42 files in 144 seconds
on project storage, with `tar` waiting on filesystem I/O. The staged runner
avoids the small-file workload on that filesystem:

```bash
sbatch --account=YOUR_ACCOUNT bouchet-staged.sbatch /absolute/source.tar.gz SHA256
```

Upload the script and source archive, then submit from their project directory.
It checks the archive hash, stages source/dependencies on the allocated node's
temporary disk (requiring at least 25 GiB free), runs the same three checks,
and saves a single results archive plus one reusable Linux dependency archive
back to the submission directory. A failed stage produces an error log rather
than a success claim. The source revision is recorded inside every result.

Do not run concurrent jobs that overwrite the same dependency archive. The
initial source snapshot is commit `543e02f7`; later proof additions can be
replayed using a fresh source archive and its SHA256. Temporary working files
are not a durable record; the results archive and original Git source are.

## Current deployment

The initial job `30048468` was cancelled after mathlib's downloaded static
curl failed with OpenSSL STORE errors. No Lean verification completed in that
run. Its diagnostic archive is a partial snapshot of the active log; see
`bouchet-run-20261019.json` for provenance.

The corrected runner loads Yale's `cURL/8.7.1-GCCcore-13.3.0` module. An HTTPS
request from the compute node returned HTTP 200 with normal certificate
validation. The runner and source archive checksums were verified before
submission. Replacement bootstrap job **30049190** and dependent S1 job
**30049194** use source commit `f038dc5269b16415d6e46270acaa8a04ddc8220e`.
The S1 job starts only if the bootstrap succeeds; neither submission is proof
of a successful build or certificate. Exact deployment hashes are recorded in
`bouchet-retry-20261019.json`.

Monitor through Bouchet Shell Access:

```bash
squeue -j 30049190,30049194
sacct -j 30049190,30049194 --format=JobID,State,ExitCode,Elapsed,MaxRSS
tail -n 20 /nfs/roberts/project/pi_sl3363/sl3363/sparse-lean-30049190.out
```

## Full S1 certificate workload

The staged runner accepts a third argument `s1`. This experimental workload
generates all 15,280 Taylor leaves, 385 geometric coverage chunks, their
positive-coverage assembly and a final full-edge-cube theorem for the **first
parameter vertex of S1**. It then runs the unchanged project axiom-audit policy
on that theorem's entire dependency closure. It is one of the 36 nonapex jobs;
it does not discharge the whole cover or the main theorem.

Submit with `--time=12:00:00` and `--dependency=afterok:BOOTSTRAP_JOB_ID`.
The Python/Lean computation has an internal ten-hour timeout to leave time
for logs and cache export. Dependency ordering prevents two writers to the
same cache. Generated sources are exported only after build and audit success;
failed builds retain their diagnostic logs in the results archive.

The proposal JSON and generators are untrusted inputs. A successful proposal
is never treated as a proof; all leaves, splitting geometry, table lookups
and final mathematical conclusions must compile in Lean. The standalone
full-cube wrapper has been checked with an explicit coverage hypothesis;
that template check does not establish the missing coverage theorem.

## Full F1 apex workload

The updated runner accepts `apex1`, with the same 12-hour allocation and
10-hour internal timeout as S1. It generates all 31,263 F1 leaves, checks the
exact subdivision coverage and full-cube nonnegativity/zero-pattern theorem,
then applies the standard axiom audit. Only a successful build and audit
produce `APEX_SUCCESS.txt` and the generated-source archive.

Use an `afterok` dependency on the bootstrap. The updated runner writes the
shared dependency archive only for `bootstrap`; S1 and apex jobs read it.
The previously submitted S1 runner still exports its cache atomically, so
readers see one complete archive. Source, logs and generated artifacts are
kept separate by job ID. The checked five-leaf smoke test is not a substitute
for the full replay. F1 is one of six apex fans; all 36 nonapex jobs and the
intermediate-family certificate remain separate obligations.

F1 job **30049908** was submitted on 2026-10-19 with dependency
`afterok:30049190`. The source archive and runner hashes passed verification
in the authenticated shell. See `bouchet-apex-20261019.json`; submission alone
is not evidence of a completed certificate.

The bootstrap subsequently reported exit code 0 with logs archived. Both
S1 (`30049194`) and F1 (`30049908`) were then observed RUNNING on compute
node `a1130u35n03`, each with eight CPUs. Their full certificate results
remain unverified.

At the next diagnostic checkpoint both batch jobs were still RUNNING (18m43s).
S1 had compiled its subdivision `Coverage` module, but its full positive
leaf replay was not complete. F1 had compiled `ApexCoverAssembly`; its full
replay remained pending. Both reported MaxRSS close to the 64 GiB allocation.
An extra `srun` monitoring step failed to create its cgroup with `Cannot
allocate memory`; the original batch jobs remained RUNNING and had empty
batch stderr at that check. Do not infer a failed or successful proof from the
monitoring step. Preserve the current jobs and consult `sacct` before restarting.

## Full intermediate-family ABB neighborhood

The new `familyabb` workload checks the full logarithmic ABB contact cube of
radius 1/10 for every L in [3.9,9.5]. It generates the 108,452-leaf proposal with
93 shared parameter certificates and shared exponential endpoint certificates.
The build driver processes the actual import graph with at most two Lake
processes and two Lean threads per process. Request four CPUs and 64 GiB; the
job uses the same 10-hour internal timeout and 12-hour allocation limit.

Unlike the earlier aggregate builds, generated leaf modules cannot all start
at once. A 21-leaf test, including a complete small coverage subtree, passes
the bounded builder locally. This is evidence about the runner and replay
interface, not proof of the whole neighborhood. A successful full run must
produce `FAMILY_ABB_SUCCESS.txt` after the exact final theorem and axiom audit.
The exterior family certificate remains a separate obligation even on success.

Full ABB job **30052586** was submitted on 2026-10-19 from checked source
commit `7bbeae831aec605a701697dcb233c0e35be137e9`. Both uploaded SHA256
checksums matched. The allocation requests four CPUs and 64 GiB for up to
12 hours and excludes `a1130u35n03`, where the earlier memory-heavy jobs run.
See `bouchet-family-abb-20261019.json`. Submission is not proof of completion.

The scheduler then reported ABB **RUNNING** on `c1104u05n03` at 53 seconds;
the source checksum passed and dependency-cache restoration had started.
S1 and F1 were still RUNNING on their original node at 31m50s.


## Compact-family exterior workload

`bouchet-family-exterior.sbatch` is prepared for the complete 64,646-leaf
ordered compact-family proposal. It uses four CPUs, 64 GiB, two bounded build
workers and a ten-hour internal timeout inside a twelve-hour allocation.
It checks all exact subdivision tables and numerical leaves, then runs the
unchanged axiom-audit policy. **Even a successful exterior job leaves the
internal `FamilyABBLocal` premise to be discharged by the separate ABB job.**
The remaining critical classification is a different obligation again.

The new runner saves generated exterior sources and project build artifacts
on normal exit, including a controlled timeout, to a job-specific checkpoint
archive. This avoids discarding completed compilation when a long replay
needs another allocation. A checkpoint is not a success flag. A scheduler
kill can still prevent the exit trap; inspect the recorded job state and logs.
No new dependency cache is duplicated on the desktop. The full workload
has not yet been submitted at this preparation checkpoint.

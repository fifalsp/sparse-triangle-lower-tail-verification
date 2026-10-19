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
No new dependency cache is duplicated on the desktop. Full exterior job **30056868** was submitted from checked commit
`a9491f266af497c523e6dffabd02b08f558af248` after both uploaded SHA256
checksums matched. See `bouchet-family-exterior-20261019.json` for provenance.
Submission is not a completed certificate.

## Generic nonapex replay and bounded search

`bouchet-cover-job.sbatch SOURCE_ARCHIVE SHA256 JOB_INDEX` runs the complete
nonapex job (0..35), using a complete proposal included in that source archive.
It generates the full Lean replay, builds with two workers, audits axioms,
and saves project artifacts on controlled exit. A checkpoint is not a success
marker. Only `COVER_JOB_SUCCESS.txt` after the full build and audit reports a
finished individual job; the main theorem still needs the other jobs.

`bouchet-certificate-search.sbatch SOURCE_ARCHIVE SHA256` is a lighter array:
tasks 0..35 search the nonapex jobs; tasks 36..40 search apex fans F2..F6.
At most two tasks run at once, each with one CPU, 4 GiB RAM, and a two-minute
search budget. Every task archives its proposal, unresolved frontier if any,
source commit, and log. No Lean installation is needed for this search-only
job, and no result from it is accepted as a formal proof.

`bouchet-cover-array.sbatch SOURCE_ARCHIVE SHA256 SEARCH_RESULTS_DIRECTORY`
replays completed nonapex proposals from a search array. It requires the
search results and source archive to record the same source commit, saves the
input hashes, and preserves the actual proposal in the build checkpoint.
The initial array covers verified-complete proposals 1–4 and 6, at most four
jobs concurrently, each with four CPUs and 32 GiB RAM. Four single-thread
build workers keep process concurrency bounded. Future `--array` overrides
must name only completed proposals that have not already been submitted.
Neither queued nor running jobs count as completed formal proofs.


The initial full nonapex array was submitted as **30061427**. Tasks 1–4
were observed running and task 6 queued. Their replay source remains
`38d5c740`; the uploaded runner is from `46296bd`. See
[`bouchet-cover-jobs-20261019.json`](bouchet-cover-jobs-20261019.json).
Downloaded search results for jobs 0–12 are recorded in
[`bouchet-search-checkpoint-20261019.json`](bouchet-search-checkpoint-20261019.json).
Their geometry is complete, but their positivity is not yet a full Lean result.

## Bounded apex replay for all six fans

`run_apex_cluster.py --fan N --logs DIRECTORY --workers 4 --lean-threads 1`
checks a complete fan proposal. The runner now bounds concurrent builds and
works for every fan. The generator splits endpoint proofs into groups of 64
and numerical leaf proofs into groups of 16, so a single large endpoint module
need not hold up the whole fan. Every original inequality and coverage check
is retained. Incomplete or malformed proposals are rejected before generation.

`bouchet-apex-array.sbatch REPLAY_SOURCE SHA256 SEARCH_DIRECTORY SEARCH_COMMIT`
is prepared for fans 2–6, at most two concurrent jobs. The current runner
requests eight CPUs and 64 GiB per job and uses eight single-thread build workers.
The earlier staged `c8dc8f30` runner requested four CPUs; deployment records
identify the exact runner checksum used. The explicit search commit may precede the replay implementation;
both revisions and the actual proposal hash are recorded. The replay still
checks the actual fan cutoff, every numerical inequality, complete coverage,
and the unchanged axiom policy. Controlled exits preserve generated sources,
project build artifacts and the actual input proposal. **This apex array has
not yet been submitted.** The existing F1 job has not been restarted.


The bounded apex runner and source commit `c8dc8f30` are uploaded to Yale;
both remote SHA256 checks passed. They are staged, **not submitted**: the
F2–F6 searches must finish first. See
[`bouchet-apex-array-staged-20261019.json`](bouchet-apex-array-staged-20261019.json).
A measured full-job-3 batch checked 16 numerical boxes in 67 seconds; the full
job was still building with four workers. This single-batch timing is recorded
in [`bouchet-replay-timing-20261019.json`](bouchet-replay-timing-20261019.json),
and is not a reliable end-to-end extrapolation.

The portal's updated October 19 notice reports that Roberts is nearly full
and slowing file operations. Node-local compilation avoids its small-file
workload; initial archive staging and result export can still be affected.


Full nonapex array **30062473** was submitted for jobs 24–26 after all three
search archives reported complete subdivisions with no frontier (3221, 1903,
and 1729 nodes respectively). It uses the already verified `46296bd` runner
and `38d5c740` replay source, with two concurrent four-CPU jobs. These are
additional required regions, not replacements for the other pending jobs.

`bouchet-certificate-search-resume.sbatch SOURCE_ARCHIVE SHA256 PREVIOUS_RESULTS`
continues incomplete search archives on the same source revision. It verifies
the previous source, preserves the prior archive hash, and saves the extended
preorder and remaining frontier in a new array-specific result directory.
The default tasks are 14 and 15, with one CPU/4 GiB each and a ten-minute search
budget inside a fifteen-minute allocation. The original archives are retained.
A resumed search is still untrusted and must finish before full Lean replay.

A four-leaf local test of precomputed constant tables took 7.53 seconds versus
7.89 seconds for the existing checker, including startup. The exact environment
and margin equality compiled, but this small single-run difference does not
justify replacing live replays; the existing checker is retained.


The resumed searches were accepted as **30062715** after the uploaded runner's
SHA256 matched. See [`bouchet-search-resume-20261019.json`](bouchet-search-resume-20261019.json).
Full replay of fourteen further complete proposals (jobs 5, 7–11, 13, 16–22)
was submitted as **30062736**, with `afterany:30061427` and at most four
concurrent tasks. These independent regions can proceed after the current array
ends even if one of its jobs fails; any failed region still needs repair.
This dependency keeps the next wave from adding simultaneous proof workers.
No submission or queue state discharges a mathematical obligation.


Both resumed searches exited 0 with complete proposals and empty frontiers:
job 14 has 62,205 subdivision nodes, and job 15 has 72,687. Their full Lean
replays were then submitted as **30062956**, with `afterany:30062473` and at
most two concurrent tasks, using the resumed result directory. These larger
replays preserve compiled work on controlled timeout through the existing
checkpoint mechanism. Search completion is not formal certificate completion.


## Reusing completed proof modules

The bounded builder now asks Lake to validate existing compiled modules in
batches with `lake --no-build build`. A module file alone is never accepted:
the whole batch must pass Lake's freshness check, and the retained modules
must include every project dependency. Failed batches follow the usual bounded
build path. `--no-cache-precheck` restores the earlier scheduling behavior.
The final theorem build and axiom audit remain required.

A cached root check accepted all 351 project modules in 8.55 seconds. A mixed
check reused 141 modules and built one new module successfully. A deliberately
changed source was rejected with exit code 3, without modifying its compiled
artifact. Six regression tests pass; the unchanged mathematical root still
passes the standard axiom audit. This improves resumed/cached builds, not the
cost of a fresh numerical inequality. See
[`cache-precheck-validation-20261019.json`](cache-precheck-validation-20261019.json).

All 36 nonapex searches now have complete proposals. The last two full replay
waves are **30063319** (23, 27–29, 32–33) and **30063541** (30–31, 34–35),
both behind array 30062473 and each limited to two concurrent four-CPU tasks.
Together with the existing S1 run, every nonapex region has a replay running or
queued. This scheduling status is not proof completion. Resumed search array
30063138 completed jobs 30, 31, 34, 35 and fan F2; the remaining F4 search is
resumed as 30063538. All input/source details remain in the deployment records.

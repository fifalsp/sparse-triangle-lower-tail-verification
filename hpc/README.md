# Running the Lean checks on Yale and Delta

## Latest verified results — October 20, 2026

**39 full-region Lean builds and axiom audits have passed:** 34 nonapex
regions and apex fans F2, F3, F4, F5 and F6. The latest completion is F4, with
all 4,929 build tasks and its full declaration audit passed.
[Evidence](results-20261020-0238/verified-regions.json).

F4 completed after 9:06:47 on 8 cores, using about 35.4 GiB maximum RSS.
[F4 completion record](f4-completion-20261020.json).
The older Yale F1 and cover-12 jobs reached their 64 GiB memory limits;
both have queued recovery with 192 GiB.
[Failure and recovery record](yale-f1-failure-20261020.json).
The ABB job reached its ten-hour limit after 4,528 of 7,459 build tasks.
Its saved checkpoint is available to recovery. [ABB record](abb-timeout-20261020.json).
The exterior job reached its ten-hour limit after 11,755 of 12,872 build tasks.
Its 2.7 GiB checkpoint is saved. [Exterior record](exterior-timeout-20261020.json).
Cover 0 reached its ten-hour limit after 1,681 of 1,873 build tasks. Its
510 MiB checkpoint is saved. [Cover-0 record](cover0-timeout-20261020.json).
Recovery array `30068465` is waiting for Yale’s maintenance reservation to
clear; combined assembly `30068466` waits on that array. Completed F4 is
validated and skipped by recovery.

Delta job **23029964** replaces job `23029368`, which reached its setup
timeout while installing Lean on project storage. The replacement installs
Lean on node-local disk and retains sources and build artifacts in project
storage. [Recovery record](delta-recovery-20261019.json).
The [Delta runner](delta-replay.sbatch) checks the full F1 apex theorem with
four single-thread Lean workers. Its allocation is 16 CPUs, 30,000 MiB and
5.5 hours, capped at 88 CPU core-hours on `biah-delta-cpu`; 95 core-hours
were available before submission. The replacement remains pending for priority.

The approved Delta allocation now shows **500 CPU hours** in ACCESS. Current
source family jobs **23046543 (ABB)** and **23046544 (exterior)** are eligible
without user holds and are waiting for priority. Their combined cap is 360
allocation hours; including the two earlier jobs gives 454 hours. The two
superseded held copies were cancelled before starting.
[Deployment record](delta-family-deployment-20261020.json).

A full F1 laptop fallback started at 14:09 UTC with one low-priority worker,
one Lean thread and an 8 GiB cap. Its live status is
`results/laptop-f1-full-20261020/status.json`. This run is still in progress.

The current assembler imports the project root alongside all regional
certificates, so the combined build includes the latest author proofs.
[Seven runner checks passed](assembly-root-check-20261020.json). Queued job
`30068466` uses the earlier `98cbcb3` snapshot; latest-source integration follows.

## Yale setup and deployment history

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
project build artifacts and the actual input proposal. The array was submitted
as **30064252** from `fd69e283`; the existing F1 job has not been restarted.


The earlier bounded apex runner and source commit `c8dc8f30` were uploaded
and verified, but superseded before submission by the deployment below. See
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


## All critical-region search proposals saved

All 36 nonapex and six apex proposals now have complete subdivision geometry.
The original and resumed search archives are saved together as
[`search-results-20261019.tar.gz`](search-results-20261019.tar.gz), with input
hashes, source revisions, selected complete results and superseded frontiers in
[`bouchet-complete-searches-20261019.json`](bouchet-complete-searches-20261019.json).
Existing repository proposals were preserved when the complete geometry matched.
The proposal files are in `lean/data/`; geometry completeness is not positivity.

The F2–F6 complete archives were consolidated after checking source revision,
exit code, complete status and empty frontier. Full apex array **30064252**
was submitted from source **fd69e283** after both upload checksums matched.
It uses at most two concurrent eight-CPU, 64 GiB jobs, with eight single-thread
build workers per job and a ten-hour internal timeout. The current bounded
builder includes the tested cache precheck. Source, runner and input provenance
are recorded in [`bouchet-apex-array-20261019.json`](bouchet-apex-array-20261019.json).
The older F1 replay is unchanged. Full numerical builds and axiom audits remain
pending; no successful search or submission is counted as a formal certificate.


## Completed-region integration and ABB recovery snapshot

Nonapex job 25 passed its full-domain theorem build and axiom audit. Its
106 generated Lean sources exactly match regeneration, and the region-only
build cache was accepted locally without rebuilding. The root project now
imports the theorem through `CheckedCoverJobs`, which supplies completed
regions and asks only for the unfinished ones. See the checked results and
archive hashes in `bouchet-job25-completion-20261019.json`.

The older ABB allocation has a separate live snapshot on Yale:
`sparse-lean-abb-live-checkpoint-30052586.tar.gz` (reported 1.3 GiB).
The copy completed with exit zero while the build continued. It includes
generated full-region sources, project build artifacts and `SOURCE_COMMIT`.
This is only a recovery candidate: files captured during writes must be
revalidated, and the full theorem build and axiom audit remain mandatory.
No full ABB completion is asserted.


## CPU-time planning estimate (2026-10-19)

Budget roughly **1,000–2,000 additional allocated CPU core-hours** for the
remaining replay work, subject to revision as more full regions finish. This
is a planning range, not a measured remaining-work count or a deadline.
Job 25 used 1.64 actual CPU-hours and occupied 1.86 allocated core-hours for
952 boxes, including setup and final coverage/audit. Job 3's observed
partial throughput supports a similar order of magnitude. The proposals
contain 802,144 boxes across critical regions, ABB and the compact exterior;
their costs differ, and some work is already complete or in progress.

At the observed 68 allocated cores, the range corresponds to roughly
15–30 hours if parallelism is sustained. Queueing, uneven job lengths and
resumptions make **1–3 days** a more cautious elapsed-time allowance, assuming
no proof failures require changes. More CPUs alone do not guarantee this
speedup: memory pressure and sequential dependencies also matter. Raw
observations and caveats are in `compute-estimate-20261019.json`.


## Aggressive parallel scheduling (2026-10-19)

At the user's explicit request, the existing independent proof arrays were
released for concurrent scheduling. Throttles are now 14 for array 30062736,
2 for 30062956, 6 for 30063319, 4 for 30063541, 5 for 30061427, and 5 for
apex array 30064252. The four scheduling-only dependencies were removed.
Slurm confirmed each updated throttle and empty dependency. The total
eligible allocation rises from the observed 68 running cores to up to 200.
No running proof was restarted, and no duplicate replay was submitted.

If 200 cores are sustained, the 1,000–2,000 core-hour planning range means
5–10 ideal elapsed hours. A provisional **12–36 hour** completion allowance
is more cautious because individual long jobs, queueing, resumptions and
final assembly can dominate. This remains a rough forecast conditional on
no proof failures, not a deadline. See `bouchet-parallel-scaleup-20261019.json`
for queue evidence and `compute-estimate-20261019.json` for measured inputs.

A subsequent expanded queue check confirmed **43 jobs RUNNING, 200 cores
allocated, and no pending jobs**. The increased concurrency is now an
observed allocation, not merely a request. It does not establish additional
proof completion; full target builds and axiom audits remain required.

## October 19 evening: 27 regional proofs passed; conditional recovery

The downloaded results bundle contains successful complete Lean targets and
unchanged axiom audits for 23 nonapex jobs and fans F2, F3, F5 and F6.
`results-20261019-evening/verified-regions.json` identifies each region, source
revision, result hash, build counters and audit counts. The bundle is retained
verbatim. `audit_result_archives.py` checks the evidence; it is not itself a
kernel checker. Six failure-injection/inventory tests check that missing markers,
bad audits, incomplete builds and nonzero exits cannot be promoted to success.

Only job 25 is integrated into the default local root at this checkpoint.
The combined main theorem remains unfinished. The two family replays have
3,267/7,459 (ABB) and 6,947/12,872 (exterior) build modules completed, with no
reported failures in those live snapshots. Module counts have unequal costs.

`bouchet-recover.sbatch` is a conditional continuation array for the 17
outstanding allocations. Submit it with `afterany` dependencies on all original
jobs in `recovery-manifest-20261019.json`. Each task first checks its original
full theorem and audit: successful work is skipped before loading dependencies.
Unfinished work uses the current bounded generator/build path, up to eight
single-thread workers, and revalidates any restored cache through Lake. The
array requests 8 CPUs and 192 GiB per task, with at most eight concurrent tasks.
It preserves generated sources and build artifacts on controlled exit. A
scheduler kill can prevent this export; a checkpoint never counts as a proof.

`bouchet-assemble.sbatch` runs after the recovery array. Its first gate requires
all 36 nonapex, six apex, ABB and exterior build/audit records. It then imports
only generated proof subtrees from their archives, validates/rebuilds the full
dependency graph, and audits `CompletedReplays.mainTheorem`. The seven named
external/classical inputs stay explicit, consistent with `lean/ASSUMPTIONS.md`.
`ASSEMBLY_SUCCESS.txt` is written only after the combined build and audit.
These runners are deployment machinery, not evidence of completed integration.

Yale's emergency storage reservation currently holds new jobs. The existing
allocations continue running. ACCESS Delta reports 100 approved CPU core-hours
and a pending 400-core-hour exchange; the pending amount is not treated as
usable capacity. The revised 500–1,200 additional core-hour / 2–4 calendar-day
planning allowance is in `results-20261019-evening/estimate.json`.

Recovery array **30068465** and final assembly **30068466** were accepted by
Slurm after all uploaded hashes matched. Both were observed PENDING with
dependency reasons. Deployment details are in
[`bouchet-recovery-deployment-20261019.json`](bouchet-recovery-deployment-20261019.json).
Submission is not a successful proof. The newer ABB live snapshot is about
3.9 GiB and reported directory changes during capture; Lake must revalidate it.


### Latest author-proof root on Delta — October 20

Job **23040802** checks source **8473e61**: the current `SparseLowerTail`
root and its full axiom audit. Both uploaded hashes were checked before
submission. It requests one CPU, 6000 MiB and two hours, with a maximum
memory-weighted charge of six allocation hours. Together with the existing
F1 replay's 88-hour cap, the pending cap is 94 of the last verified 95-hour
balance. Both jobs were PENDING for priority, with no start estimate.
The [deployment record](delta-author-root-20261020.json) records the source,
runner hashes, resource adjustment and result paths.

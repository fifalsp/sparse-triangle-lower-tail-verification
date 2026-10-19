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

Job `30048468` was submitted on 2026-10-19 under account `pi_sl3363`.
The source archive passed SHA256 verification in the authenticated web shell.
See `bouchet-run-20261019.json` for exact source/runner revisions and hashes.
Submission is not a successful build or audit; verify the result archive and
Slurm terminal state before recording a pass.

Monitor through Bouchet Shell Access:

```bash
squeue -j 30048468
sacct -j 30048468 --format=JobID,State,ExitCode,Elapsed,MaxRSS
tail -n 20 /nfs/roberts/project/pi_sl3363/sl3363/sparse-lean-30048468.out
```

The job was subsequently observed **RUNNING** on compute node `a1132u11n04`;
the source checksum passed there and official elan setup started. Remote
build/audit completion remains unverified.

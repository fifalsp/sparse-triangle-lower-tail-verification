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

Source and logs belong in backed-up project storage. Scratch is temporary and
subject to Yale's purge policy. Keep a single dependency cache and toolchain;
submit later certificate jobs against that prepared environment.

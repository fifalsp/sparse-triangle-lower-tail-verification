#!/usr/bin/env bash
#SBATCH --job-name=sparse-lean
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --time=04:00:00
#SBATCH --output=sparse-lean-%j.out
#SBATCH --error=sparse-lean-%j.err

# Submit with two arguments: source archive's absolute path and its SHA256.
set -euo pipefail
umask 077
SOURCE_ARCHIVE="${1:?source archive required}"
SOURCE_SHA256="${2:?expected SHA256 required}"
SAVE_ROOT="${SLURM_SUBMIT_DIR:?}"
JOB_ID="${SLURM_JOB_ID:?}"
WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/sparse-lean-${JOB_ID}.XXXXXX")
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$RUN_DIR" "$WORK_DIR/repo"
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  tar -czf "$SAVE_ROOT/sparse-lean-results-${JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  printf 'Job %s finished with exit code %s; logs archived.\n' "$JOB_ID" "$rc"
  exit "$rc"
}
trap finish EXIT
hostname > "$RUN_DIR/host.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
df -h "$WORK_DIR" > "$RUN_DIR/local-storage.txt"
free_kib=$(df -Pk "$WORK_DIR" | awk 'END { print $4 }')
if (( free_kib < 25*1024*1024 )); then
  printf '%s\n' 'Less than 25 GiB available on temporary disk; stopping.' >&2
  exit 1
fi
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
CACHE_ARCHIVE="$SAVE_ROOT/lean-v4.24.0-linux-cache.tar.gz"
if [[ -f "$CACHE_ARCHIVE" ]]; then
  printf '%s\n' 'Restoring reusable Linux dependency cache.'
  tar -xzf "$CACHE_ARCHIVE" -C "$WORK_DIR"
fi
export ELAN_HOME="$WORK_DIR/runtime"
export XDG_CACHE_HOME="$WORK_DIR/download-cache"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="$SLURM_CPUS_PER_TASK"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl --fail --location --retry 3 https://elan.lean-lang.org/elan-init.sh -o "$RUN_DIR/elan-init.sh"
  sh "$RUN_DIR/elan-init.sh" -y --no-modify-path --default-toolchain none
fi
cd "$WORK_DIR/repo/lean"
lean --version | tee "$RUN_DIR/lean-version.txt"
printf '%s\n' 'Fetching pinned public mathlib dependencies and binary cache.'
lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
printf '%s\n' 'Building the Lean project on the compute node.'
/usr/bin/time -v -o "$RUN_DIR/build-time.txt" lake build > "$RUN_DIR/build.log" 2>&1
printf '%s\n' 'Auditing project axioms.'
/usr/bin/time -v -o "$RUN_DIR/audit-time.txt" lake env lean Audit.lean > "$RUN_DIR/audit.log" 2>&1
cat "$RUN_DIR/audit.log"
printf '%s\n' 'Recomputing the 40 refined apex matrix/RHS intervals.'
/usr/bin/time -v -o "$RUN_DIR/apex-proposal-time.txt" lake env lean tools/ProposeRefinedApexSystem.lean > "$RUN_DIR/apex-system.txt" 2>&1
printf '%s\n' 'Saving one reusable toolchain/dependency archive.'
tar -cf - -C "$WORK_DIR" runtime repo/lean/.lake/packages | gzip -1 > "$CACHE_ARCHIVE.${JOB_ID}.partial"
mv "$CACHE_ARCHIVE.${JOB_ID}.partial" "$CACHE_ARCHIVE"
printf '%s\n' 'Build, axiom audit and refined-system proposal completed.' > "$RUN_DIR/SUCCESS.txt"

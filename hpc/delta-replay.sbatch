#!/usr/bin/env bash
#SBATCH --job-name=triangle-apex-f1
#SBATCH --account=biah-delta-cpu
#SBATCH --partition=cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=30000M
#SBATCH --time=06:00:00
#SBATCH --constraint=projects
#SBATCH --output=triangle-delta-%j.out
#SBATCH --error=triangle-delta-%j.err
# At most 96 CPU core-hours. Four single-thread Lean workers bound memory use.
set -euo pipefail
umask 077
SOURCE_ARCHIVE=${1:?source archive}
SOURCE_SHA256=${2:?source SHA256}
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR="$SAVE_ROOT/run-${SLURM_JOB_ID:?}"
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$WORK_DIR/repo" "$RUN_DIR"
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  tar -czf "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  # Sources, toolchain and build artifacts remain in project storage for resumption.
  exit "$rc"
}
trap finish EXIT
hostname > "$RUN_DIR/host.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
export ELAN_HOME="$SAVE_ROOT/lean-runtime"
export XDG_CACHE_HOME="$SAVE_ROOT/download-cache"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl --fail --location --retry 3 --max-time 120 https://elan.lean-lang.org/elan-init.sh -o "$RUN_DIR/elan-init.sh"
  timeout 10m sh "$RUN_DIR/elan-init.sh" -y --no-modify-path --default-toolchain none
fi
cd "$WORK_DIR/repo/lean"
timeout 15m lean --version > "$RUN_DIR/lean-version.txt" 2>&1
timeout --signal=TERM --kill-after=30s 35m lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
/usr/bin/time -v -o "$RUN_DIR/replay-time.txt" timeout --signal=TERM --kill-after=60s 285m python3 tools/run_apex_cluster.py --fan 1 --logs "$RUN_DIR" --workers 4 --lean-threads 1
printf '%s\n' 'Full apex F1 theorem compiled and axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

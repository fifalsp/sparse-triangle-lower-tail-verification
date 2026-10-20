#!/usr/bin/env bash
#SBATCH --job-name=triangle-author-root
#SBATCH --account=biah-delta-cpu
#SBATCH --partition=cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=6000M
#SBATCH --time=02:00:00
#SBATCH --constraint=projects
#SBATCH --output=triangle-author-%j.out
#SBATCH --error=triangle-author-%j.err
# At most two CPU core-hours and six memory-weighted allocation hours.
# Independent of the regional replay workspaces.
set -euo pipefail
umask 077
SOURCE_ARCHIVE=${1:?source archive}
SOURCE_SHA256=${2:?source SHA256}
EXPECTED_COMMIT=${3:?source commit}
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR="$SAVE_ROOT/author-root-${SLURM_JOB_ID:?}"
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$WORK_DIR/repo" "$RUN_DIR"
RUNTIME_DIR=$(mktemp -d /tmp/triangle-author-${SLURM_JOB_ID}-XXXXXX)
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  tar -czf "$SAVE_ROOT/triangle-author-results-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  exit "$rc"
}
trap finish EXIT
hostname > "$RUN_DIR/host.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
[[ $(cat "$WORK_DIR/repo/SOURCE_COMMIT") == "$EXPECTED_COMMIT" ]]
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
export ELAN_HOME="$RUNTIME_DIR/elan"
export XDG_CACHE_HOME="$SAVE_ROOT/download-cache"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
curl --fail --location --retry 2 --max-time 120 https://elan.lean-lang.org/elan-init.sh -o "$RUN_DIR/elan-init.sh"
timeout 5m sh "$RUN_DIR/elan-init.sh" -y --no-modify-path --default-toolchain none
cd "$WORK_DIR/repo/lean"
timeout 15m lean --version > "$RUN_DIR/lean-version.txt" 2>&1
timeout --signal=TERM --kill-after=30s 35m lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
/usr/bin/time -v -o "$RUN_DIR/build-time.txt" timeout --signal=TERM --kill-after=30s 50m lake build SparseLowerTail > "$RUN_DIR/build.log" 2>&1
/usr/bin/time -v -o "$RUN_DIR/audit-time.txt" timeout --signal=TERM --kill-after=30s 10m lake env lean Audit.lean > "$RUN_DIR/audit.log" 2>&1
grep -F 'Axiom audit passed:' "$RUN_DIR/audit.log" > "$RUN_DIR/audit-summary.txt"
printf '%s\n' 'Latest author root built and axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

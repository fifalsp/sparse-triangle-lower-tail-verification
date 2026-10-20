#!/usr/bin/env bash
#SBATCH --job-name=triangle-family
#SBATCH --account=biah-delta-cpu
#SBATCH --partition=cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=30000M
#SBATCH --time=12:00:00
#SBATCH --constraint=projects
#SBATCH --output=triangle-family-%j.out
#SBATCH --error=triangle-family-%j.err
# Three single-thread workers; at most 180 memory-weighted allocation hours.
# Submit held until live balance covers all outstanding requested caps.
set -euo pipefail
umask 077
KIND=${1:?abb or exterior}
SOURCE_ARCHIVE=${2:?source archive}
SOURCE_SHA256=${3:?source SHA256}
EXPECTED_COMMIT=${4:?source commit}
[[ "$KIND" == abb || "$KIND" == exterior ]]
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR="$SAVE_ROOT/family-$KIND-${SLURM_JOB_ID:?}"
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$WORK_DIR/repo" "$RUN_DIR"
RUNTIME_DIR=$(mktemp -d /tmp/triangle-family-${SLURM_JOB_ID}-XXXXXX)
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  tar -czf "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  # Keep sources and partial .lake builds in project storage for resumption.
  exit "$rc"
}
trap finish EXIT
date -u +%FT%TZ > "$RUN_DIR/started.txt"
hostname > "$RUN_DIR/host.txt"
/sw/user/scripts/accounts | awk '$1=="biah-delta-cpu" {print}' > "$RUN_DIR/account-before.txt"
balance=$(awk '{print $2}' "$RUN_DIR/account-before.txt")
[[ "$balance" =~ ^[0-9]+([.][0-9]+)?$ ]]
awk -v b="$balance" 'BEGIN {exit !(b>=180)}'
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
[[ $(cat "$WORK_DIR/repo/SOURCE_COMMIT") == "$EXPECTED_COMMIT" ]]
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
export ELAN_HOME="$RUNTIME_DIR/elan"
export XDG_CACHE_HOME="$SAVE_ROOT/download-cache"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
curl --fail --location --retry 3 --max-time 120 https://elan.lean-lang.org/elan-init.sh -o "$RUN_DIR/elan-init.sh"
timeout 10m sh "$RUN_DIR/elan-init.sh" -y --no-modify-path --default-toolchain none
cd "$WORK_DIR/repo/lean"
timeout 15m lean --version > "$RUN_DIR/lean-version.txt" 2>&1
timeout --signal=TERM --kill-after=30s 35m lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
if [[ "$KIND" == abb ]]; then
  runner=tools/run_family_abb_cluster.py
else
  runner=tools/run_family_exterior_cluster.py
fi
/usr/bin/time -v -o "$RUN_DIR/replay-time.txt" timeout --signal=TERM --kill-after=60s 10h \
  python3 "$runner" --logs "$RUN_DIR" --workers 3 --lean-threads 1
printf '%s\n' 'Full family replay and unchanged axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

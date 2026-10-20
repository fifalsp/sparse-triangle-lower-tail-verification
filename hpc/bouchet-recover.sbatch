#!/usr/bin/env bash
#SBATCH --job-name=sparse-recover
#SBATCH --partition=day
#SBATCH --array=0-16%8
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=192G
#SBATCH --time=12:00:00
#SBATCH --output=sparse-recover-%A_%a.out
#SBATCH --error=sparse-recover-%A_%a.err
set -euo pipefail
umask 077
SOURCE_ARCHIVE=${1:?}
SOURCE_SHA256=${2:?}
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/sparse-recover-${SLURM_JOB_ID}.XXXXXX")
RUN_DIR=$WORK_DIR/logs
mkdir -p "$RUN_DIR" "$WORK_DIR/repo"
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  if [[ -d "$WORK_DIR/repo/lean/.lake/build" ]]; then
    tar -cf - -C "$WORK_DIR/repo" lean/SparseLowerTail lean/.lake/build SOURCE_COMMIT | gzip -1 > "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" && mv "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz" || rc=1
  fi
  tar -czf "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  exit "$rc"
}
trap finish EXIT
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
cd "$WORK_DIR/repo"
# Check before restoring gigabytes of dependencies. Exit 10 means replay needed;
# invalid evidence is an error and must not silently trigger a duplicate run.
set +e
python3 hpc/recover_replay.py --task "$SLURM_ARRAY_TASK_ID" --save "$SAVE_ROOT" --logs "$RUN_DIR" --check-only
check_rc=$?
set -e
if (( check_rc == 0 )); then exit 0; fi
if (( check_rc != 10 )); then exit "$check_rc"; fi
free_kib=$(df -Pk "$WORK_DIR" | awk 'END { print $4 }')
(( free_kib >= 40*1024*1024 ))
module load cURL/8.7.1-GCCcore-13.3.0
tar -xzf "$SAVE_ROOT/lean-v4.24.0-linux-cache.tar.gz" -C "$WORK_DIR"
export ELAN_HOME="$WORK_DIR/runtime"
export XDG_CACHE_HOME="$WORK_DIR/download-cache"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
(cd lean && lake exe cache get) > "$RUN_DIR/mathlib-cache.log" 2>&1
timeout --signal=TERM --kill-after=60s 10h python3 hpc/recover_replay.py --task "$SLURM_ARRAY_TASK_ID" --save "$SAVE_ROOT" --logs "$RUN_DIR"

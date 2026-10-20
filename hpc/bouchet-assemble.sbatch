#!/usr/bin/env bash
#SBATCH --job-name=sparse-assemble
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=256G
#SBATCH --time=12:00:00
#SBATCH --output=sparse-assemble-%j.out
#SBATCH --error=sparse-assemble-%j.err
set -euo pipefail
umask 077
SOURCE_ARCHIVE=${1:?}
SOURCE_SHA256=${2:?}
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/sparse-assembly-${SLURM_JOB_ID}.XXXXXX")
RUN_DIR=$WORK_DIR/logs
mkdir -p "$RUN_DIR" "$WORK_DIR/repo"
finish() {
 rc=$?
 trap - EXIT
 printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
 date -u +%FT%TZ > "$RUN_DIR/finished.txt"
 tar -czf "$SAVE_ROOT/sparse-assembly-results-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
 if [[ -f "$RUN_DIR/ASSEMBLY_SUCCESS.txt" ]]; then
  tar -czf "$SAVE_ROOT/sparse-assembly-sources-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR/repo" lean/SparseLowerTail SOURCE_COMMIT || rc=1
 fi
 exit "$rc"
}
trap finish EXIT
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
cd "$WORK_DIR/repo"
python3 hpc/assemble_replays.py --save "$SAVE_ROOT" --logs "$RUN_DIR" --check-only
free_kib=$(df -Pk "$WORK_DIR" | awk 'END { print $4 }')
(( free_kib >= 100*1024*1024 ))
module load cURL/8.7.1-GCCcore-13.3.0
tar -xzf "$SAVE_ROOT/lean-v4.24.0-linux-cache.tar.gz" -C "$WORK_DIR"
export ELAN_HOME="$WORK_DIR/runtime"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
(cd lean && lake exe cache get) > "$RUN_DIR/mathlib-cache.log" 2>&1
timeout --signal=TERM --kill-after=60s 10h python3 hpc/assemble_replays.py --save "$SAVE_ROOT" --logs "$RUN_DIR"

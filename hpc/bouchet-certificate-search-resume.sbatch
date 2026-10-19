#!/usr/bin/env bash
#SBATCH --job-name=sparse-search-resume
#SBATCH --partition=day
#SBATCH --array=14-15%2
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:15:00
#SBATCH --output=sparse-search-resume-%A_%a.out
#SBATCH --error=sparse-search-resume-%A_%a.err

# Bounded proposal search only. No success flag here is a formal proof.
# Tasks 0..35: nonapex jobs; tasks 36..40: apex fans F2..F6.
set -euo pipefail
umask 077
SOURCE_ARCHIVE="${1:?source archive required}"
SOURCE_SHA256="${2:?expected SHA256 required}"
PREVIOUS_RESULTS="${3:?previous search-results directory required}"
SEARCH_TASK="${SLURM_ARRAY_TASK_ID:?}"
SAVE_ROOT="${SLURM_SUBMIT_DIR:?}/certificate-search-${SLURM_ARRAY_JOB_ID:?}"
WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/sparse-search-${SLURM_JOB_ID}.XXXXXX")
mkdir -p "$SAVE_ROOT" "$WORK_DIR/repo" "$WORK_DIR/results"
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$WORK_DIR/results/exit-code.txt"
  tar -czf "$SAVE_ROOT/task-${SEARCH_TASK}.tar.gz" -C "$WORK_DIR" results
  exit "$rc"
}
trap finish EXIT
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$WORK_DIR/results/source-commit.txt"
printf '%s\n' 'UNTRUSTED proposal search; every leaf and the full domain still require Lean.' > "$WORK_DIR/results/TRUST_STATUS.txt"
mkdir -p "$WORK_DIR/previous"
PREVIOUS_ARCHIVE="$PREVIOUS_RESULTS/task-${SEARCH_TASK}.tar.gz"
sha256sum "$PREVIOUS_ARCHIVE" > "$WORK_DIR/results/previous-archive-sha256.txt"
tar -xzf "$PREVIOUS_ARCHIVE" -C "$WORK_DIR/previous"
cmp "$WORK_DIR/previous/results/source-commit.txt" "$WORK_DIR/repo/SOURCE_COMMIT"
if (( SEARCH_TASK < 36 )); then
  cp "$WORK_DIR/previous/results/proposal.json.gz" "$WORK_DIR/results/proposal.json.gz"
else
  cp "$WORK_DIR/previous/results/proposal.json" "$WORK_DIR/results/proposal.json"
fi
cd "$WORK_DIR/repo/lean"
if (( SEARCH_TASK < 36 )); then
  python3 tools/propose_cover_job.py --job "$SEARCH_TASK" --resume --seconds 600 --budget 1000000 --output "$WORK_DIR/results/proposal.json.gz" > "$WORK_DIR/results/search.log" 2>&1
else
  FAN_INDEX=$((SEARCH_TASK-34))
  python3 tools/propose_apex_cover.py --fan "$FAN_INDEX" --resume --seconds 600 --budget 1000000 --output "$WORK_DIR/results/proposal.json" > "$WORK_DIR/results/search.log" 2>&1
fi
cat "$WORK_DIR/results/search.log"

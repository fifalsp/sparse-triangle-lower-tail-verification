#!/usr/bin/env bash
#SBATCH --job-name=sparse-apex-array
#SBATCH --array=2-6%2
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --time=12:00:00
#SBATCH --output=sparse-apex-%A_%a.out
#SBATCH --error=sparse-apex-%A_%a.err

# Submit with replay source archive, SHA256, search-results directory, and search source commit.
# Array indices are one-based apex fan numbers. Override --array only for completed proposals.
set -euo pipefail
umask 077
SOURCE_ARCHIVE="${1:?source archive required}"
SOURCE_SHA256="${2:?expected SHA256 required}"
APEX_FAN="${SLURM_ARRAY_TASK_ID:?}"
SEARCH_TASK=$((APEX_FAN+34))
SEARCH_RESULTS="${3:?completed search-results directory required}"
SEARCH_SOURCE_COMMIT="${4:?expected search source commit required}"
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
  # Preserve completed project artifacts on success, failure, or timeout.
  # This is a resumable checkpoint, not evidence of a completed proof.
  if [[ -d "$WORK_DIR/repo/lean/.lake/build" ]]; then
    tar -cf - -C "$WORK_DIR/repo" lean/SparseLowerTail/Section05/ApexReplay lean/.lake/build "lean/data/apex-f${APEX_FAN}-subdivision-proposal.json" SOURCE_COMMIT | gzip -1 > "$SAVE_ROOT/sparse-lean-apex-checkpoint-${JOB_ID}.tar.gz.partial" &&
      mv "$SAVE_ROOT/sparse-lean-apex-checkpoint-${JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-apex-checkpoint-${JOB_ID}.tar.gz" || rc=1
  fi
  tar -czf "$SAVE_ROOT/sparse-lean-results-${JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  printf 'Job %s finished with exit code %s; logs archived.\n' "$JOB_ID" "$rc"
  exit "$rc"
}
trap finish EXIT
hostname > "$RUN_DIR/host.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
# Bouchet's system curl is older than mathlib's minimum. Without this module,
# mathlib downloads a static curl that fails with OpenSSL STORE errors here.
# Use Yale's supported module, keeping normal TLS certificate validation.
module load cURL/8.7.1-GCCcore-13.3.0
curl --version > "$RUN_DIR/curl-version.txt"
df -h "$WORK_DIR" > "$RUN_DIR/local-storage.txt"
free_kib=$(df -Pk "$WORK_DIR" | awk 'END { print $4 }')
if (( free_kib < 25*1024*1024 )); then
  printf '%s\n' 'Less than 25 GiB available on temporary disk; stopping.' >&2
  exit 1
fi
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
mkdir -p "$WORK_DIR/search"
SEARCH_ARCHIVE="$SEARCH_RESULTS/task-${SEARCH_TASK}.tar.gz"
sha256sum "$SEARCH_ARCHIVE" > "$RUN_DIR/search-archive-sha256.txt"
tar -xzf "$SEARCH_ARCHIVE" -C "$WORK_DIR/search"
printf '%s\n' "$SEARCH_SOURCE_COMMIT" > "$RUN_DIR/expected-search-source.txt"
cmp "$WORK_DIR/search/results/source-commit.txt" "$RUN_DIR/expected-search-source.txt"
cp "$WORK_DIR/search/results/source-commit.txt" "$RUN_DIR/search-source-commit.txt"
if [[ "$(cat "$WORK_DIR/search/results/exit-code.txt")" != 0 ]]; then
  printf '%s\n' 'Search task did not exit successfully.' >&2
  exit 1
fi
PROPOSAL_NAME="apex-f${APEX_FAN}-subdivision-proposal.json"
cp "$WORK_DIR/search/results/proposal.json" "$WORK_DIR/repo/lean/data/$PROPOSAL_NAME"
sha256sum "$WORK_DIR/repo/lean/data/$PROPOSAL_NAME" > "$RUN_DIR/proposal-sha256.txt"
# The Python generator rejects incomplete proposals and wrong fan cutoffs;
# the full Lean build still checks every inequality and the entire coverage tree.
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
printf '%s\n' 'Checking the full apex fan subdivision with bounded build workers.'
/usr/bin/time -v -o "$RUN_DIR/apex-time.txt" timeout --signal=TERM --kill-after=60s 10h python3 tools/run_apex_cluster.py --fan "$APEX_FAN" --logs "$RUN_DIR" --workers 4 --lean-threads 1
printf '%s\n' 'One full apex fan replay and axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

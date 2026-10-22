#!/usr/bin/env bash
#SBATCH --job-name=triangle-joint-resume
#SBATCH --account=pi_sl3363
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=12
#SBATCH --mem=320G
#SBATCH --time=24:00:00
#SBATCH --output=triangle-joint-resume-%j.out
#SBATCH --error=triangle-joint-resume-%j.err
set -euo pipefail
umask 077
CONTROL_DIR=$(realpath "${1:?checked control directory}")
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
PREVIOUS=/tmp/triangle-yale-30104499-FbBV5N
SOURCE_COMMIT=8ecc9d41892517175d46efc84e63a5d745096db0
PRIOR_RESULT="$SAVE_ROOT/sparse-assembly-results-30104499.tar.gz"
CHECKPOINT="$SAVE_ROOT/sparse-lean-recovery-checkpoint-30104499.tar.gz"
WORK_DIR=$(mktemp -d /tmp/triangle-joint-${SLURM_JOB_ID:?}-XXXXXX)
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$RUN_DIR"
# Refuse overlapping continuations, including on different nodes.
exec 8>"$SAVE_ROOT/triangle-joint-resume.lock"
flock -n 8
[[ $(sacct -j30104499 -X -n -o State,ExitCode | xargs) == 'FAILED 124:0' ]]
cd "$CONTROL_DIR"
sha256sum -c SHA256SUMS
printf '%s  %s\n' b2ff0419001de74f7c16a2cac4e6fc657ea7eeda6fae826d237b1e41a76e9687 "$PRIOR_RESULT" | sha256sum -c -
checkpoint_args=()
if [[ -f "$PREVIOUS/repo/SOURCE_COMMIT" && -d "$PREVIOUS/runtime" ]]; then
  REPO="$PREVIOUS/repo"
  RUNTIME="$PREVIOUS/runtime"
else
  REPO="$WORK_DIR/repo"
  RUNTIME="$WORK_DIR/runtime"
  mkdir -p "$REPO"
  printf '%s  %s\n' 2378c0a843220e56b80381013bc164f150fcc025d85a38f66719ab354e79c43e "$SAVE_ROOT/triangle-yale-source-8ecc9d4.tar.gz" | sha256sum -c -
  tar -xzf "$SAVE_ROOT/triangle-yale-source-8ecc9d4.tar.gz" -C "$REPO"
  tar -xzf "$SAVE_ROOT/lean-v4.24.0-linux-cache.tar.gz" -C "$WORK_DIR"
  checkpoint_args=(--checkpoint "$CHECKPOINT")
fi
[[ $(cat "$REPO/SOURCE_COMMIT") == "$SOURCE_COMMIT" ]]
finish() {
  rc=$?
  trap - EXIT
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  if [[ -d "$REPO/lean/.lake/build" ]]; then
    tar -cf - -C "$REPO" lean/SparseLowerTail lean/.lake/build SOURCE_COMMIT | gzip -1 > "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" && mv "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz" || rc=1
  fi
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  tar -czf "$SAVE_ROOT/sparse-assembly-results-${SLURM_JOB_ID}.tar.gz.partial" -C "$WORK_DIR" logs && mv "$SAVE_ROOT/sparse-assembly-results-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-assembly-results-${SLURM_JOB_ID}.tar.gz" || rc=1
  if [[ "$rc" == 0 && -f "$RUN_DIR/ASSEMBLY_SUCCESS.txt" ]]; then
    tar -czf "$SAVE_ROOT/sparse-assembly-sources-${SLURM_JOB_ID}.tar.gz.partial" -C "$REPO" lean/SparseLowerTail SOURCE_COMMIT && mv "$SAVE_ROOT/sparse-assembly-sources-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-assembly-sources-${SLURM_JOB_ID}.tar.gz" || rc=1
  fi
  exit "$rc"
}
trap finish EXIT
date -u +%FT%TZ > "$RUN_DIR/started.txt"
hostname > "$RUN_DIR/host.txt"
printf '%s\n' "$WORK_DIR" > "$RUN_DIR/node-work-directory.txt"
printf '%s\n' "$REPO" > "$RUN_DIR/resumed-repository.txt"
cp "$CONTROL_DIR/SHA256SUMS" "$RUN_DIR/control-sha256.txt"
module load cURL/8.7.1-GCCcore-13.3.0
export ELAN_HOME="$RUNTIME"
export ELAN_TOOLCHAIN
ELAN_TOOLCHAIN=$(cat "$REPO/lean/lean-toolchain")
[[ "$ELAN_TOOLCHAIN" == leanprover/lean4:v4.24.0 ]]
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
ulimit -s 65536
cd "$REPO/lean"
lean --version > "$RUN_DIR/lean-version.txt"
# Six independent single-threaded Lean processes, each capped at 48 GiB.
# All sources, target, and the namespace-wide axiom policy stay unchanged.
timeout --signal=TERM --kill-after=60s 21h python3 "$CONTROL_DIR/resume_assembly.py" --repo "$REPO" --prior-result "$PRIOR_RESULT" "${checkpoint_args[@]}" --logs "$RUN_DIR" --workers 6

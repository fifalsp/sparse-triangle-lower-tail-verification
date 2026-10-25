#!/usr/bin/env bash
#SBATCH --job-name=triangle-root-stack
#SBATCH --account=pi_sl3363
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=192G
#SBATCH --time=24:00:00
#SBATCH --output=triangle-root-stack-%j.out
#SBATCH --error=triangle-root-stack-%j.err
set -euo pipefail
umask 077
CONTROL_DIR=$(realpath "${1:?checked control directory}")
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
# Later continuations pass the ended predecessor and its node-local directory.
PREDECESSOR=${2:-30496690}
PREVIOUS=${3:-/tmp/triangle-joint-30496690-FdpBt4}
[[ "$PREDECESSOR" =~ ^[0-9]+$ ]] || exit 2
[[ "$PREVIOUS" == /tmp/triangle-joint-"$PREDECESSOR"-* && "$PREVIOUS" != *..* ]] || exit 2
SOURCE_COMMIT=8ecc9d41892517175d46efc84e63a5d745096db0
BASE_RESULT="$SAVE_ROOT/sparse-assembly-results-30104499.tar.gz"
PRIOR_RESULT="$SAVE_ROOT/sparse-assembly-results-${PREDECESSOR}.tar.gz"
CHECKPOINT="$SAVE_ROOT/sparse-lean-recovery-checkpoint-${PREDECESSOR}.tar.gz"
WORK_DIR=$(mktemp -d /tmp/triangle-joint-${SLURM_JOB_ID:?}-XXXXXX)
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$RUN_DIR"
# Refuse overlapping continuations, including on different nodes.
exec 8>"$SAVE_ROOT/triangle-joint-resume.lock"
flock -n 8

cd "$CONTROL_DIR"
sha256sum -c SHA256SUMS
printf '%s  %s\n' b2ff0419001de74f7c16a2cac4e6fc657ea7eeda6fae826d237b1e41a76e9687 "$BASE_RESULT" | sha256sum -c -
read -r prior_state prior_exit < <(sacct -j"$PREDECESSOR" -X -n -o State,ExitCode | xargs)
decision=$(python3 "$CONTROL_DIR/recover_combined_root.py" gate "$PRIOR_RESULT" "$prior_state" "$prior_exit")
if [[ "$decision" == finished ]]; then
  printf 'Prior job passed full target and audit; skipping duplicate computation.\n'
  exit 0
fi
[[ "$decision" == resume-isolated-root-stack-overflow && -s "$CHECKPOINT" ]]
sha256sum "$PRIOR_RESULT" > "$RUN_DIR/predecessor-result-sha256.txt"
checkpoint_args=()
if [[ -f "$PREVIOUS/repo/SOURCE_COMMIT" && -d "$PREVIOUS/runtime" ]]; then
  REPO="$PREVIOUS/repo"
  RUNTIME="$PREVIOUS/runtime"
  # Prior job has ended. Normalize only its weak CPU resource setting.
  if grep -Fq 'weakLeanArgs = ["-M49152", "-j2", "-s65536"]' "$REPO/lean/lakefile.yale.toml"; then
    python3 "$CONTROL_DIR/set_lean_threads.py" --repo "$REPO" --logs "$PREVIOUS/logs" --threads 1 --expected-threads 2
  fi
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
ulimit -s 262144
cd "$REPO/lean"
lean --version > "$RUN_DIR/lean-version.txt"
# One ordinary aggregate build, then the original namespace audit.
# Lake itself runs through the pinned Lean runtime with a larger stack.
timeout --signal=TERM --kill-after=60s 21h python3 "$CONTROL_DIR/recover_combined_root.py" --repo "$REPO" --prior-result "$PRIOR_RESULT" "${checkpoint_args[@]}" --logs "$RUN_DIR"

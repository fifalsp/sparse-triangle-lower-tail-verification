#!/usr/bin/env bash
#SBATCH --job-name=triangle-integration-stack
#SBATCH --account=pi_sl3363
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=192G
#SBATCH --time=24:00:00
#SBATCH --output=triangle-yale-%j.out
#SBATCH --error=triangle-yale-%j.err
set -euo pipefail
umask 077
ulimit -s 65536
STAGE=${1:?f1, cover0, cover12, abb, exterior, or assembly}
SOURCE_ARCHIVE=${2:?checked source archive}
SOURCE_SHA256=${3:?source archive SHA256}
EXPECTED_COMMIT=${4:?source commit}
CHECKPOINT_DIR=${5:?original Yale transfer staging directory}
CONTROL_ARCHIVE=${6:?checked stack control archive}
CONTROL_SHA256=${7:?control archive SHA256}
case "$STAGE" in f1|cover0|cover12|abb|exterior|assembly) ;; *) exit 2 ;; esac
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR=$(mktemp -d /tmp/triangle-yale-${SLURM_JOB_ID:?}-XXXXXX)
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$WORK_DIR/repo" "$RUN_DIR"
finish() {
  rc=$?
  trap - EXIT
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  # Keep generated sources and validated partial cache even on failure.
  if [[ -d "$WORK_DIR/repo/lean/.lake/build" ]]; then
    tar -cf - -C "$WORK_DIR/repo" lean/SparseLowerTail lean/.lake/build SOURCE_COMMIT | gzip -1 > "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" && mv "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz" || rc=1
  fi
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  if [[ "$STAGE" == assembly ]]; then result_prefix=sparse-assembly-results; else result_prefix=sparse-lean-results; fi
  tar -czf "$SAVE_ROOT/$result_prefix-${SLURM_JOB_ID}.tar.gz.partial" -C "$WORK_DIR" logs && mv "$SAVE_ROOT/$result_prefix-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/$result_prefix-${SLURM_JOB_ID}.tar.gz" || rc=1
  if [[ -f "$RUN_DIR/ASSEMBLY_SUCCESS.txt" && "$rc" == 0 ]]; then
    tar -czf "$SAVE_ROOT/sparse-assembly-sources-${SLURM_JOB_ID}.tar.gz.partial" -C "$WORK_DIR/repo" lean/SparseLowerTail SOURCE_COMMIT && mv "$SAVE_ROOT/sparse-assembly-sources-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-assembly-sources-${SLURM_JOB_ID}.tar.gz" || rc=1
  fi
  # Preserve local work too; no cleanup is needed for proof acceptance.
  exit "$rc"
}
trap finish EXIT
hostname > "$RUN_DIR/host.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
printf '%s\n' "$WORK_DIR" > "$RUN_DIR/node-work-directory.txt"
free_kib=$(df -Pk "$WORK_DIR" | awk 'END {print $4}')
(( free_kib >= 100*1024*1024 ))
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
printf '%s  %s\n' "$CONTROL_SHA256" "$CONTROL_ARCHIVE" | sha256sum -c -
tar -xzf "$CONTROL_ARCHIVE" -C "$WORK_DIR/repo"
[[ $(cat "$WORK_DIR/repo/SOURCE_COMMIT") == "$EXPECTED_COMMIT" ]]
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
cd "$WORK_DIR/repo"
checkpoint=
case "$STAGE" in
  cover0) checkpoint=sparse-lean-cover-checkpoint-30060676.tar.gz ;;
  abb) checkpoint=sparse-lean-abb-live-checkpoint-30052586-2145.tar.gz ;;
  exterior) checkpoint=sparse-lean-exterior-checkpoint-30056868.tar.gz ;;
esac
if [[ -n "$checkpoint" ]]; then
  python3 hpc/prepare_delta_migration.py --save "$CHECKPOINT_DIR" --checkpoint "$checkpoint" > "$RUN_DIR/checkpoint-sha256.log" 2>&1
  python3 -c 'import sys; from pathlib import Path; sys.path.insert(0,"hpc"); from recover_replay import restore; restore(Path(sys.argv[1]),Path.cwd())' "$CHECKPOINT_DIR/$checkpoint"
fi
if [[ "$STAGE" == assembly ]]; then
  python3 hpc/assemble_replays.py --save "$SAVE_ROOT" --logs "$RUN_DIR" --check-only
fi
module load cURL/8.7.1-GCCcore-13.3.0
# Stage large archives as single files; all extraction writes stay on local disk.
cp "$SAVE_ROOT/lean-v4.24.0-linux-cache.tar.gz" "$WORK_DIR/runtime-cache.tar.gz"
sha256sum "$WORK_DIR/runtime-cache.tar.gz" > "$RUN_DIR/runtime-cache-sha256.txt"
tar -xzf "$WORK_DIR/runtime-cache.tar.gz" -C "$WORK_DIR"
export ELAN_HOME="$WORK_DIR/runtime"
export XDG_CACHE_HOME="$WORK_DIR/download-cache"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
cd lean
lean --version > "$RUN_DIR/lean-version.txt" 2>&1
timeout --signal=TERM --kill-after=30s 45m lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
memory=16384
workers=4
if [[ "$STAGE" == assembly ]]; then memory=49152; workers=3; fi
python3 -c 'from pathlib import Path; import sys; s=Path("lakefile.toml").read_text(); assert "weakLeanArgs" not in s; Path("lakefile.yale.toml").write_text(s.replace("defaultTargets","weakLeanArgs = [\"-M"+sys.argv[1]+"\", \"-j1\", \"-s65536\"]\ndefaultTargets",1))' "$memory"
PROFILE="$PWD/lakefile.yale.toml"
if [[ "$STAGE" == assembly ]]; then
  command=(python3 ../hpc/assemble_replays.py --save "$SAVE_ROOT" --logs "$RUN_DIR" --workers "$workers" --lakefile "$PROFILE" --audit-memory-mib "$memory" --ready-batches)
else
  command=(python3 ../hpc/run_regional_ready.py "$STAGE" --logs "$RUN_DIR" --lakefile "$PROFILE" --workers "$workers" --audit-sha256 956129721ba7190769a93bd755dde91ac7b4fcd15326656721cc822308cc9014)
fi
timeout --signal=TERM --kill-after=60s 21h /usr/bin/time -v -o "$RUN_DIR/replay-time.txt" "${command[@]}"
printf '%s\n' 'Full stage, source hashes and unchanged axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

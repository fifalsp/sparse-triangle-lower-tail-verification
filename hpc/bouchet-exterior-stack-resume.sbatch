#!/usr/bin/env bash
#SBATCH --job-name=triangle-exterior-stack
#SBATCH --account=pi_sl3363
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=96G
#SBATCH --time=24:00:00
#SBATCH --output=triangle-exterior-stack-%j.out
#SBATCH --error=triangle-exterior-stack-%j.err
set -euo pipefail
umask 077
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
CONTROL=${1:?checked control archive}
CONTROL_SHA=${2:?control SHA256}
PREVIOUS=/tmp/triangle-yale-30082914-Ke4JN9
WORK_DIR=$(mktemp -d /tmp/triangle-exterior-stack-${SLURM_JOB_ID:?}-XXXXXX)
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$RUN_DIR" "$WORK_DIR/control"
printf '%s  %s\n' "$CONTROL_SHA" "$CONTROL" | sha256sum -c -
tar -xzf "$CONTROL" -C "$WORK_DIR/control"
# A serialized repair may follow an earlier recovery attempt. If that attempt
# passed every existing archive gate, leave its proof and evidence authoritative.
if [[ -f "$SAVE_ROOT/sparse-lean-results-30101361.tar.gz" ]] && python3 -c 'import sys;from pathlib import Path;sys.path.insert(0,sys.argv[1]+"/hpc");from audit_result_archives import inspect;p=Path(sys.argv[2]);r=inspect(p.read_bytes(),p.name);sys.exit(0 if r and r.get("verified") and r.get("key")=="exterior" else 10)' "$WORK_DIR/control" "$SAVE_ROOT/sparse-lean-results-30101361.tar.gz"; then
  printf 'Earlier exterior recovery passed; no duplicate replay.\n'
  exit 0
fi
# Reuse the ended allocation's persistent checkout when it is still present.
# A complete saved checkpoint provides a fallback if /tmp was cleaned.
if [[ -f "$PREVIOUS/repo/SOURCE_COMMIT" && -d "$PREVIOUS/runtime" ]]; then
  REPO="$PREVIOUS/repo"
  RUNTIME="$PREVIOUS/runtime"
  OLD_LOGS="$PREVIOUS/logs"
else
  REPO="$WORK_DIR/repo"
  RUNTIME="$WORK_DIR/runtime"
  OLD_LOGS="$WORK_DIR/previous/logs"
  mkdir -p "$REPO" "$WORK_DIR/previous"
  printf '%s  %s\n' 2378c0a843220e56b80381013bc164f150fcc025d85a38f66719ab354e79c43e "$SAVE_ROOT/triangle-yale-source-8ecc9d4.tar.gz" | sha256sum -c -
  tar -xzf "$SAVE_ROOT/triangle-yale-source-8ecc9d4.tar.gz" -C "$REPO"
  python3 -c 'import sys;from pathlib import Path;sys.path.insert(0,sys.argv[3]+"/hpc");from restore_family_checkpoint import restore;restore(Path(sys.argv[2]),Path(sys.argv[1]),"exterior")' "$REPO" "$SAVE_ROOT/sparse-lean-recovery-checkpoint-30082914.tar.gz" "$WORK_DIR/control"
  tar -xzf "$SAVE_ROOT/sparse-lean-results-30082914.tar.gz" -C "$WORK_DIR/previous"
  tar -xzf "$SAVE_ROOT/lean-v4.24.0-linux-cache.tar.gz" -C "$WORK_DIR"
fi
[[ $(cat "$REPO/SOURCE_COMMIT") == 8ecc9d41892517175d46efc84e63a5d745096db0 ]]
exec 9>"$REPO/exterior-stack-resume.lock"
flock -n 9
finish() {
  rc=$?
  trap - EXIT
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  tar -cf - -C "$REPO" lean/SparseLowerTail lean/.lake/build SOURCE_COMMIT | gzip -1 > "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" && mv "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz" || rc=1
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  tar -czf "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz.partial" -C "$WORK_DIR" logs && mv "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz" || rc=1
  exit "$rc"
}
trap finish EXIT
date -u +%FT%TZ > "$RUN_DIR/started.txt"
hostname > "$RUN_DIR/host.txt"
printf '%s\n' "$WORK_DIR" > "$RUN_DIR/node-work-directory.txt"
printf '%s\n' "$REPO" > "$RUN_DIR/resumed-repository.txt"
module load cURL/8.7.1-GCCcore-13.3.0
export ELAN_HOME="$RUNTIME"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
ulimit -s 65536
lean --version > "$RUN_DIR/lean-version.txt"
timeout --signal=TERM --kill-after=60s 20h python3 "$WORK_DIR/control/hpc/resume_exterior_root.py" --repo "$REPO" --previous-logs "$OLD_LOGS" --logs "$RUN_DIR"

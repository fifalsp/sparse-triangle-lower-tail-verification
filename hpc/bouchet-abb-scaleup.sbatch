#!/usr/bin/env bash
#SBATCH --job-name=triangle-abb8-yale
#SBATCH --account=pi_sl3363
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=12
#SBATCH --mem=192G
#SBATCH --time=24:00:00
#SBATCH --output=triangle-abb8-%j.out
#SBATCH --error=triangle-abb8-%j.err
set -euo pipefail
umask 077
SOURCE_ARCHIVE=${1:?source archive}
SOURCE_SHA256=${2:?source archive sha256}
EXPECTED_COMMIT=${3:?source commit}
CONTROL_ARCHIVE=${4:?checked control bundle}
CONTROL_SHA256=${5:?control sha256}
HANDOFF=${6:?shared checkpoint directory}
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR=$(mktemp -d /tmp/triangle-yale-${SLURM_JOB_ID:?}-XXXXXX)
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$WORK_DIR/repo" "$RUN_DIR" "$HANDOFF"
finish() {
  rc=$?
  trap - EXIT
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  if [[ -d "$WORK_DIR/repo/lean/.lake/build" ]]; then
    tar -cf - -C "$WORK_DIR/repo" lean/SparseLowerTail lean/.lake/build SOURCE_COMMIT | gzip -1 > "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" && mv "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-recovery-checkpoint-${SLURM_JOB_ID}.tar.gz" || rc=1
  fi
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  tar -czf "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz.partial" -C "$WORK_DIR" logs && mv "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz.partial" "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz" || rc=1
  exit "$rc"
}
trap finish EXIT
hostname > "$RUN_DIR/host.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
printf '%s\n' "$WORK_DIR" > "$RUN_DIR/node-work-directory.txt"
free_kib=$(df -Pk "$WORK_DIR" | awk 'END {print $4}')
(( free_kib >= 100*1024*1024 ))
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
printf '%s  %s\n' "$CONTROL_SHA256" "$CONTROL_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
[[ $(cat "$WORK_DIR/repo/SOURCE_COMMIT") == "$EXPECTED_COMMIT" ]]
# The small control bundle changes orchestration only; proof source stays fixed.
tar -xzf "$CONTROL_ARCHIVE" -C "$WORK_DIR/repo"
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
cp "$WORK_DIR/repo/CONTROL_COMMIT" "$RUN_DIR/control-commit.txt"
cd "$WORK_DIR/repo"
sha256sum hpc/build_ready_batches.py hpc/run_regional_ready.py hpc/checkpoint_abb_scaleup.py > "$RUN_DIR/control-sha256.txt"
module load cURL/8.7.1-GCCcore-13.3.0
cp "$SAVE_ROOT/lean-v4.24.0-linux-cache.tar.gz" "$WORK_DIR/runtime-cache.tar.gz"
tar -xzf "$WORK_DIR/runtime-cache.tar.gz" -C "$WORK_DIR"
export ELAN_HOME="$WORK_DIR/runtime"
export XDG_CACHE_HOME="$WORK_DIR/download-cache"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
cd lean
lean --version > "$RUN_DIR/lean-version.txt" 2>&1
timeout --signal=TERM --kill-after=30s 45m lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
python3 -c 'from pathlib import Path; s=Path("lakefile.toml").read_text(); assert "weakLeanArgs" not in s; Path("lakefile.yale.toml").write_text(s.replace("defaultTargets", "weakLeanArgs = [\"-M16384\", \"-j1\"]\ndefaultTargets",1))'
printf '%s\n%s\n' "$SLURM_JOB_ID" "$WORK_DIR" > "$HANDOFF/replacement-ready.txt.partial"
mv "$HANDOFF/replacement-ready.txt.partial" "$HANDOFF/replacement-ready.txt"
# The old job keeps working while we wait. No competing proof build is launched.
deadline=$((SECONDS+7200))
until [[ -f "$HANDOFF/checkpoint.json" ]]; do
  (( SECONDS < deadline )) || { echo 'Checkpoint handoff timed out'; exit 1; }
  sleep 10
done
python3 - "$HANDOFF" "$WORK_DIR/repo" "$RUN_DIR" <<'PY'
import hashlib,json,sys
from pathlib import Path
handoff,repo,logs=map(Path,sys.argv[1:])
record=json.loads((handoff/'checkpoint.json').read_text())
assert record['source_commit']==(repo/'SOURCE_COMMIT').read_text().strip()
def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(8*1024*1024),b''):h.update(block)
    return h.hexdigest()
assert digest(Path(record['archive']))==record['archive_sha256']
assert digest(handoff/'source-manifest.json')==record['source_manifest_sha256']
sys.path.insert(0,str(repo/'hpc'))
from recover_replay import restore
restore(Path(record['archive']),repo)
(logs/'preserved-checkpoint.json').write_text(json.dumps(record,indent=2)+'\n')
PY
timeout --signal=TERM --kill-after=60s 19h /usr/bin/time -v -o "$RUN_DIR/replay-time.txt" python3 ../hpc/run_regional_ready.py abb --logs "$RUN_DIR" --lakefile "$PWD/lakefile.yale.toml" --workers 8 --expected-manifest "$HANDOFF/source-manifest.json" --audit-sha256 956129721ba7190769a93bd755dde91ac7b4fcd15326656721cc822308cc9014
printf '%s\n' 'Full ABB target, source hashes and unchanged axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

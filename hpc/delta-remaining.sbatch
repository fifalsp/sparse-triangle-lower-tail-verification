#!/usr/bin/env bash
# Override memory/time for each stage at submission; the ledger records each cap.
#SBATCH --job-name=triangle-remaining
#SBATCH --account=biah-delta-cpu
#SBATCH --partition=cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=12000M
#SBATCH --time=04:00:00
#SBATCH --constraint=projects
#SBATCH --output=triangle-remaining-%j.out
#SBATCH --error=triangle-remaining-%j.err
set -euo pipefail
umask 077
STAGE=${1:?cover0, cover12, abb, exterior, or assembly}
SOURCE_ARCHIVE=${2:?source archive}
SOURCE_SHA256=${3:?archive SHA256}
EXPECTED_COMMIT=${4:?source commit}
TRANSFER_DIR=${5:?verified Yale transfer directory}
case "$STAGE" in cover0|cover12|abb|exterior|assembly) ;; *) exit 2 ;; esac
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
WORK_DIR="$SAVE_ROOT/remaining-$STAGE-${SLURM_JOB_ID:?}"
RUN_DIR="$WORK_DIR/logs"
mkdir -p "$WORK_DIR/repo" "$RUN_DIR"
RUNTIME_DIR=$(mktemp -d /tmp/triangle-remaining-${SLURM_JOB_ID}-XXXXXX)
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  tar -czf "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  # All generated sources and partial builds remain in project storage.
  exit "$rc"
}
trap finish EXIT
date -u +%FT%TZ > "$RUN_DIR/started.txt"
hostname > "$RUN_DIR/host.txt"
printf '%s  %s\n' "$SOURCE_SHA256" "$SOURCE_ARCHIVE" | sha256sum -c -
tar -xzf "$SOURCE_ARCHIVE" -C "$WORK_DIR/repo"
[[ $(cat "$WORK_DIR/repo/SOURCE_COMMIT") == "$EXPECTED_COMMIT" ]]
cp "$WORK_DIR/repo/SOURCE_COMMIT" "$RUN_DIR/source-commit.txt"
/sw/user/scripts/accounts | awk '$1=="biah-delta-cpu" {print}' > "$RUN_DIR/account-before.txt"
cd "$WORK_DIR/repo"
checkpoint=
case "$STAGE" in
  cover0) checkpoint=sparse-lean-cover-checkpoint-30060676.tar.gz ;;
  abb) checkpoint=sparse-lean-abb-live-checkpoint-30052586-2145.tar.gz ;;
  exterior) checkpoint=sparse-lean-exterior-checkpoint-30056868.tar.gz ;;
esac
if [[ -n "$checkpoint" ]]; then
  python3 hpc/prepare_delta_migration.py --save "$TRANSFER_DIR" --checkpoint "$checkpoint"
  python3 -c 'import sys; from pathlib import Path; sys.path.insert(0,"hpc"); from recover_replay import restore; restore(Path(sys.argv[1]),Path.cwd())' "$TRANSFER_DIR/$checkpoint"
elif [[ "$STAGE" == assembly ]]; then
  python3 hpc/prepare_delta_migration.py --save "$TRANSFER_DIR" --collect-delta "$SAVE_ROOT" > "$RUN_DIR/assembly-collection.log" 2>&1
  python3 hpc/assemble_replays.py --save "$TRANSFER_DIR" --logs "$RUN_DIR" --check-only
else
  # The failed Yale cover-12 process did not leave a checkpoint.
  [[ -s "$TRANSFER_DIR/SHA256SUMS" ]]
fi
export ELAN_HOME="$RUNTIME_DIR/elan"
# mathlib writes curl.cfg and partial downloads in this directory. Each job
# needs its own cache even when several stages start together.
export XDG_CACHE_HOME="$WORK_DIR/download-cache"
# The static curl used by mathlib does not discover Red Hat's CA bundle.
# Keep certificate verification enabled and use the system trust store.
export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
export SSL_CERT_FILE="$CURL_CA_BUNDLE"
[[ -r "$CURL_CA_BUNDLE" ]]
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=1
curl --fail --location --retry 3 --max-time 120 https://elan.lean-lang.org/elan-init.sh -o "$RUN_DIR/elan-init.sh"
timeout 10m sh "$RUN_DIR/elan-init.sh" -y --no-modify-path --default-toolchain none
cd lean
timeout 15m lean --version > "$RUN_DIR/lean-version.txt" 2>&1
timeout --signal=TERM --kill-after=30s 35m lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
memory=8192
workers=1
if [[ "$STAGE" == abb || "$STAGE" == exterior ]]; then workers=3; fi
if [[ "$STAGE" == assembly ]]; then memory=49152; fi
python3 -c 'from pathlib import Path; import sys; p=Path("lakefile.toml"); s=p.read_text(); assert "weakLeanArgs" not in s; Path("lakefile.delta.toml").write_text(s.replace("defaultTargets", "weakLeanArgs = [\"-M"+sys.argv[1]+"\", \"-j1\"]\ndefaultTargets",1))' "$memory"
export SPARSE_LAKEFILE="$PWD/lakefile.delta.toml"
case "$STAGE" in
  cover0|cover12) command=(python3 tools/run_cover_job_cluster.py --job "${STAGE#cover}" --logs "$RUN_DIR" --workers 1 --lean-threads 1) ;;
  abb) command=(python3 tools/run_family_abb_cluster.py --logs "$RUN_DIR" --workers "$workers" --lean-threads 1) ;;
  exterior) command=(python3 tools/run_family_exterior_cluster.py --logs "$RUN_DIR" --workers "$workers" --lean-threads 1) ;;
  assembly) command=(python3 ../hpc/assemble_replays.py --save "$TRANSFER_DIR" --logs "$RUN_DIR" --workers 1 --lakefile "$SPARSE_LAKEFILE" --audit-memory-mib "$memory") ;;
esac
/usr/bin/time -v -o "$RUN_DIR/replay-time.txt" "${command[@]}"
printf '%s\n' 'Full stage and unchanged axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

#!/usr/bin/env bash
# Submit only after the previous exterior job has ended and the budget fits.
#SBATCH --job-name=triangle-exterior-local-resume
#SBATCH --account=biah-delta-cpu
#SBATCH --partition=cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=30000M
#SBATCH --time=06:00:00
#SBATCH --constraint=projects
#SBATCH --output=triangle-exterior-resume-%j.out
#SBATCH --error=triangle-exterior-resume-%j.err
set -euo pipefail
umask 077
PREVIOUS=${1:?previous Delta job ID}
EXPECTED_COMMIT=${2:?proof source commit}
AUDIT_SHA256=${3:?expected unchanged Audit.lean SHA256}
SCHEDULER=${4:?absolute path to checked build_ready_batches.py}
[[ "$PREVIOUS" =~ ^[0-9]+$ && "$AUDIT_SHA256" =~ ^[0-9a-f]{64}$ ]]
[[ "$EXPECTED_COMMIT" =~ ^[0-9a-f]{40}$ && -f "$SCHEDULER" ]]
[[ ${SLURM_JOB_ACCOUNT:?} == biah-delta-cpu ]]
SAVE_ROOT=${SLURM_SUBMIT_DIR:?}
PREVIOUS_WORK="$SAVE_ROOT/remaining-exterior-$PREVIOUS"
# Never compete with a live job or resume an already successful replay.
previous_state=$(sacct -X --noheader --parsable2 --jobs="$PREVIOUS" --format=JobID,State | awk -F'|' -v job="$PREVIOUS" '$1==job {print $2}')
case "$previous_state" in TIMEOUT|FAILED|CANCELLED*|OUT_OF_MEMORY|NODE_FAIL|PREEMPTED|COMPLETED) ;; *) echo "Previous job is not confirmed terminal: $previous_state" >&2; exit 2 ;; esac
[[ ! -e "$PREVIOUS_WORK/logs/FAMILY_EXTERIOR_SUCCESS.txt" ]]
[[ $(cat "$PREVIOUS_WORK/repo/SOURCE_COMMIT") == "$EXPECTED_COMMIT" ]]
exec 9>"$PREVIOUS_WORK/repo/.triangle-resume.lock"
flock -n 9
live_states=$(squeue --noheader --user="${USER:?}" --format='%i %T' | awk -v job="$PREVIOUS" '$1==job {print $2}')
[[ -z "$live_states" ]]
WORK_DIR="$SAVE_ROOT/remaining-exterior-${SLURM_JOB_ID:?}"
mkdir "$WORK_DIR"
mkdir "$WORK_DIR/logs"
ln -s "$PREVIOUS_WORK/repo" "$WORK_DIR/repo"
RUN_DIR="$WORK_DIR/logs"
RUNTIME_DIR=$(mktemp -d /tmp/triangle-exterior-resume-${SLURM_JOB_ID}-XXXXXX)
finish() {
  rc=$?
  trap - EXIT
  printf '%s\n' "$rc" > "$RUN_DIR/exit-code.txt"
  date -u +%FT%TZ > "$RUN_DIR/finished.txt"
  tar -czf "$SAVE_ROOT/sparse-lean-results-${SLURM_JOB_ID}.tar.gz" -C "$WORK_DIR" logs || rc=1
  exit "$rc"
}
trap finish EXIT
date -u +%FT%TZ > "$RUN_DIR/started.txt"
hostname > "$RUN_DIR/host.txt"
printf '%s\n' "$EXPECTED_COMMIT" > "$RUN_DIR/source-commit.txt"
printf '%s\n' "$PREVIOUS" > "$RUN_DIR/resumed-from-job.txt"
cp "$SCHEDULER" "$RUN_DIR/build_ready_batches.py"
sha256sum "$RUN_DIR/build_ready_batches.py" > "$RUN_DIR/scheduler-sha256.txt"
cd "$WORK_DIR/repo/lean"
printf '%s  Audit.lean\n' "$AUDIT_SHA256" | sha256sum -c -
export ELAN_HOME="$RUNTIME_DIR/elan"
export XDG_CACHE_HOME="$WORK_DIR/download-cache"
export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
export SSL_CERT_FILE="$CURL_CA_BUNDLE"
export LEAN_NUM_THREADS=1
export PATH="$ELAN_HOME/bin:$PATH"
[[ -r "$CURL_CA_BUNDLE" ]]
curl --fail --location --retry 3 --max-time 120 https://elan.lean-lang.org/elan-init.sh -o "$RUN_DIR/elan-init.sh"
timeout 10m sh "$RUN_DIR/elan-init.sh" -y --no-modify-path --default-toolchain none
timeout 15m lean --version > "$RUN_DIR/lean-version.txt" 2>&1
# The prior job completed mathlib cache installation. Reuse that checkout;
# do not extract the Yale archive, regenerate proofs, or redownload its cache.
PROFILE="$PWD/lakefile.resume-${SLURM_JOB_ID}.toml"
python3 -c 'from pathlib import Path; import sys; s=Path("lakefile.toml").read_text(); assert "weakLeanArgs" not in s; Path(sys.argv[1]).write_text(s.replace("defaultTargets", "weakLeanArgs = [\"-M8192\", \"-j1\"]\ndefaultTargets",1))' "$PROFILE"
TARGET=SparseLowerTail.Section08.FamilyExteriorReplay.Full.CompactCertificate
export RUN_DIR TARGET PROFILE
python3 -c 'import json,os; from pathlib import Path; Path(os.environ["RUN_DIR"],"family-exterior-status.json").write_text(json.dumps(dict(phase="resume_build",trust_status="Full target, source hashes and unchanged axiom audit pending"))+"\n")'
python3 - <<'PY'
import hashlib, importlib.util, json, os
from pathlib import Path
root=Path.cwd()
s=importlib.util.spec_from_file_location('plan',root/'tools/build_bounded.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
graph=m.dependency_graph(os.environ['TARGET'])
manifest={name:hashlib.sha256((root/Path(name.replace('.','/')).with_suffix('.lean')).read_bytes()).hexdigest() for name in sorted(graph)}
Path(os.environ['RUN_DIR'],'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
PY
python3 "$RUN_DIR/build_ready_batches.py" --repo "$WORK_DIR/repo" --target "$TARGET" --logs "$RUN_DIR/exterior-build" --lakefile "$PROFILE" --workers 3 > "$RUN_DIR/family-exterior-build.log" 2>&1
python3 - <<'PY'
import os
from pathlib import Path
s=Path('Audit.lean').read_text();assert s.startswith('import SparseLowerTail\n')
Path(os.environ['RUN_DIR'],'AuditFamilyExterior.lean').write_text(s.replace('import SparseLowerTail\n','import '+os.environ['TARGET']+'\n',1))
PY
lake --file "$PROFILE" env lean -M8192 -j1 "$RUN_DIR/AuditFamilyExterior.lean" > "$RUN_DIR/family-exterior-audit.log" 2>&1
printf '%s  Audit.lean\n' "$AUDIT_SHA256" | sha256sum -c -
python3 - <<'PY'
import hashlib,json,os
from pathlib import Path
manifest=json.loads(Path(os.environ['RUN_DIR'],'source-manifest.json').read_text())
for name,expected in manifest.items():
    p=Path(name.replace('.','/')).with_suffix('.lean')
    if hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
        raise ValueError('Proof source changed: '+name)
Path(os.environ['RUN_DIR'],'source-hashes-passed.txt').write_text('All target dependency sources unchanged.\n')
Path(os.environ['RUN_DIR'],'family-exterior-status.json').write_text(json.dumps(dict(phase='complete',trust_status='Full exterior replay compiled; source hashes unchanged; axiom audit passed; ABB remains an internal premise'))+'\n')
PY
printf '%s\n' 'Full exterior replay and unchanged axiom audit passed; ABB local theorem remains required.' > "$RUN_DIR/FAMILY_EXTERIOR_SUCCESS.txt"
printf '%s\n' 'Full stage, unchanged source hashes and axiom audit passed.' > "$RUN_DIR/SUCCESS.txt"

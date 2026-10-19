#!/usr/bin/env bash
#SBATCH --job-name=sparse-lean
#SBATCH --partition=day
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --time=04:00:00
#SBATCH --output=logs/slurm-%j.out
#SBATCH --error=logs/slurm-%j.err

# Submit from the extracted repository root. All compilation runs on a compute node.
set -euo pipefail
umask 077
cd "${SLURM_SUBMIT_DIR:?Submit this file with sbatch from the repository root}"
RUN_DIR="$PWD/logs/job-${SLURM_JOB_ID:?}"
mkdir -p "$RUN_DIR"
trap 'rc=$?; printf "%s\n" "$rc" > "$RUN_DIR/exit-code.txt"; date -u +%FT%TZ > "$RUN_DIR/finished.txt"' EXIT
hostname > "$RUN_DIR/host.txt"
date -u +%FT%TZ > "$RUN_DIR/started.txt"
cp SOURCE_COMMIT "$RUN_DIR/source-commit.txt"
# Keep one project-local toolchain installation across source snapshots.
export ELAN_HOME="${SPARSE_ELAN_HOME:-$(dirname "$PWD")/lean-runtime}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="$SLURM_CPUS_PER_TASK"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl --fail --location --retry 3 https://elan.lean-lang.org/elan-init.sh -o "$RUN_DIR/elan-init.sh"
  sh "$RUN_DIR/elan-init.sh" -y --no-modify-path --default-toolchain none
fi
cd lean
lean --version > "$RUN_DIR/lean-version.txt"
# The committed Lake manifest pins dependency revisions; do not run lake update.
lake exe cache get > "$RUN_DIR/mathlib-cache.log" 2>&1
/usr/bin/time -v -o "$RUN_DIR/build-time.txt" lake build > "$RUN_DIR/build.log" 2>&1
/usr/bin/time -v -o "$RUN_DIR/audit-time.txt" lake env lean Audit.lean > "$RUN_DIR/audit.log" 2>&1
# Recompute the 40 refined matrix/RHS proposals independently on Linux.
/usr/bin/time -v -o "$RUN_DIR/apex-proposal-time.txt" lake env lean tools/ProposeRefinedApexSystem.lean > "$RUN_DIR/apex-system.txt" 2>&1
printf '%s\n' 'Build, axiom audit and refined-system proposal completed.' > "$RUN_DIR/SUCCESS.txt"

#!/usr/bin/env python3
"""Generate and kernel-check the entire S1 vertex-0 subdivision on a CPU node.
No proposed status, JSON margin, or exit code is a mathematical assumption.
Success requires the full-domain Lean theorem and the ordinary axiom audit.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'SparseLowerTail/Section05/S1Replay'
FINAL_SOURCE = '''import SparseLowerTail.Section05.S1Replay.PositiveCoverage

namespace SparseLowerTail.Section05.S1Replay

theorem ordered_positive {q : EdgeTriple} (hq : q∈orderedLogDomain coverS1Q) :
    0<logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  have hc := orderedLogDomain_subset_cube coverS1Q hq
  have hb : q∈Coverage.initialBox.region := by
    intro i
    fin_cases i
    · simpa [Coverage.initialBox,edgeCoordinate,coverS1Q] using hc.1
    · simpa [Coverage.initialBox,edgeCoordinate,coverS1Q] using hc.2.1
    · simpa [Coverage.initialBox,edgeCoordinate,coverS1Q] using hc.2.2
  exact PositiveCoverage.positive hb hq

theorem full_cube_positive {u : EdgeTriple}
    (hu : u∈edgeCube (Real.exp (-coverS1Q))) :
    0<coverCertificate coverS1Theta coverS1Lam u coverS1Vertex0 :=
  coverCertificate_pos_of_orderedLog coverS1Theta coverS1Lam coverS1Vertex0
    coverS1Q (fun _ hq => ordered_positive hq) u hu

end SparseLowerTail.Section05.S1Replay
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--logs', required=True, type=Path)
    args = parser.parse_args()
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    status = {'scope': 'S1 first parameter vertex; full edge cube only',
              'trust_status': 'Pending Lean build and axiom audit', 'phase': 'generate'}
    def record():
        status['seconds'] = time.monotonic() - started
        (logs/'s1-status.json').write_text(json.dumps(status, indent=2)+'\n')
        print(json.dumps(status), flush=True)
    def run(argv, filename):
        with (logs/filename).open('w') as log:
            subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    record()
    run([sys.executable, 'tools/generate_s1_replay_data.py'], 's1-generate-data.log')
    for batch in range(120):
        run([sys.executable, 'tools/generate_s1_replay_batch.py', str(batch)],
            's1-generate-batch.log')
        if batch % 20 == 19:
            status['generated_batches'] = batch + 1
            record()
    run([sys.executable, 'tools/generate_s1_replay_coverage.py'], 's1-generate-coverage.log')
    run([sys.executable, 'tools/generate_s1_replay_positive_coverage.py'], 's1-generate-positive.log')
    (OUT/'FullCube.lean').write_text(FINAL_SOURCE)
    status['phase'] = 'kernel_build'
    record()
    run(['lake', 'build', 'SparseLowerTail.Section05.S1Replay.FullCube'], 's1-build.log')
    status['phase'] = 'axiom_audit'
    record()
    audit = (ROOT/'Audit.lean').read_text()
    if not audit.startswith('import SparseLowerTail\n'):
        raise ValueError('Unexpected audit header; do not weaken the audit')
    audit = audit.replace('import SparseLowerTail\n',
        'import SparseLowerTail.Section05.S1Replay.FullCube\n', 1)
    audit_path = logs/'AuditS1.lean'
    audit_path.write_text(audit)
    run(['lake', 'env', 'lean', str(audit_path)], 's1-audit.log')
    status.update(phase='complete', trust_status='Lean full-cube theorem compiled and axiom audit passed')
    record()
    (logs/'S1_SUCCESS.txt').write_text('Full S1 vertex-0 cube theorem and axiom audit passed.\n')

if __name__ == '__main__':
    main()

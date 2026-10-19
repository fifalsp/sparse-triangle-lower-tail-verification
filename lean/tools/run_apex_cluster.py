#!/usr/bin/env python3
"""Generate, compile and audit the full F1 apex subdivision on a CPU node."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--logs', required=True, type=Path)
    args = parser.parse_args()
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    status = {'scope': 'F1 full apex cube, nonnegativity and zero-to-pattern implication',
              'phase': 'generate', 'trust_status': 'Pending Lean build and axiom audit'}

    def record():
        status['seconds'] = time.monotonic()-start
        (logs/'apex-status.json').write_text(json.dumps(status, indent=2)+'\n')
        print(json.dumps(status), flush=True)

    def run(argv, filename):
        with (logs/filename).open('w') as output:
            subprocess.run(argv, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=True)

    record()
    run([sys.executable, 'tools/generate_apex_replay.py',
         'data/apex-f1-subdivision-proposal.json'], 'apex-generation.log')
    status['phase'] = 'kernel_build'
    record()
    run(['lake', 'build', 'SparseLowerTail.Section05.ApexReplay.F1.FullCube'], 'apex-build.log')
    status['phase'] = 'axiom_audit'
    record()
    audit = (ROOT/'Audit.lean').read_text()
    if not audit.startswith('import SparseLowerTail\n'):
        raise ValueError('Unexpected audit header; do not weaken the audit')
    audit = audit.replace('import SparseLowerTail\n',
        'import SparseLowerTail.Section05.ApexReplay.F1.FullCube\n', 1)
    audit_path = logs/'AuditApex.lean'
    audit_path.write_text(audit)
    run(['lake', 'env', 'lean', str(audit_path)], 'apex-audit.log')
    status.update(phase='complete', trust_status='Full F1 apex theorem compiled and axiom audit passed')
    record()
    (logs/'APEX_SUCCESS.txt').write_text('Full F1 apex cube theorem and axiom audit passed.\n')


if __name__ == '__main__':
    main()

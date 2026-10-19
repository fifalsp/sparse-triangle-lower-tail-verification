#!/usr/bin/env python3
"""Full ABB neighborhood replay, bounded build concurrency, and axiom audit."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
TARGET = 'SparseLowerTail.Section08.FamilyABBReplay.Full.FullNeighborhood'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--logs',required=True,type=Path)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--lean-threads',type=int,default=2)
    args = p.parse_args()
    logs = args.logs.resolve()
    logs.mkdir(parents=True,exist_ok=True)
    start = time.monotonic()
    status = {'scope':'Full ABB logarithmic contact cube radius 1/10, L in [3.9,9.5]',
              'trust_status':'Pending full Lean build and axiom audit'}
    def record(phase):
        status.update(phase=phase,seconds=time.monotonic()-start)
        (logs/'family-abb-status.json').write_text(json.dumps(status,indent=2)+'\n')
        print(json.dumps(status),flush=True)
    def run(argv,name):
        with (logs/name).open('w') as out:
            subprocess.run(argv,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,check=True)
    record('generate')
    run([sys.executable,'tools/generate_family_abb_replay.py',
         'data/family-abb-subdivision-proposal.json.gz'],'family-abb-generation.log')
    record('bounded_kernel_build')
    run([sys.executable,'tools/build_bounded.py',TARGET,'--logs',str(logs/'family-build'),
         '--workers',str(args.workers),'--lean-threads',str(args.lean_threads)],'family-abb-build.log')
    record('axiom_audit')
    audit = (ROOT/'Audit.lean').read_text()
    if not audit.startswith('import SparseLowerTail\n'):
        raise ValueError('Unexpected audit header; do not weaken the audit')
    audit = audit.replace('import SparseLowerTail\n','import '+TARGET+'\n',1)
    audit_path = logs/'AuditFamilyABB.lean'
    audit_path.write_text(audit)
    run(['lake','env','lean',str(audit_path)],'family-abb-audit.log')
    status['trust_status'] = 'Full ABB neighborhood compiled and axiom audit passed; exterior remains separate'
    record('complete')
    (logs/'FAMILY_ABB_SUCCESS.txt').write_text('Full ABB neighborhood and axiom audit passed.\n')


if __name__ == '__main__':
    main()

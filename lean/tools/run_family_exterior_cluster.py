#!/usr/bin/env python3
"""Full exterior replay, bounded build concurrency, and axiom audit.

The resulting compact certificate still explicitly requires FamilyABBLocal."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
TARGET = 'SparseLowerTail.Section08.FamilyExteriorReplay.Full.CompactCertificate'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--logs',required=True,type=Path)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--lean-threads',type=int,default=2)
    args = p.parse_args()
    logs = args.logs.resolve()
    logs.mkdir(parents=True,exist_ok=True)
    start = time.monotonic()
    status = {'scope':'Full ordered compact family q in [0,12]^3, L in [3.9,9.5]; conditional on internal ABB local result',
              'trust_status':'Pending full Lean build and axiom audit'}
    def record(phase):
        status.update(phase=phase,seconds=time.monotonic()-start)
        (logs/'family-exterior-status.json').write_text(json.dumps(status,indent=2)+'\n')
        print(json.dumps(status),flush=True)
    def run(argv,name):
        with (logs/name).open('w') as out:
            subprocess.run(argv,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,check=True)
    record('generate')
    run([sys.executable,'tools/generate_family_exterior_replay.py',
         'data/family-exterior-subdivision-proposal.json.gz','--full'],'family-exterior-generation.log')
    record('bounded_kernel_build')
    run([sys.executable,'tools/build_bounded.py',TARGET,'--logs',str(logs/'exterior-build'),
         '--workers',str(args.workers),'--lean-threads',str(args.lean_threads)],'family-exterior-build.log')
    record('axiom_audit')
    audit = (ROOT/'Audit.lean').read_text()
    if not audit.startswith('import SparseLowerTail\n'):
        raise ValueError('Unexpected audit header; do not weaken the audit')
    audit = audit.replace('import SparseLowerTail\n','import '+TARGET+'\n',1)
    audit_path = logs/'AuditFamilyExterior.lean'
    audit_path.write_text(audit)
    run(['lake','env','lean',str(audit_path)],'family-exterior-audit.log')
    status['trust_status'] = 'Full exterior replay compiled and axiom audit passed; ABB remains an internal premise'
    record('complete')
    (logs/'FAMILY_EXTERIOR_SUCCESS.txt').write_text('Full exterior replay and axiom audit passed; ABB local theorem remains required.\n')


if __name__ == '__main__':
    main()

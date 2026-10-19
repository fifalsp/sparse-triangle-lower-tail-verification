#!/usr/bin/env python3
"""Search, kernel-check, and audit one actual full nonapex cover job on a CPU node."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--job',required=True,type=int,choices=range(36))
    p.add_argument('--logs',required=True,type=Path)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--lean-threads',type=int,default=2)
    args = p.parse_args()
    logs = args.logs.resolve()
    logs.mkdir(parents=True,exist_ok=True)
    start = time.monotonic()
    status = dict(job=args.job,scope='Full actual ordered domain of one nonapex job',
                  phase='generate',trust_status='Pending full Lean build and axiom audit')

    def record():
        status['seconds'] = time.monotonic()-start
        (logs/'cover-job-status.json').write_text(json.dumps(status,indent=2)+'\n')
        print(json.dumps(status),flush=True)

    def run(command, name):
        with (logs/name).open('w') as output:
            subprocess.run(command,cwd=ROOT,stdout=output,stderr=subprocess.STDOUT,check=True)

    proposal = ROOT/f'data/cover-job-{args.job:02d}-subdivision-proposal.json.gz'
    record()
    run([sys.executable,'tools/generate_cover_job_replay.py',str(proposal),'--full'],
        'cover-job-generation.log')
    target = f'SparseLowerTail.Section05.CoverJobReplay.Job{args.job:02d}Full.Ordered'
    status['phase'] = 'bounded_kernel_build'
    record()
    run([sys.executable,'tools/build_bounded.py',target,'--logs',str(logs/'cover-build'),
         '--workers',str(args.workers),'--lean-threads',str(args.lean_threads)],'cover-job-build.log')
    status['phase'] = 'axiom_audit'
    record()
    audit = (ROOT/'Audit.lean').read_text()
    if not audit.startswith('import SparseLowerTail\n'):
        raise ValueError('Unexpected audit header; do not weaken the audit')
    path = logs/'AuditCoverJob.lean'
    path.write_text(audit.replace('import SparseLowerTail\n','import '+target+'\n',1))
    run(['lake','env','lean',str(path)],'cover-job-audit.log')
    status.update(phase='complete',trust_status='Full ordered job theorem compiled and axiom audit passed')
    record()
    (logs/'COVER_JOB_SUCCESS.txt').write_text(target+' compiled and passed the axiom audit.\n')


if __name__ == '__main__':
    main()

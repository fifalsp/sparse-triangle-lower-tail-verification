#!/usr/bin/env python3
"""Resume only a clean timeout; skip a finished proof and reject other failures."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile

from resume_assembly import COMMIT, REQUIRED, TARGET, prior_evidence

MANIFEST_SHA = 'b14aedaa8bc2447939e456b80e112b138b16348085539f108bff0f6134514811'


def decision(archive, state, exit_code):
    if state not in ('FAILED', 'COMPLETED'):
        raise ValueError('Predecessor is not an eligible ended job')
    with tarfile.open(archive, 'r:gz') as stream:
        names = set(stream.getnames())
        def read(name):
            return stream.extractfile('logs/' + name).read()
        manifest = read('source-manifest.json')
        if hashlib.sha256(manifest).hexdigest() != MANIFEST_SHA:
            raise ValueError('Combined source manifest changed')
        if read('source-commit.txt').decode().strip() != COMMIT:
            raise ValueError('Proof source revision changed')
        status = json.loads(read('combined-build/status.json'))
        inputs = json.loads(read('assembly-inputs.json'))
        if (status['target'] != TARGET or status['total'] != 94032 or status['failed']
                or inputs['missing'] or not REQUIRED <= inputs['selected'].keys()):
            raise ValueError('Combined dependency gate failed')
        recorded_exit = read('exit-code.txt').strip()
        if state == 'FAILED' and exit_code == '124:0' and recorded_exit == b'124':
            if 'logs/ASSEMBLY_SUCCESS.txt' in names:
                raise ValueError('Contradictory timeout and success evidence')
            prior_evidence(archive)
            return 'resume'
        if state == 'COMPLETED' and exit_code == '0:0' and recorded_exit == b'0':
            for name in ('ASSEMBLY_SUCCESS.txt', 'SUCCESS.txt', 'source-hashes-passed.txt'):
                if not read(name).strip():
                    raise ValueError('Missing final success evidence')
            if (status['phase'] != 'build_complete' or status['completed'] != status['total']
                    or not re.search(rb'Axiom audit passed: [1-9][0-9]* project declarations, '
                                     rb'[1-9][0-9]* theorems; only propext, Classical.choice, '
                                     rb'Quot.sound allowed\.', read('combined-audit.log'))):
                raise ValueError('Full target or original audit did not pass')
            # Skip duplicate work. Independent archive acceptance is still required.
            return 'finished'
    raise ValueError('Predecessor did not end with a clean timeout or audited success')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('archive', type=Path)
    p.add_argument('state')
    p.add_argument('exit_code')
    a = p.parse_args()
    print(decision(a.archive, a.state, a.exit_code))


if __name__ == '__main__':
    main()

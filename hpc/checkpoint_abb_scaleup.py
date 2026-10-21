#!/usr/bin/env python3
"""Drain the explicitly selected ABB coordinator and preserve a stable checkpoint.

Only the scheduler pauses; its already-running Lean children may finish. On
failure the scheduler is resumed. On success it stays paused for handoff.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

AUDIT_SHA = '956129721ba7190769a93bd755dde91ac7b4fcd15326656721cc822308cc9014'


def matching_scheduler(argv, work):
    expected = str(work / 'repo/hpc/build_ready_batches.py')
    return len(argv) > 1 and argv[1] == expected and '--logs' in argv and str(work / 'logs/family-build') in argv


def process_table():
    result = {}
    for path in Path('/proc').glob('[0-9]*'):
        try:
            if path.stat().st_uid != os.getuid():
                continue
            status = dict(line.split(':', 1) for line in (path/'status').read_text().splitlines() if ':' in line)
            result[int(path.name)] = dict(ppid=int(status['PPid'].strip()), state=status['State'].strip()[0],
                                         argv=(path/'cmdline').read_bytes().decode().split('\0')[:-1])
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
    return result


def active_descendants(table, pid):
    descendants = {pid}
    while True:
        expanded = descendants | {p for p, row in table.items() if row['ppid'] in descendants}
        if expanded == descendants:
            return [p for p in descendants - {pid} if table[p]['state'] not in ('Z', 'X')]
        descendants = expanded


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(8*1024*1024), b''):
            digest.update(block)
    return digest.hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work', type=Path, required=True)
    p.add_argument('--handoff', type=Path, required=True)
    p.add_argument('--job', required=True)
    a = p.parse_args()
    work, handoff = a.work.resolve(), a.handoff.resolve()
    if os.environ.get('SLURM_JOB_ID') != a.job or work.name.split('-')[2] != a.job:
        raise ValueError('Checkpoint must run inside the selected ABB allocation')
    if (handoff/'checkpoint.json').exists() or not (handoff/'replacement-ready.txt').exists():
        raise ValueError('Replacement readiness missing or handoff already exists')
    matches = [pid for pid, row in process_table().items() if matching_scheduler(row['argv'], work)]
    if len(matches) != 1:
        raise ValueError('Expected exactly one matching ABB scheduler')
    pid = matches[0]
    def interrupted(signum, frame):
        raise RuntimeError("Checkpoint interrupted by signal " + str(signum))
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    success = False
    os.kill(pid, signal.SIGSTOP)
    try:
        deadline = time.monotonic()+300
        while True:
            table = process_table()
            if pid not in table or table[pid]['state'] != 'T':
                raise ValueError('Selected scheduler is not paused')
            active = active_descendants(table, pid)
            print(json.dumps(dict(phase='draining', scheduler_pid=pid, active_children=active)), flush=True)
            if not active:
                break
            if time.monotonic() >= deadline:
                raise TimeoutError('Active Lean children did not drain')
            time.sleep(5)
        repo = work/'repo'
        manifest = json.loads((work/'logs/source-manifest.json').read_text())
        for name, expected in manifest.items():
            if sha256(repo/'lean'/Path(name.replace('.', '/')).with_suffix('.lean')) != expected:
                raise ValueError('Proof source changed: '+name)
        if sha256(repo/'lean/Audit.lean') != AUDIT_SHA:
            raise ValueError('Audit policy changed')
        archive = handoff/'abb-consistent-checkpoint.tar.gz'
        if archive.exists():
            raise ValueError('Refusing to replace a checkpoint')
        partial = archive.with_suffix('.gz.partial')
        with partial.open('wb') as output:
            tar = subprocess.Popen(['tar','-cf','-','-C',str(repo),'lean/.lake/build','lean/SparseLowerTail','SOURCE_COMMIT'], stdout=subprocess.PIPE)
            gzip = subprocess.run(['gzip','-1'], stdin=tar.stdout, stdout=output)
            tar.stdout.close()
            tar_rc = tar.wait()
            if gzip.returncode or tar_rc:
                raise RuntimeError('Checkpoint archive failed')
        partial.rename(archive)
        (handoff/'source-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
        build = json.loads((work/'logs/family-build/status.json').read_text())
        record = dict(old_job=a.job, scheduler_pid=pid, old_work=str(work), archive=str(archive),
                      archive_sha256=sha256(archive), source_commit=(repo/'SOURCE_COMMIT').read_text().strip(),
                      source_manifest_sha256=sha256(handoff/'source-manifest.json'),
                      preserved_module_count=build['completed'], total=build['total'], source_files=len(manifest),
                      audit_sha256=AUDIT_SHA, trust_status='Preserved partial cache; full target/audit still required')
        temporary = handoff/'checkpoint.json.partial'
        temporary.write_text(json.dumps(record, indent=2)+'\n')
        temporary.rename(handoff/'checkpoint.json')
        print(json.dumps(record), flush=True)
        success = True
    finally:
        if not success:
            try:
                os.kill(pid, signal.SIGCONT)
            except ProcessLookupError:
                pass


if __name__ == '__main__': main()

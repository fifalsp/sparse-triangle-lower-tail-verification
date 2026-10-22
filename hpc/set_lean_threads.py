#!/usr/bin/env python3
"""Atomically use spare allocated CPU cores without changing proof inputs."""
import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re

AUDIT_SHA = '956129721ba7190769a93bd755dde91ac7b4fcd15326656721cc822308cc9014'


def revised_profile(before, old_threads, threads, workers, allocated_cpus):
    if min(old_threads, threads, workers, allocated_cpus) < 1:
        raise ValueError('Resource counts must be positive')
    if workers * threads > allocated_cpus:
        raise ValueError('Threads exceed the existing CPU allocation')
    matches = list(re.finditer(r'^weakLeanArgs\s*=\s*(\[[^\n]*\])\s*$', before, re.M))
    if len(matches) != 1:
        raise ValueError('Ambiguous resource profile')
    args = ast.literal_eval(matches[0].group(1))
    if args != ['-M49152', f'-j{old_threads}', '-s65536']:
        raise ValueError('Unexpected existing resource limits')
    token = f'"-j{old_threads}"'
    if before.count(token) != 1:
        raise ValueError('Ambiguous thread setting')
    after = before.replace(token, f'"-j{threads}"', 1)
    if after.replace(f'"-j{threads}"', token, 1) != before:
        raise ValueError('A setting other than the thread count changed')
    return after


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--logs', type=Path, required=True)
    p.add_argument('--threads', type=int, required=True)
    p.add_argument('--expected-threads', type=int, default=1)
    p.add_argument('--workers', type=int, default=6)
    p.add_argument('--allocated-cpus', type=int, default=12)
    a = p.parse_args()
    repo, logs = a.repo.resolve(), a.logs.resolve()
    profile = repo / 'lean/lakefile.yale.toml'
    if profile.is_symlink():
        raise ValueError('Resource profile must be a regular local file')
    audit = repo / 'lean/Audit.lean'
    if hashlib.sha256(audit.read_bytes()).hexdigest() != AUDIT_SHA:
        raise ValueError('Original audit policy does not match')
    manifest = (logs / 'source-manifest.json').read_bytes()
    before = profile.read_text()
    after = revised_profile(before, a.expected_threads, a.threads,
                            a.workers, a.allocated_cpus)
    logs.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    (logs / f'lakefile-before-threads-{stamp}.toml').write_text(before)
    pending = profile.with_name(profile.name + f'.threads-{os.getpid()}.tmp')
    pending.write_text(after)
    os.replace(pending, profile)
    if (hashlib.sha256(audit.read_bytes()).hexdigest() != AUDIT_SHA
            or (logs / 'source-manifest.json').read_bytes() != manifest):
        profile.write_text(before)
        raise ValueError('Audit policy or source manifest changed during adjustment')
    record = dict(checked_at_utc=stamp, workers=a.workers,
                  lean_threads=a.threads, previous_lean_threads=a.expected_threads,
                  allocated_cpus=a.allocated_cpus, memory_mib_per_process=49152,
                  stack_kib=65536, audit_sha256=AUDIT_SHA,
                  source_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
                  before_profile_sha256=hashlib.sha256(before.encode()).hexdigest(),
                  after_profile_sha256=hashlib.sha256(after.encode()).hexdigest(),
                  proof_sources_written=[], audit_policy_written=False,
                  note='Only the weakLeanArgs thread count changed. Existing processes continue; new Lean invocations use the new thread count.')
    (logs / f'thread-adjustment-{stamp}.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record), flush=True)


if __name__ == '__main__':
    main()

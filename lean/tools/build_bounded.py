#!/usr/bin/env python3
"""Build a local Lean module dependency graph with bounded Lake processes.

Each project module is built only after its project imports have succeeded.
Cached mathlib imports remain Lake's responsibility. This avoids launching
hundreds of independent generated proof modules through one aggregate target.
No proof is accepted here: Lake/Lean must exit successfully for every module.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import heapq
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def dependency_graph(target):
    graph = {}
    def visit(module):
        if module in graph:
            return
        path = ROOT/Path(module.replace('.','/')).with_suffix('.lean')
        if not path.is_file():
            raise ValueError(f'Missing project module {module}')
        imports = []
        for line in path.read_text().splitlines():
            match = re.match(r'^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$',line)
            if match:
                for name in match.group(1).split():
                    if name == 'SparseLowerTail' or name.startswith('SparseLowerTail.'):
                        imports.append(name)
        graph[module] = set(imports)
        for name in imports:
            visit(name)
    visit(target)
    return graph



def verified_cached_modules(graph, root, check, batch_size=128):
    """Reuse only modules whose whole batch Lake validates without rebuilding.

    Artifact existence merely selects candidates. A failed batch contributes
    nothing; those modules use the ordinary bounded build path. Retain a
    dependency-closed subset so no completed node hides an unchecked import.
    """
    candidates = sorted(m for m in graph if
        (root/'.lake/build/lib/lean'/Path(m.replace('.','/')).with_suffix('.olean')).is_file())
    accepted = set()
    for offset in range(0,len(candidates),batch_size):
        batch = candidates[offset:offset+batch_size]
        if check(batch):
            accepted.update(batch)
    while True:
        closed = {m for m in accepted if graph[m] <= accepted}
        if closed == accepted:
            return accepted
        accepted = closed


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('target')
    p.add_argument('--logs',required=True,type=Path)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--lean-threads',type=int,default=1)
    p.add_argument('--dry-run',action='store_true')
    p.add_argument('--no-cache-precheck',action='store_true',
                   help='Use one bounded Lake invocation per project module, including cached modules')
    args = p.parse_args()
    if not 1 <= args.workers <= 8 or not 1 <= args.lean_threads <= 8:
        p.error('workers and lean-threads must be in 1..8')
    graph = dependency_graph(args.target)
    # Reject cycles before launching anything. The live scheduler repeats the
    # indegree calculation to keep its completion state separate from planning.
    planned, todo = set(),dict(graph)
    while todo:
        ready = {m for m,deps in todo.items() if deps <= planned}
        if not ready:
            raise ValueError('Cycle in project imports')
        planned.update(ready)
        for m in ready:
            del todo[m]
    logs = args.logs.resolve()
    logs.mkdir(parents=True,exist_ok=True)
    (logs/'plan.json').write_text(json.dumps({'target':args.target,'modules':len(graph),
        'workers':args.workers,'lean_threads':args.lean_threads,
        'dependencies':{m:sorted(d) for m,d in sorted(graph.items())}},indent=2)+'\n')
    if args.dry_run:
        print(json.dumps({'phase':'plan_only','modules':len(graph),'target':args.target}))
        return
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = str(args.lean_threads)
    start = time.monotonic()
    cache_checks = []
    def check_cache(batch):
        filename = logs/f'cache-check-{len(cache_checks):04d}.log'
        with filename.open('w') as output:
            rc = subprocess.run(['lake','--no-build','build',*batch],cwd=ROOT,env=env,
                                stdout=output,stderr=subprocess.STDOUT).returncode
        cache_checks.append(dict(modules=batch,exit_code=rc,log=filename.name))
        (logs/'cache-checks.json').write_text(json.dumps(cache_checks,indent=2)+'\n')
        return rc == 0
    cached = set() if args.no_cache_precheck else verified_cached_modules(graph,ROOT,check_cache)
    completed, failed = set(cached),{}
    dependents = {m:[] for m in graph}
    indegree = {m:len(d-completed) for m,d in graph.items()}
    for m,deps in graph.items():
        for d in deps:
            dependents[d].append(m)
    ready = [m for m,d in indegree.items() if d == 0 and m not in completed]
    heapq.heapify(ready)
    def run(module):
        filename = logs/(module+'.log')
        with filename.open('w') as output:
            rc = subprocess.run(['lake','build',module],cwd=ROOT,env=env,
                                stdout=output,stderr=subprocess.STDOUT).returncode
        return rc
    def record(phase,active):
        status = {'phase':phase,'target':args.target,'total':len(graph),
            'completed':len(completed),'cached':len(cached),'failed':failed,'active':sorted(active),
            'seconds':time.monotonic()-start,'workers':args.workers,
            'trust_status':'Build scheduling only; final axiom audit is separate'}
        (logs/'status.json').write_text(json.dumps(status,indent=2)+'\n')
        print(json.dumps(status),flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        active = {}
        last_report = start
        while ready or active:
            while ready and len(active)<args.workers and not failed:
                m = heapq.heappop(ready)
                active[pool.submit(run,m)] = m
            if not active:
                break
            done,_ = wait(active,timeout=30,return_when=FIRST_COMPLETED)
            for future in done:
                m = active.pop(future)
                rc = future.result()
                if rc:
                    failed[m] = rc
                else:
                    completed.add(m)
                    for nxt in dependents[m]:
                        if nxt in completed:
                            continue
                        indegree[nxt] -= 1
                        if indegree[nxt] == 0:
                            heapq.heappush(ready,nxt)
            if failed or time.monotonic()-last_report >= 30:
                record('build_failed' if failed else 'building',active.values())
                last_report = time.monotonic()
        record('build_complete' if len(completed)==len(graph) and not failed else 'build_failed',[])
    if failed or len(completed)!=len(graph):
        raise SystemExit(1)


if __name__ == '__main__':
    main()

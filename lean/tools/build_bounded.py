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


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('target')
    p.add_argument('--logs',required=True,type=Path)
    p.add_argument('--workers',type=int,default=2)
    p.add_argument('--lean-threads',type=int,default=1)
    p.add_argument('--dry-run',action='store_true')
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
    completed, failed = set(),{}
    dependents = {m:[] for m in graph}
    indegree = {m:len(d) for m,d in graph.items()}
    for m,deps in graph.items():
        for d in deps:
            dependents[d].append(m)
    ready = [m for m,d in indegree.items() if d == 0]
    heapq.heapify(ready)
    def run(module):
        filename = logs/(module+'.log')
        with filename.open('w') as output:
            rc = subprocess.run(['lake','build',module],cwd=ROOT,env=env,
                                stdout=output,stderr=subprocess.STDOUT).returncode
        return rc
    def record(phase,active):
        status = {'phase':phase,'target':args.target,'total':len(graph),
            'completed':len(completed),'failed':failed,'active':sorted(active),
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

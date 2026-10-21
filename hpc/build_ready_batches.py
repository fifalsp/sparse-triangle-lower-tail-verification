#!/usr/bin/env python3
"""Validate cached Lean modules only after their project imports are checked.

This scheduler is for cluster resumptions. It leaves the existing laptop
scheduler untouched. Every accepted cache batch must pass Lake --no-build;
all other modules must pass an ordinary bounded Lake build.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time


def build_graph(graph, cached_candidates, check, build, workers, report):
    completed = set()
    while len(completed) < len(graph):
        ready = sorted(m for m, deps in graph.items()
                       if m not in completed and deps <= completed)
        if not ready:
            raise ValueError('Cycle or missing project import in dependency graph')
        reusable = set()
        candidates = [m for m in ready if m in cached_candidates]
        for offset in range(0, len(candidates), 128):
            batch = candidates[offset:offset + 128]
            if check(batch) == 0:
                reusable.update(batch)
        completed.update(reusable)
        report(completed, reusable, {})
        pending = [m for m in ready if m not in reusable]
        with ThreadPoolExecutor(max_workers=workers) as pool:
            # Fill each freed worker immediately; a slow sibling must not
            # leave the rest idle until an entire fixed-size batch finishes.
            pending_iter = iter(pending)
            active = {}
            failures = {}
            while True:
                while len(active) < workers and not failures:
                    name = next(pending_iter, None)
                    if name is None:
                        break
                    active[pool.submit(build, name)] = name
                if not active:
                    break
                done, _ = wait(active, return_when=FIRST_COMPLETED)
                for future in done:
                    name = active.pop(future)
                    rc = future.result()
                    if rc:
                        failures[name] = rc
                    else:
                        completed.add(name)
                report(completed, reusable, failures)
            if failures:
                raise RuntimeError('Lean build failed: ' + repr(failures))
    return completed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--target', required=True)
    parser.add_argument('--logs', type=Path, required=True)
    parser.add_argument('--lakefile', type=Path, required=True)
    parser.add_argument('--workers', type=int, choices=range(1, 9), default=3)
    args = parser.parse_args()
    root = args.repo.resolve() / 'lean'
    spec = importlib.util.spec_from_file_location('bounded_plan', root / 'tools/build_bounded.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    graph = module.dependency_graph(args.target)
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=False)
    lake = ['lake', '--file', str(args.lakefile.resolve())]
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    start = time.monotonic()
    checks, reused = [], set()
    (logs / 'plan.json').write_text(json.dumps({
        'target': args.target, 'modules': len(graph), 'workers': args.workers,
        'dependencies': {m: sorted(d) for m, d in sorted(graph.items())}}, indent=2) + '\n')
    def invoke(argv, filename):
        with (logs / filename).open('w') as output:
            return subprocess.run([*lake, *argv], cwd=root, env=env,
                                  stdout=output, stderr=subprocess.STDOUT).returncode
    def check(batch):
        filename = f'cache-check-{len(checks):04d}.log'
        rc = invoke(['--no-build', 'build', *batch], filename)
        checks.append(dict(modules=batch, exit_code=rc, log=filename))
        (logs / 'cache-checks.json').write_text(json.dumps(checks, indent=2) + '\n')
        return rc
    def report(completed, accepted, failed):
        reused.update(accepted)
        status = dict(target=args.target, total=len(graph), completed=len(completed),
                      cached=len(reused), failed=failed, seconds=time.monotonic()-start,
                      workers=args.workers,
                      phase='build_failed' if failed else
                            'build_complete' if len(completed) == len(graph) else 'building',
                      trust_status='Final full target build, source hashes and axiom audit remain required')
        (logs / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
        print(json.dumps(status), flush=True)
    candidates = {m for m in graph if
                  (root / '.lake/build/lib/lean' / Path(m.replace('.', '/')).with_suffix('.olean')).is_file()}
    build_graph(graph, candidates, check,
                lambda m: invoke(['build', m], m + '.log'), args.workers, report)
    # Explicitly revalidate the aggregate after every project module succeeded.
    aggregate_rc = invoke(['build', args.target], 'full-target.log')
    if aggregate_rc:
        report(set(graph), set(), {args.target: aggregate_rc})
        raise RuntimeError('Final aggregate target failed')


if __name__ == '__main__':
    main()

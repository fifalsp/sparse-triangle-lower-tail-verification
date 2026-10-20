#!/usr/bin/env python3
"""Resume an unfinished replay after its original Slurm allocation has ended."""
import argparse, json, shutil, subprocess, sys, tarfile
from pathlib import Path
from audit_result_archives import inspect

ROOT=Path(__file__).resolve().parents[1]
def restore(archive, root):
 # Restore build cache only. Current source and generators remain authoritative;
 # Lake must revalidate every cached module against them.
 with tarfile.open(archive,'r|gz') as t:
  for m in t:
   if not m.isfile() or not m.name.startswith('lean/.lake/build/'): continue
   parts=Path(m.name).parts
   if '..' in parts: raise ValueError('Unsafe checkpoint path')
   dest=root/m.name;dest.parent.mkdir(parents=True,exist_ok=True)
   with dest.open('wb') as out: shutil.copyfileobj(t.extractfile(m),out)

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--task',type=int,required=True);p.add_argument('--save',type=Path,required=True);p.add_argument('--logs',type=Path,required=True);p.add_argument('--check-only',action='store_true');a=p.parse_args()
 task=json.loads((ROOT/'hpc/recovery-manifest-20261019.json').read_text())['tasks'][a.task]
 old=a.save/f'sparse-lean-results-{task["old_job"]}.tar.gz'
 if old.exists():
  result=inspect(old.read_bytes(),old.name)
  if result and result.get('verified'):
   if result['key']!=task['key']: raise ValueError('Wrong original job result')
   print('Original full theorem and audit succeeded; no duplicate replay.',flush=True)
   a.logs.mkdir(parents=True,exist_ok=True)
   (a.logs/'ORIGINAL_SUCCESS.json').write_text(json.dumps(result,indent=2)+'\n')
   return
 if a.check_only: sys.exit(10)
 for name in task['checkpoints']:
  path=a.save/name
  if path.is_file():
   print('Restoring checkpoint cache:',name,flush=True);restore(path,ROOT);break
 kind,_,number=task['key'].partition(':')
 cmd=[sys.executable]
 if kind=='cover': cmd+=['tools/run_cover_job_cluster.py','--job',number]
 elif kind=='apex': cmd+=['tools/run_apex_cluster.py','--fan',number]
 elif kind=='abb': cmd+=['tools/run_family_abb_cluster.py']
 elif kind=='exterior': cmd+=['tools/run_family_exterior_cluster.py']
 else: raise ValueError(kind)
 # Eight independent single-thread processes, never an unbounded aggregate build.
 cmd+=['--logs',str(a.logs.resolve()),'--workers','8','--lean-threads','1']
 subprocess.run(cmd,cwd=ROOT/'lean',check=True)
 (a.logs/'SUCCESS.txt').write_text('Recovery full target build and axiom audit passed.\n')
if __name__=='__main__': main()

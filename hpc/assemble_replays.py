#!/usr/bin/env python3
"""Assemble all full-domain replay proofs; fail closed on any missing result."""
import argparse, hashlib, importlib.util, json, re, shutil, subprocess, sys, tarfile
from pathlib import Path
from audit_result_archives import inspect
ROOT=Path(__file__).resolve().parents[1]
REQUIRED={*(f'cover:{i}' for i in range(36)),*(f'apex:{i}' for i in range(1,7)),'abb','exterior'}

def generate(selected):
 # Include the current root so author proofs added after the regional source
 # snapshot participate in the combined build and namespace-wide axiom audit.
 imports=['SparseLowerTail','SparseLowerTail.MainReplayAssembly']; nonapex=[];apex=[]
 for j in range(36):
  if selected[f'cover:{j}']['kind']=='s1':
   imports.append('SparseLowerTail.Section05.S1Replay.FullCube')
   nonapex.append('''  · have hq' : q ∈ orderedLogDomain coverS1Q := by
      simpa [nonapexCell_s1, cellQ, coverS1Q] using hq
    simpa [nonapexCell_s1, coverCellTheta, fixedCellTheta_s1,
      cellLambda_s1, nonapexVertex_s1] using S1Replay.ordered_positive hq' ''')
  else:
   imports.append(f'SparseLowerTail.Section05.CoverJobReplay.Job{j:02d}Full.Ordered')
   nonapex.append(f'  · exact CoverJobReplay.Job{j:02d}Full.ordered hq')
 for i in range(1,7):
  imports.append(f'SparseLowerTail.Section05.ApexReplay.F{i}.FullCube')
  apex.append(f'  · exact ApexReplay.F{i}.ordered hq')
 imports+=['SparseLowerTail.Section08.FamilyABBReplay.Full.FullNeighborhood',
  'SparseLowerTail.Section08.FamilyABBRadiusReplay.Full.FullNeighborhood',
  'SparseLowerTail.Section08.FamilyExteriorReplay.Full.CompactCertificate']
 return '\n'.join('import '+i for i in imports)+'''
noncomputable section
namespace SparseLowerTail.CompletedReplays
open Section02 Section04 Section05 Section07 Section08 Certificate Section05.CoverGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem all_nonapex : NonapexJobResults := by
  intro j q hq
  fin_cases j
'''+ '\n'.join(nonapex)+'''

theorem all_apex : ApexJobResults := by
  intro i q hq
  fin_cases i
'''+ '\n'.join(apex)+'''

theorem full_abb : FamilyABBLocal := by
  intro z hz hL q hq
  exact FamilyABBReplay.Full.local_nonnegative_and_unique_zero hz hL hq

/-- Literal Appendix A.3 ABB Hessian at the exact binary64 radius. -/
theorem full_abb_binary64_hessian {z : ℝ} (hz : 0<z)
    (hL : Numerics.Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z)
      ManuscriptFamilyRadius.binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  FamilyABBRadiusReplay.Full.hessian_positive hz hL hq hv

theorem full_abb_binary64_local {z : ℝ} (hz : 0<z)
    (hL : Numerics.Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z)
      ManuscriptFamilyRadius.binary64Radius) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) :=
  FamilyABBRadiusReplay.Full.local_nonnegative_and_unique_zero hz hL hq

theorem full_compact : CompactFamilyCertificate :=
  FamilyExteriorReplay.Full.compact_certificate full_abb

/-- All internal finite certificate obligations discharged. The seven named
external/classical inputs remain explicit, as in the existing assumptions ledger. -/
theorem mainTheorem
    (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting) : MainTheorem :=
  mainTheorem_of_finite_certificates external hSampling hSpectral hdyadic hcompact hpull hcount
    (criticalClassification_of_ordered_jobs hdyadic hcompact hcount hSampling all_nonapex all_apex)
    full_compact
end SparseLowerTail.CompletedReplays
'''

def restore(path,kind,key):
 # Restrict source extraction to the relevant generated proof subtree. Never
 # overwrite current handwritten source, the audit policy, or the source revision.
 if kind=='s1': sub='Section05/S1Replay/'
 elif kind=='cover':sub=f'Section05/CoverJobReplay/Job{int(key.split(":")[1]):02d}Full/'
 elif kind=='apex':sub=f'Section05/ApexReplay/F{key.split(":")[1]}/'
 elif kind=='abb':sub='Section08/FamilyABBReplay/Full/'
 else:sub='Section08/FamilyExteriorReplay/Full/'
 prefix='lean/SparseLowerTail/'+sub
 with tarfile.open(path,'r|gz') as t:
  for m in t:
   if not m.isfile() or '..' in Path(m.name).parts:continue
   if not (m.name.startswith(prefix) or m.name.startswith('lean/.lake/build/')):continue
   dest=ROOT/m.name;dest.parent.mkdir(parents=True,exist_ok=True)
   with dest.open('wb') as out:shutil.copyfileobj(t.extractfile(m),out)

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--save',type=Path,required=True);p.add_argument('--logs',type=Path,required=True);p.add_argument('--check-only',action='store_true');p.add_argument('--workers',type=int,choices=range(1,9),default=2);p.add_argument('--lakefile',type=Path);p.add_argument('--audit-memory-mib',type=int);p.add_argument('--ready-batches',action='store_true');a=p.parse_args();a.logs.mkdir(parents=True,exist_ok=True)
 selected={}
 for path in sorted(a.save.glob('sparse-lean-results-*.tar.gz')):
  r=inspect(path.read_bytes(),path.name)
  if r and r.get('verified'):selected[r['key']]=r
 missing=sorted(REQUIRED-selected.keys())
 (a.logs/'assembly-inputs.json').write_text(json.dumps(dict(selected=selected,missing=missing),indent=2)+'\n')
 if missing:raise RuntimeError('Missing full theorem/audit results: '+', '.join(missing))
 if a.check_only:return
 for key,r in selected.items():
  j=re.fullmatch(r'sparse-lean-results-(\d+)\.tar\.gz',r['archive'])[1]
  candidates=[f'sparse-lean-recovery-checkpoint-{j}.tar.gz',f'sparse-lean-{r["kind"]}-checkpoint-{j}.tar.gz']
  if r['kind']=='s1':candidates+=[f'sparse-lean-s1-sources-{j}.tar.gz']
  if r['kind']=='apex':candidates+=[f'sparse-lean-apex-sources-{j}.tar.gz']
  if r['kind']=='abb':candidates+=[f'sparse-lean-family-abb-sources-{j}.tar.gz']
  found=next((a.save/n for n in candidates if (a.save/n).is_file()),None)
  if found is None:raise RuntimeError('No proof sources for '+key)
  print('Importing',key,found.name,flush=True);restore(found,r['kind'],key)
 target='SparseLowerTail.CompletedReplays'
 (ROOT/'lean/SparseLowerTail/CompletedReplays.lean').write_text(generate(selected))
 def run(cmd,name):
  with (a.logs/name).open('w') as out:subprocess.run(cmd,cwd=ROOT/'lean',stdout=out,stderr=subprocess.STDOUT,check=True)
 run([sys.executable,'tools/generate_family_abb_radius_replay.py','--mode','full'],'abb-radius-generation.log')
 loader=importlib.util.spec_from_file_location('assembly_plan',ROOT/'lean/tools/build_bounded.py')
 bounded=importlib.util.module_from_spec(loader);loader.loader.exec_module(bounded)
 graph=bounded.dependency_graph(target)
 def manifest():
  return {m:hashlib.sha256((ROOT/'lean'/Path(m.replace('.','/')).with_suffix('.lean')).read_bytes()).hexdigest() for m in sorted(graph)}
 sources=manifest();(a.logs/'source-manifest.json').write_text(json.dumps(sources,indent=2)+'\n')
 audit_source=(ROOT/'lean/Audit.lean').read_bytes()
 config_args=['--lakefile',str(a.lakefile.resolve())] if a.lakefile else []
 if a.ready_batches:
  if not a.lakefile:raise ValueError('Dependency-ready scheduler requires an explicit bounded Lake profile')
  run([sys.executable,str(ROOT/'hpc/build_ready_batches.py'),'--repo',str(ROOT),'--target',target,'--logs',str(a.logs/'combined-build'),'--workers',str(a.workers),*config_args],'combined-build.log')
 else:
  run([sys.executable,'tools/build_bounded.py',target,'--logs',str(a.logs/'combined-build'),'--workers',str(a.workers),'--lean-threads','1',*config_args],'combined-build.log')
 audit=(ROOT/'lean/Audit.lean').read_text()
 if not audit.startswith('import SparseLowerTail\n'):raise ValueError('Unexpected audit header')
 audit_path=a.logs/'AuditCompleted.lean';audit_path.write_text(audit.replace('import SparseLowerTail\n','import '+target+'\n',1))
 lake_args=['--file',str(a.lakefile.resolve())] if a.lakefile else []
 memory_args=['-s65536','-j1']
 if a.audit_memory_mib:memory_args.insert(0,'-M'+str(a.audit_memory_mib))
 run(['lake',*lake_args,'env','lean',*memory_args,str(audit_path)],'combined-audit.log')
 if (ROOT/'lean/Audit.lean').read_bytes()!=audit_source or manifest()!=sources:raise ValueError('Proof source or audit policy changed during combined verification')
 (a.logs/'source-hashes-passed.txt').write_text('All combined target dependency sources and the audit policy unchanged.\n')
 (a.logs/'ASSEMBLY_SUCCESS.txt').write_text('All internal numerical certificates discharged in CompletedReplays.mainTheorem, including the binary64 ABB radius replay; the seven named external/classical inputs remain explicit.\n')
if __name__=='__main__':main()

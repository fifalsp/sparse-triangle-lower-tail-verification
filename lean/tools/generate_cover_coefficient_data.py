#!/usr/bin/env python3
"""Emit exact coefficient and non-apex job data from the release JSON.
No positivity is asserted; Lean checks the job-to-cell membership bridges.
"""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[1]
source=ROOT.parent/'data/cover.json';data=json.loads(source.read_text())
names=['F1','F2','F3','F4','F5','F6','S1','S2','S3','R1','B1','B2']
def rat(x):return f'({0 if x is None else x} : ℚ)'
def vec(xs):return '!['+','.join(xs)+']'
jobs=[(i,v)for i,n in enumerate(names)for v in data['cells'][n]['vertices']]
txt='''import SparseLowerTail.Section05.CoverSupportData
import SparseLowerTail.Section05.CoverS1Expr

/-! Exact coefficient arrays and the thirty-six non-apex jobs from data/cover.json.
Fan coefficient slots0,2,3,4 are zero placeholders where JSON is null.
These arrays encode only the fixed coefficients, not the exact tangency solution.
Cell order: F1,...,F6,S1,S2,S3,R1,B1,B2. Numeric positivity is separate.
Source SHA-256: '''+hashlib.sha256(source.read_bytes()).hexdigest()+''' -/
namespace SparseLowerTail.Section05.CoverGeometry
open Numerics
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable

def fixedCellThetaQ : Fin 12 → Fin 12 → ℚ :=
  '''+vec([vec(list(map(rat,data['cells'][n]['theta'])))for n in names])+'''
noncomputable def fixedCellTheta (i j : Fin 12) : ℝ := fixedCellThetaQ i j

def cellLambdaQ : Fin 12 → ℚ :=
  '''+vec([rat(data['cells'][n]['lam'])for n in names])+'''
theorem cellLambdaQ_cast (i : Fin 12) : (cellLambdaQ i : ℝ)=cellLambda i := by
  fin_cases i <;> norm_num [cellLambdaQ,cellLambda]

theorem fixedCellTheta_s1 : fixedCellTheta 6=coverS1Theta := by
  have h : fixedCellThetaQ 6=s1Theta := rfl
  funext i
  change (fixedCellThetaQ 6 i:ℝ)=coverS1Theta i
  rw [h]
  fin_cases i <;> norm_num [s1Theta,coverS1Theta]
theorem cellLambda_s1 : cellLambda 6=coverS1Lam := by rfl

def nonapexCell : Fin 36 → Fin 12 :=
  '''+vec([str(i)for i,v in jobs])+'''
def nonapexVertexQ : Fin 36 → ℚ×ℚ :=
  '''+vec(['('+rat(v[0])+','+rat(v[1])+')'for i,v in jobs])+'''
noncomputable def nonapexVertex (j : Fin 36) : ℝ×ℝ :=
  ((nonapexVertexQ j).1,(nonapexVertexQ j).2)

theorem nonapexCell_s1 : nonapexCell 12=6 := rfl
theorem nonapexVertex_s1 : nonapexVertex 12=coverS1Vertex0 := by
  change (((7872292148643627/36028797018963968:ℚ):ℝ),((8304637712871195/18014398509481984:ℚ):ℝ))=coverS1Vertex0
  norm_num [coverS1Vertex0]

'''
for j,(i,v) in enumerate(jobs):
 txt+=f'\ntheorem nonapexVertex{j}_eq : nonapexVertex {j}=(({v[0]}:ℝ),({v[1]}:ℝ)) := by\n'
 txt+=f'  change ((({v[0]}:ℚ):ℝ),(({v[1]}:ℚ):ℝ))=(({v[0]}:ℝ),({v[1]}:ℝ))\n  norm_num\n'

start=0
for i,n in enumerate(names):
 verts=data['cells'][n]['vertices']
 reals=[f'(({v[0]}:ℝ),({v[1]}:ℝ))'for v in verts]
 items=(['criticalPoint']if i<6 else [])+reals
 txt+=f"\ntheorem cellVertices{i}_eq : cellVertices {i}="+'{'+','.join(items)+'} := rfl\n'
 start+=len(verts)
txt+='\n/-- Every cell vertex is the apex or one of the thirty-six exact non-apex jobs. -/\ntheorem cellVertex_eq_apex_or_job (i : Fin 12) (v : ℝ×ℝ)\n    (hv : v∈cellVertices i) :\n    v=criticalPoint ∨ ∃ j : Fin 36,nonapexCell j=i ∧ nonapexVertex j=v := by\n  fin_cases i\n'
start=0
for i,n in enumerate(names):
 nv=len(data['cells'][n]['vertices']);isfan=i<6
 txt+=f'  · change v∈cellVertices {i} at hv\n    rw [cellVertices{i}_eq] at hv\n    simp only [Finset.mem_insert,Finset.mem_singleton] at hv\n'
 txt+='    rcases hv with '+' | '.join(['rfl']*(nv+int(isfan)))+'\n'
 if isfan:txt+='    · exact Or.inl rfl\n'
 for j in range(start,start+nv):
  txt+=f'    · exact Or.inr ⟨{j},rfl,nonapexVertex{j}_eq⟩\n'
 start+=nv
txt+='\nend SparseLowerTail.Section05.CoverGeometry\n'
(ROOT/'SparseLowerTail/Section05/CoverCoefficientData.lean').write_text(txt)
print(f'Generated12 fixed coefficient arrays and{len(jobs)} non-apex jobs')

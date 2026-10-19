#!/usr/bin/env python3
"""Emit an eight-leaf exact subdivision, with all leaves already proved in Lean."""
from pathlib import Path
lines=[f'import SparseLowerTail.Section05.CoverS1Near{i}' for i in range(8)]
lines+=['import SparseLowerTail.Section05.CoverS1Tail','''
/-! Actual checked regions of the S1 vertex-zero certificate.
The near-one cube uses an eight-leaf exact subdivision tree; the far-tail cube
uses one uniform interval proof. Neither statement claims the full S1 domain. -/
noncomputable section
namespace SparseLowerTail.Section05
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def coverS1NearRoot : LogBox := ⟨fun _ => 0,fun _ => 1/32⟩

def coverS1NearProperty (q : EdgeTriple) : Prop :=
  (1/2:ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q
''']
def emit(s):lines.append(s)
def path(bits):
 b='coverS1NearRoot'
 for axis,side in enumerate(bits):b=f'({b}.{"right" if side else "left"} {axis} (1/64))'
 return b
for i in range(8):
 bits=[(i>>j)&1 for j in [2,1,0]];B=path(bits)
 emit(f'''theorem coverS1Near_leaf{i}_eq : {B} = coverS1Near{i}Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near{i}Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf{i} : CheckedLogBoxTree Set.univ coverS1NearProperty {B} :=
  .leaf _ (fun _ hq _ => coverS1Near{i}_positive (by rwa [coverS1Near_leaf{i}_eq] at hq))
''')
def tree(bits):
 if len(bits)==3:return f'coverS1Near_leaf{bits[0]*4+bits[1]*2+bits[2]}'
 B=path(bits);axis=len(bits)
 return f'''(.split {B} {axis} (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    {tree(bits+[0])}
    {tree(bits+[1])})'''
emit(f'''/-- A concrete complete subdivision tree with eight proved leaves. -/
def coverS1NearTree : CheckedLogBoxTree Set.univ coverS1NearProperty coverS1NearRoot :=
  {tree([])}

theorem coverS1NearTree_leafCount : coverS1NearTree.leafCount=8 := by
  rfl

theorem coverS1NearRoot_region : coverS1NearRoot.region=logCube (1/32) := by
  ext q
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [coverS1NearRoot,edgeCoordinate,Matrix.cons_val] at h0 h1 h2
    norm_num at h0 h1 h2
    exact ⟨h0,h1,h2⟩
  · rintro ⟨h0,h1,h2⟩ i
    simp only [Set.mem_Icc,one_div] at h0 h1 h2
    fin_cases i <;> simp [coverS1NearRoot,edgeCoordinate,Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> assumption

/-- A cube with 32 times the side length of the first checked box, covered
without gaps by the actual finite subdivision tree. -/
theorem coverS1_near_cube_positive {{q : EdgeTriple}} (hq : q ∈ logCube (1/32)) :
    (1/2:ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  apply coverS1NearTree.sound q
  · rwa [coverS1NearRoot_region]
  · trivial

/-- A large tail portion of the sorted S1 domain is covered by one leaf. -/
theorem coverS1_sorted_tail_positive {{q : EdgeTriple}}
    (hq : q ∈ orderedLogDomain coverS1Q) (h8 : 8 ≤ q.2) :
    (1/100:ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  apply coverS1Tail_positive
  intro i
  fin_cases i <;>
    simp [coverS1TailBox,edgeCoordinate,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
    change _ ∧ _ <;> constructor <;>
    linarith [hq.1,hq.2.1,hq.2.2.1,hq.2.2.2,show coverS1Q=(6743/512:ℝ) from rfl]

/-- The larger near-one positivity region in the original edge coordinates. -/
theorem coverS1_near_edges_positive :
    ∀ u ∈ edgeCube (Real.exp (-(1/32:ℝ))),
      (1/2:ℝ) ≤ coverCertificate coverS1Theta coverS1Lam u coverS1Vertex0 := by
  apply coverCertificate_bound_of_orderedLog
  intro q hq
  exact le_of_lt (coverS1_near_cube_positive (orderedLogDomain_subset_cube _ hq))

end SparseLowerTail.Section05''')
(Path(__file__).resolve().parents[1]/'SparseLowerTail/Section05/CoverS1Regions.lean').write_text('\n'.join(lines)+'\n')

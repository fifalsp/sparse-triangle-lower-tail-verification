import SparseLowerTail.Section05.CoverS1Near0
import SparseLowerTail.Section05.CoverS1Near1
import SparseLowerTail.Section05.CoverS1Near2
import SparseLowerTail.Section05.CoverS1Near3
import SparseLowerTail.Section05.CoverS1Near4
import SparseLowerTail.Section05.CoverS1Near5
import SparseLowerTail.Section05.CoverS1Near6
import SparseLowerTail.Section05.CoverS1Near7
import SparseLowerTail.Section05.CoverS1Tail

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

theorem coverS1Near_leaf0_eq : (((coverS1NearRoot.left 0 (1/64)).left 1 (1/64)).left 2 (1/64)) = coverS1Near0Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near0Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf0 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.left 0 (1/64)).left 1 (1/64)).left 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near0_positive (by rwa [coverS1Near_leaf0_eq] at hq))

theorem coverS1Near_leaf1_eq : (((coverS1NearRoot.left 0 (1/64)).left 1 (1/64)).right 2 (1/64)) = coverS1Near1Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near1Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf1 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.left 0 (1/64)).left 1 (1/64)).right 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near1_positive (by rwa [coverS1Near_leaf1_eq] at hq))

theorem coverS1Near_leaf2_eq : (((coverS1NearRoot.left 0 (1/64)).right 1 (1/64)).left 2 (1/64)) = coverS1Near2Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near2Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf2 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.left 0 (1/64)).right 1 (1/64)).left 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near2_positive (by rwa [coverS1Near_leaf2_eq] at hq))

theorem coverS1Near_leaf3_eq : (((coverS1NearRoot.left 0 (1/64)).right 1 (1/64)).right 2 (1/64)) = coverS1Near3Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near3Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf3 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.left 0 (1/64)).right 1 (1/64)).right 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near3_positive (by rwa [coverS1Near_leaf3_eq] at hq))

theorem coverS1Near_leaf4_eq : (((coverS1NearRoot.right 0 (1/64)).left 1 (1/64)).left 2 (1/64)) = coverS1Near4Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near4Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf4 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.right 0 (1/64)).left 1 (1/64)).left 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near4_positive (by rwa [coverS1Near_leaf4_eq] at hq))

theorem coverS1Near_leaf5_eq : (((coverS1NearRoot.right 0 (1/64)).left 1 (1/64)).right 2 (1/64)) = coverS1Near5Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near5Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf5 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.right 0 (1/64)).left 1 (1/64)).right 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near5_positive (by rwa [coverS1Near_leaf5_eq] at hq))

theorem coverS1Near_leaf6_eq : (((coverS1NearRoot.right 0 (1/64)).right 1 (1/64)).left 2 (1/64)) = coverS1Near6Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near6Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf6 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.right 0 (1/64)).right 1 (1/64)).left 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near6_positive (by rwa [coverS1Near_leaf6_eq] at hq))

theorem coverS1Near_leaf7_eq : (((coverS1NearRoot.right 0 (1/64)).right 1 (1/64)).right 2 (1/64)) = coverS1Near7Box := by
  ext j <;> fin_cases j <;>
    simp [coverS1NearRoot,coverS1Near7Box,LogBox.left,LogBox.right,Function.update,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> norm_num

def coverS1Near_leaf7 : CheckedLogBoxTree Set.univ coverS1NearProperty (((coverS1NearRoot.right 0 (1/64)).right 1 (1/64)).right 2 (1/64)) :=
  .leaf _ (fun _ hq _ => coverS1Near7_positive (by rwa [coverS1Near_leaf7_eq] at hq))

/-- A concrete complete subdivision tree with eight proved leaves. -/
def coverS1NearTree : CheckedLogBoxTree Set.univ coverS1NearProperty coverS1NearRoot :=
  (.split coverS1NearRoot 0 (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    (.split (coverS1NearRoot.left 0 (1/64)) 1 (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    (.split ((coverS1NearRoot.left 0 (1/64)).left 1 (1/64)) 2 (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    coverS1Near_leaf0
    coverS1Near_leaf1)
    (.split ((coverS1NearRoot.left 0 (1/64)).right 1 (1/64)) 2 (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    coverS1Near_leaf2
    coverS1Near_leaf3))
    (.split (coverS1NearRoot.right 0 (1/64)) 1 (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    (.split ((coverS1NearRoot.right 0 (1/64)).left 1 (1/64)) 2 (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    coverS1Near_leaf4
    coverS1Near_leaf5)
    (.split ((coverS1NearRoot.right 0 (1/64)).right 1 (1/64)) 2 (1/64)
    (by norm_num [LogBox.CutInside,coverS1NearRoot,LogBox.left,LogBox.right,Function.update,Fin.ext_iff])
    coverS1Near_leaf6
    coverS1Near_leaf7)))

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
theorem coverS1_near_cube_positive {q : EdgeTriple} (hq : q ∈ logCube (1/32)) :
    (1/2:ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  apply coverS1NearTree.sound q
  · rwa [coverS1NearRoot_region]
  · trivial

/-- A large tail portion of the sorted S1 domain is covered by one leaf. -/
theorem coverS1_sorted_tail_positive {q : EdgeTriple}
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

end SparseLowerTail.Section05

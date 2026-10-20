import SparseLowerTail.Section05.CoverTreeReplay

/-! Soundness of successful sorted branch-and-bound outside the acceptance neighborhoods. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05

/-- A completed, validated subdivision proves the lower bound away from the acceptance set.
Each leaf is accepted by containment in that set or by a proved numerical lower bound. -/
theorem branch_bound_ordered {F : EdgeTriple → ℝ} {Q ε : ℝ} {A : Set EdgeTriple}
    {table : ℕ → Option LogBox} {B : LogBox} (T : CoverReplayTree) (hT : T.Valid table B)
    (hroot : orderedLogDomain Q⊆B.region)
    (hleaf : ∀ i C, table i=some C → C.region⊆A ∨
      ∀ q∈C.region, q∈orderedLogDomain Q → ε≤F q) :
    ∀ q∈orderedLogDomain Q, q∉A → ε≤F q := by
  have hh := CoverReplayTree.sound (Q:=Q) (P:=fun q => q∉A → ε≤F q) (table:=table)
    (fun i C hi q hq hD hnot => by
      rcases hleaf i C hi with hA|hbound
      · exact False.elim (hnot (hA hq))
      · exact hbound q hq hD) T hT
  exact fun q hq => hh q (hroot hq) hq

/-- `lem:comp-bnb`: permutation invariance transfers the checked sorted-domain bound.
A sorting word explicitly represents q↓; it may be chosen independently for every q. -/
theorem branch_bound_full_cube {F : EdgeTriple → ℝ} {Q ε : ℝ} {A : Set EdgeTriple}
    {table : ℕ → Option LogBox} {B : LogBox} (T : CoverReplayTree) (hT : T.Valid table B)
    (hroot : orderedLogDomain Q⊆B.region)
    (hleaf : ∀ i C, table i=some C → C.region⊆A ∨
      ∀ q∈C.region, q∈orderedLogDomain Q → ε≤F q)
    (hperm : ∀ w q, F (edgePermutationWord w q)=F q)
    (q : EdgeTriple) (_hq : q∈logCube Q)
    (hsorted : ∃ w : List Bool, edgePermutationWord w q∈orderedLogDomain Q ∧ edgePermutationWord w q∉A) :
    ε≤F q := by
  obtain ⟨w,hD,houtside⟩ := hsorted
  have hh := branch_bound_ordered T hT hroot hleaf _ hD houtside
  rwa [hperm] at hh

/-- Every cube point has a sorting word, including all equal-coordinate boundary cases. -/
theorem branch_bound_sorted_or_accepted {F : EdgeTriple → ℝ} {Q ε : ℝ} {A : Set EdgeTriple}
    {table : ℕ → Option LogBox} {B : LogBox} (T : CoverReplayTree) (hT : T.Valid table B)
    (hroot : orderedLogDomain Q⊆B.region)
    (hleaf : ∀ i C, table i=some C → C.region⊆A ∨
      ∀ q∈C.region, q∈orderedLogDomain Q → ε≤F q)
    (hperm : ∀ w q, F (edgePermutationWord w q)=F q)
    (q : EdgeTriple) (hq : q∈logCube Q) :
    ∃ w : List Bool, edgePermutationWord w q∈orderedLogDomain Q ∧
      (edgePermutationWord w q∈A ∨ ε≤F q) := by
  classical
  obtain ⟨w,hD⟩ := exists_orderedLog_permutation hq
  refine ⟨w,hD,?_⟩
  by_cases hA : edgePermutationWord w q∈A
  · exact Or.inl hA
  · exact Or.inr (branch_bound_full_cube T hT hroot hleaf hperm q hq ⟨w,hD,hA⟩)

end SparseLowerTail.Section05

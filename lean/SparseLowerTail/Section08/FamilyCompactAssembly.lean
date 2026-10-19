import SparseLowerTail.Section08.FiniteCertificateAssembly
import SparseLowerTail.Section08.FamilyAAACover
import SparseLowerTail.Section05.SortedLogBoxes

/-! Exact conclusion needed from compact-family leaves, including the zero
patterns. Sorting preserves both parts of the certificate. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Section02 Section04 Section05 Numerics Set

/-- Common conclusion of strict-positive and local-contact leaves. -/
def FamilyLeafConclusion (z : ℝ) (q : FamilyVector) : Prop :=
  0≤familyPhi z q ∧ (familyPhi z q=0 →
    AllowedPattern (branchA z) (branchB z)
      (Real.exp (-q 0)) (Real.exp (-q 1)) (Real.exp (-q 2)))

theorem familyLeafConclusion_of_positive {z : ℝ} {q : FamilyVector}
    (h : 0<familyPhi z q) : FamilyLeafConclusion z q :=
  ⟨h.le,fun hz => False.elim (ne_of_gt h hz)⟩

/-- The ABB local input is still an internal finite verification obligation.
It will be supplied by the full ABB replay, not assumed as an external result. -/
def FamilyABBLocal : Prop :=
  ∀z : ℝ,0<z → Bounds (branchLog z) (39/10) (19/2) →
    ∀q : FamilyVector,q∈familyCube (familyContactABB z) (1/10) →
      0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z)

def familyContact (mixed : Bool) (z : ℝ) : FamilyVector :=
  if mixed then familyContactABB z else familyContactAAA z

theorem allowedPattern_of_familyContact {z : ℝ} (hz : 0<z) (mixed : Bool) :
    AllowedPattern (branchA z) (branchB z)
      (Real.exp (-familyContact mixed z 0)) (Real.exp (-familyContact mixed z 1))
      (Real.exp (-familyContact mixed z 2)) := by
  cases mixed
  · change AllowedPattern (branchA z) (branchB z)
      (Real.exp (-qA z)) (Real.exp (-qA z)) (Real.exp (-qA z))
    simp only [qA,neg_neg,Real.exp_log (branchA_pos hz)]
    exact Or.inl ⟨rfl,rfl,rfl⟩
  · change AllowedPattern (branchA z) (branchB z)
      (Real.exp (-qA z)) (Real.exp (-(-Real.log (branchB z))))
      (Real.exp (-(-Real.log (branchB z))))
    simp only [qA,neg_neg,Real.exp_log (branchA_pos hz),Real.exp_log (branchB_pos z)]
    exact Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)

theorem familyLeafConclusion_of_contact (hABB : FamilyABBLocal)
    {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10) (19/2))
    (mixed : Bool) {q : FamilyVector} (hq : q∈familyCube (familyContact mixed z) (1/10)) :
    FamilyLeafConclusion z q := by
  have hh : 0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContact mixed z) := by
    cases mixed
    · exact FamilyAAACover.local_nonnegative_and_unique_zero hz hL hq
    · exact hABB z hz hL q hq
  refine ⟨hh.1,?_⟩
  intro he
  rw [hh.2.mp he]
  exact allowedPattern_of_familyContact hz mixed

def familyTriplePhi (z : ℝ) (q : EdgeTriple) : ℝ := phi z q.1.1 q.1.2 q.2

theorem familyTriplePhi_permutation (z : ℝ) (w : List Bool) (q : EdgeTriple) :
    familyTriplePhi z (edgePermutationWord w q)=familyTriplePhi z q := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    cases b
    · change familyTriplePhi z (edgePermutationWord w (edgeSwap12 q))=familyTriplePhi z q
      rw [ih]
      exact phi_swap_uv z q.1.2 q.1.1 q.2
    · change familyTriplePhi z (edgePermutationWord w (edgeSwap23 q))=familyTriplePhi z q
      rw [ih]
      exact (phi_swap_uv z q.1.1 q.2 q.1.2).trans
        ((phi_swap_uw z q.2 q.1.1 q.1.2).trans (phi_swap_uv z q.1.2 q.1.1 q.2))

theorem allowedPattern_permutation (a b : ℝ) (w : List Bool) (q : EdgeTriple) :
    AllowedPattern a b (edgePermutationWord w q).1.1
      (edgePermutationWord w q).1.2 (edgePermutationWord w q).2 ↔
    AllowedPattern a b q.1.1 q.1.2 q.2 := by
  induction w generalizing q with
  | nil => rfl
  | cons c w ih =>
    cases c
    · change AllowedPattern a b (edgePermutationWord w (edgeSwap12 q)).1.1
        (edgePermutationWord w (edgeSwap12 q)).1.2 (edgePermutationWord w (edgeSwap12 q)).2 ↔ _
      rw [ih]
      simp only [AllowedPattern,edgeSwap12_apply]
      tauto
    · change AllowedPattern a b (edgePermutationWord w (edgeSwap23 q)).1.1
        (edgePermutationWord w (edgeSwap23 q)).1.2 (edgePermutationWord w (edgeSwap23 q)).2 ↔ _
      rw [ih]
      simp only [AllowedPattern,edgeSwap23_apply]
      tauto

/-- A full ordered compact replay gives precisely the internal family input
of the main theorem, including all equality cases and repeated coordinates. -/
theorem compactFamilyCertificate_of_ordered
    (h : ∀z : ℝ,0<z → Bounds (branchLog z) (39/10) (19/2) →
      ∀q : FamilyVector,(∀i,Bounds (q i) 0 12) → q 2≤q 1 → q 1≤q 0 →
        FamilyLeafConclusion z q) : Section08.CompactFamilyCertificate := by
  intro z hz hL u hu v hv t ht
  let q : EdgeTriple := ((u,v),t)
  obtain ⟨w,hw⟩ := exists_orderedLog_permutation (q := q) (Q := 12) ⟨hu,hv,ht⟩
  let p := edgePermutationWord w q
  have hc := orderedLogDomain_subset_cube 12 hw
  have hp : ∀i : Fin 3,Bounds (![p.1.1,p.1.2,p.2] i) 0 12 := by
    intro i
    fin_cases i
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2
  have hh := h z hz hL ![p.1.1,p.1.2,p.2] hp hw.2.1 hw.2.2.1
  have he : familyPhi z ![p.1.1,p.1.2,p.2]=phi z u v t :=
    familyTriplePhi_permutation z w q
  refine ⟨by simpa only [he] using hh.1,?_⟩
  intro hzero
  have hpat := hh.2 (he.trans hzero)
  have hpat' : AllowedPattern (branchA z) (branchB z)
      (logBoxEdges p).1.1 (logBoxEdges p).1.2 (logBoxEdges p).2 := hpat
  dsimp only [p] at hpat'
  rw [logBoxEdges_permutation] at hpat'
  exact (allowedPattern_permutation _ _ w (logBoxEdges q)).mp hpat'

end SparseLowerTail.Certificate

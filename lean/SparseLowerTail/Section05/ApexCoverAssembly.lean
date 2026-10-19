import SparseLowerTail.Section05.ApexContactBox
import SparseLowerTail.Section05.CriticalAssembly

/-! Preserve apex zero patterns through sorted subdivision and permutation.
The full sorted-domain hypothesis remains a numerical certificate obligation.
-/
noncomputable section
namespace SparseLowerTail.Section05
open CoverGeometry Section02

/-- The common conclusion of strict-positive leaves and local contact leaves. -/
def ApexLeafConclusion (i : Fin 6) (q : EdgeTriple) : Prop :=
  0 ≤ logCertificate (apexFanTheta i) (cellLambda (i.castAdd 6)) criticalPoint q ∧
  (logCertificate (apexFanTheta i) (cellLambda (i.castAdd 6)) criticalPoint q = 0 →
    ∃ mixed, edgeCoordinate q = apexFanContact mixed)

theorem apexLeafConclusion_of_positive {i : Fin 6} {q : EdgeTriple}
    (h : 0 < logCertificate (apexFanTheta i) (cellLambda (i.castAdd 6)) criticalPoint q) :
    ApexLeafConclusion i q :=
  ⟨h.le, fun hz => False.elim (ne_of_gt h hz)⟩

theorem LogBox.apexLeafConclusion_of_contact {B : LogBox} {i : Fin 6} {mixed : Bool}
    (hB : B.InApexContact i mixed) {q : EdgeTriple} (hq : q ∈ B.region) :
    ApexLeafConclusion i q := by
  have h := B.apex_contact_nonneg_zero_iff hB hq
  exact ⟨h.1, fun hz => ⟨mixed, h.2.mp hz⟩⟩

theorem criticalPatterns_permutationWord (w : List Bool) (u : EdgeTriple) :
    edgePermutationWord w u ∈ criticalPatterns ↔ u ∈ criticalPatterns := by
  induction w generalizing u with
  | nil => rfl
  | cons b w ih =>
    cases b
    · change edgePermutationWord w (edgeSwap12 u) ∈ criticalPatterns ↔ _
      rw [ih]
      simp only [criticalPatterns, Set.mem_setOf_eq, AllowedPattern, edgeSwap12_apply]
      tauto
    · change edgePermutationWord w (edgeSwap23 u) ∈ criticalPatterns ↔ _
      rw [ih]
      simp only [criticalPatterns, Set.mem_setOf_eq, AllowedPattern, edgeSwap23_apply]
      tauto

theorem criticalPatterns_of_apexContact {q : EdgeTriple} {mixed : Bool}
    (h : edgeCoordinate q = apexFanContact mixed) : logBoxEdges q ∈ criticalPatterns := by
  have he := congrArg (fun p : ApexVector => logBoxEdges ((p 0,p 1),p 2)) h
  cases mixed
  · change logBoxEdges q = logBoxEdges ((apexContactAAA 0,apexContactAAA 1),apexContactAAA 2) at he
    rw [apexContactAAA_edges] at he
    rw [he]
    exact Or.inl ⟨rfl,rfl,rfl⟩
  · change logBoxEdges q = logBoxEdges ((apexContactABB 0,apexContactABB 1),apexContactABB 2) at he
    rw [apexContactABB_edges] at he
    rw [he]
    exact Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)

/-- Sorting loses neither the nonnegativity statement nor its equality cases. -/
theorem apex_nonneg_patterns_of_ordered (i : Fin 6) (Q : ℝ)
    (h : ∀ q ∈ orderedLogDomain Q, ApexLeafConclusion i q) :
    ∀ u ∈ edgeCube (Real.exp (-Q)),
      0 ≤ coverCertificate (apexFanTheta i) (cellLambda (i.castAdd 6)) u criticalPoint ∧
      (coverCertificate (apexFanTheta i) (cellLambda (i.castAdd 6)) u criticalPoint = 0 →
        u ∈ criticalPatterns) := by
  intro u hu
  refine ⟨coverCertificate_bound_of_orderedLog _ _ _ Q 0 (fun q hq => (h q hq).1) u hu, ?_⟩
  intro hz
  let q : EdgeTriple := ((-Real.log u.1.1,-Real.log u.1.2),-Real.log u.2)
  have hu0 : 0 < u.1.1 ∧ 0 < u.1.2 ∧ 0 < u.2 :=
    ⟨(Real.exp_pos _).trans_le hu.1.1,(Real.exp_pos _).trans_le hu.2.1.1,
      (Real.exp_pos _).trans_le hu.2.2.1⟩
  have he : logBoxEdges q = u := by
    simp only [q,logBoxEdges,neg_neg,Real.exp_log hu0.1,Real.exp_log hu0.2.1,
      Real.exp_log hu0.2.2]
  have hq : q ∈ logCube Q := (logBoxEdges_mem_cube_iff q Q).mp (he ▸ hu)
  obtain ⟨w,hw⟩ := exists_orderedLog_permutation hq
  have hz' : logCertificate (apexFanTheta i) (cellLambda (i.castAdd 6)) criticalPoint
      (edgePermutationWord w q) = 0 := by
    rw [logCertificate_permutation,logCertificate,he]
    exact hz
  obtain ⟨mixed,hm⟩ := (h _ hw).2 hz'
  have hp := criticalPatterns_of_apexContact hm
  rw [logBoxEdges_permutation,he] at hp
  exact (criticalPatterns_permutationWord w u).mp hp

end SparseLowerTail.Section05

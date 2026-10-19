import SparseLowerTail.Section05.CoverSymmetry

/-! Exact logarithmic-domain reduction for the ordered interval verifier.
This module proves the domain/permutation step; it does not certify any finite
partition or any numerical box positivity. -/
noncomputable section
namespace SparseLowerTail.Section05

/-- Exponentiation from logarithmic coordinates to the positive edge cube. -/
def logBoxEdges (q : EdgeTriple) : EdgeTriple :=
  ((Real.exp (-q.1.1),Real.exp (-q.1.2)),Real.exp (-q.2))

def logCube (Q : ℝ) : Set EdgeTriple :=
  {q | q.1.1 ∈ Set.Icc 0 Q ∧ q.1.2 ∈ Set.Icc 0 Q ∧ q.2 ∈ Set.Icc 0 Q}

/-- The manuscript's ordered domain D_Q. -/
def orderedLogDomain (Q : ℝ) : Set EdgeTriple :=
  {q | 0 ≤ q.2 ∧ q.2 ≤ q.1.2 ∧ q.1.2 ≤ q.1.1 ∧ q.1.1 ≤ Q}

def logCertificate (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ × ℝ) (q : EdgeTriple) : ℝ :=
  coverCertificate θ lam (logBoxEdges q) π

theorem exp_neg_mem_Icc_iff (x Q : ℝ) :
    Real.exp (-x) ∈ Set.Icc (Real.exp (-Q)) 1 ↔ x ∈ Set.Icc 0 Q := by
  rw [Set.mem_Icc,Set.mem_Icc,show (1:ℝ)=Real.exp 0 by simp,
    Real.exp_le_exp,Real.exp_le_exp]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem logBoxEdges_mem_cube_iff (q : EdgeTriple) (Q : ℝ) :
    logBoxEdges q ∈ edgeCube (Real.exp (-Q)) ↔ q ∈ logCube Q := by
  simp only [logBoxEdges,edgeCube,logCube,Set.mem_setOf_eq,exp_neg_mem_Icc_iff]

theorem orderedLogDomain_subset_cube (Q : ℝ) : orderedLogDomain Q ⊆ logCube Q := by
  rintro q ⟨h0,h1,h2,h3⟩
  exact ⟨⟨h0.trans (h1.trans h2),h3⟩,⟨h0.trans h1,h2.trans h3⟩,
    ⟨h0,h1.trans (h2.trans h3)⟩⟩

/-- Every point of the cube is a permutation of a point in D_Q. -/
theorem exists_orderedLog_permutation {q : EdgeTriple} {Q : ℝ} (hq : q ∈ logCube Q) :
    ∃ w : List Bool, edgePermutationWord w q ∈ orderedLogDomain Q := by
  rcases hq with ⟨hx,hy,hz⟩
  rcases le_total q.1.2 q.1.1 with hxy | hyx
  · rcases le_total q.2 q.1.2 with hyz | hzy
    · exact ⟨[],hz.1,hyz,hxy,hx.2⟩
    · rcases le_total q.2 q.1.1 with hxz | hzx
      · exact ⟨[true],hy.1,hzy,hxz,hx.2⟩
      · exact ⟨[true,false],hy.1,hxy,hzx,hz.2⟩
  · rcases le_total q.2 q.1.1 with hxz | hzx
    · exact ⟨[false],hz.1,hxz,hyx,hy.2⟩
    · rcases le_total q.2 q.1.2 with hyz | hzy
      · exact ⟨[false,true],hx.1,hzx,hyz,hy.2⟩
      · exact ⟨[false,true,false],hx.1,hyx,hzy,hz.2⟩

theorem logBoxEdges_permutation (w : List Bool) (q : EdgeTriple) :
    logBoxEdges (edgePermutationWord w q) = edgePermutationWord w (logBoxEdges q) := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => exact (ih (edgeSwap12 q))
    | true => exact (ih (edgeSwap23 q))

theorem logCertificate_permutation (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ × ℝ)
    (w : List Bool) (q : EdgeTriple) :
    logCertificate θ lam π (edgePermutationWord w q)=logCertificate θ lam π q := by
  simp only [logCertificate,logBoxEdges_permutation,coverCertificate_permutationWord]

/-- A bound on sorted logarithmic coordinates proves the same bound on the full
positive cube, including all repeated-coordinate boundary points. -/
theorem coverCertificate_bound_of_orderedLog (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ × ℝ)
    (Q L : ℝ) (h : ∀ q ∈ orderedLogDomain Q,L ≤ logCertificate θ lam π q) :
    ∀ u ∈ edgeCube (Real.exp (-Q)), L ≤ coverCertificate θ lam u π := by
  intro u hu
  let q : EdgeTriple := ((-Real.log u.1.1,-Real.log u.1.2),-Real.log u.2)
  have hu0 : 0 < u.1.1 ∧ 0 < u.1.2 ∧ 0 < u.2 :=
    ⟨(Real.exp_pos _).trans_le hu.1.1,(Real.exp_pos _).trans_le hu.2.1.1,
      (Real.exp_pos _).trans_le hu.2.2.1⟩
  have he : logBoxEdges q=u := by
    simp only [q,logBoxEdges,neg_neg,Real.exp_log hu0.1,Real.exp_log hu0.2.1,
      Real.exp_log hu0.2.2]
  have hq : q ∈ logCube Q := (logBoxEdges_mem_cube_iff q Q).mp (he ▸ hu)
  obtain ⟨w,hw⟩ := exists_orderedLog_permutation hq
  have hb := h _ hw
  rw [logCertificate_permutation,logCertificate,he] at hb
  exact hb

theorem coverCertificate_pos_of_orderedLog (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ × ℝ)
    (Q : ℝ) (h : ∀ q ∈ orderedLogDomain Q,0 < logCertificate θ lam π q) :
    ∀ u ∈ edgeCube (Real.exp (-Q)), 0 < coverCertificate θ lam u π := by
  intro u hu
  let q : EdgeTriple := ((-Real.log u.1.1,-Real.log u.1.2),-Real.log u.2)
  have hu0 : 0 < u.1.1 ∧ 0 < u.1.2 ∧ 0 < u.2 :=
    ⟨(Real.exp_pos _).trans_le hu.1.1,(Real.exp_pos _).trans_le hu.2.1.1,
      (Real.exp_pos _).trans_le hu.2.2.1⟩
  have he : logBoxEdges q=u := by
    simp only [q,logBoxEdges,neg_neg,Real.exp_log hu0.1,Real.exp_log hu0.2.1,
      Real.exp_log hu0.2.2]
  have hq : q ∈ logCube Q := (logBoxEdges_mem_cube_iff q Q).mp (he ▸ hu)
  obtain ⟨w,hw⟩ := exists_orderedLog_permutation hq
  have hb := h _ hw
  rw [logCertificate_permutation,logCertificate,he] at hb
  exact hb

end SparseLowerTail.Section05

import SparseLowerTail.Section03.DiscreteEntropyUpper

/-! Attainment of the actual finite variational minimum in s3:Phi. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

private theorem mul_log_div_identity (a b : ℝ) (hb : b≠0) :
    a*Real.log (a/b)=a*Real.log a-a*Real.log b := by
  by_cases ha : a=0
  · simp [ha]
  rw [Real.log_div ha hb]
  ring

/-- Continuity includes the two zero-log-zero endpoints. -/
theorem continuous_bernoulliEntropy {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) :
    Continuous (bernoulliEntropy p) := by
  have he : bernoulliEntropy p=fun q =>
      (q*Real.log q+(1-q)*Real.log (1-q))-q*Real.log p-(1-q)*Real.log (1-p) := by
    funext q
    unfold bernoulliEntropy
    rw [mul_log_div_identity q p hp.1.ne',
      mul_log_div_identity (1-q) (1-p) (sub_pos.mpr hp.2).ne']
    ring
  rw [he]
  exact ((Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
    (continuous_id.mul continuous_const)).sub ((continuous_const.sub continuous_id).mul continuous_const)

theorem continuous_finiteEdgeEntropy (n : ℕ) {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) :
    Continuous (finiteEdgeEntropy n p) := by
  unfold finiteEdgeEntropy
  apply continuous_finset_sum
  intro e _
  exact (continuous_bernoulliEntropy hp).comp (continuous_apply e)

theorem continuous_weightedTriangleCount (n : ℕ) :
    Continuous (@weightedTriangleCount n) := by
  unfold weightedTriangleCount
  apply continuous_finset_sum
  intro T _
  apply continuous_finset_prod
  intro e _
  exact continuous_apply e

/-- Non-edge coordinates do not affect either quantity in the finite problem. -/
theorem finiteTriangle_normalize (n : ℕ) (p : ℝ) (q : Finset (Fin n) → ℝ) :
    let q' : Finset (Fin n) → ℝ := fun e => if e∈completeGraphEdges n then q e else 0
    weightedTriangleCount q'=weightedTriangleCount q ∧
      finiteEdgeEntropy n p q'=finiteEdgeEntropy n p q := by
  classical
  dsimp only
  constructor
  · apply Finset.sum_congr rfl
    intro T _
    apply Finset.prod_congr rfl
    intro e he
    simp only [if_pos (triangleEdgeSet_edge he)]
  · apply Finset.sum_congr rfl
    intro e he
    simp only [if_pos he]

/-- The finite variational infimum is a minimum, as asserted before lem:discrete. -/
theorem finiteTrianglePhi_attained (n : ℕ) {p η : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) :
    ∃ q : Finset (Fin n) → ℝ, FiniteTriangleFeasible n p η q ∧
      finiteEdgeEntropy n p q=finiteTrianglePhi n p η := by
  classical
  let K : Set ((Finset (Fin n)) → ℝ) :=
    Icc (fun _ => 0) (fun _ => 1) ∩ {q | weightedTriangleCount q≤η*(n.choose 3:ℝ)*p^3}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le (continuous_weightedTriangleCount n) continuous_const)
  have hzero : (fun _ => (0:ℝ))∈K := by
    exact ⟨⟨le_rfl,by intro _; norm_num⟩,(zero_finiteTriangleFeasible n hp.1.le hη).2⟩
  obtain ⟨q,hq,hmin⟩ := hK.exists_isMinOn ⟨_,hzero⟩ (continuous_finiteEdgeEntropy n hp).continuousOn
  have hfeas : FiniteTriangleFeasible n p η q :=
    ⟨fun e _ => ⟨hq.1.1 e,hq.1.2 e⟩,hq.2⟩
  refine ⟨q,hfeas,le_antisymm ?_ (finiteTrianglePhi_le n hp q hfeas)⟩
  apply le_csInf
    (show {v | ∃ q, FiniteTriangleFeasible n p η q ∧ finiteEdgeEntropy n p q=v}.Nonempty from
      ⟨_,q,hfeas,rfl⟩)
  rintro v ⟨q',hq',rfl⟩
  let q'' : Finset (Fin n) → ℝ := fun e => if e∈completeGraphEdges n then q' e else 0
  have hnorm := finiteTriangle_normalize n p q'
  have hq'' : q''∈K := by
    constructor
    · constructor <;> intro e <;> dsimp [q'']
      · split_ifs with he
        · exact (hq'.1 e he).1
        · exact le_rfl
      · split_ifs with he
        · exact (hq'.1 e he).2
        · exact zero_le_one
    · change weightedTriangleCount q''≤_
      rw [hnorm.1]
      exact hq'.2
  have hh := hmin hq''
  change finiteEdgeEntropy n p q≤finiteEdgeEntropy n p (fun e => if e∈completeGraphEdges n then q' e else 0) at hh
  rw [hnorm.2] at hh
  exact hh

end SparseLowerTail.Section03

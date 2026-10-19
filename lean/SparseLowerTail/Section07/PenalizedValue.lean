import SparseLowerTail.Section07.PenalizedPhase

/-! The attained scalar value C(γ) in `prop:pen`, defined as the infimum of
actual two-variable penalty values. No external reduction is used here. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04

def penalizedValues (γ : ℝ) : Set ℝ :=
  {v | ∃ a b : ℝ, a∈Icc (0:ℝ) 1 ∧ b∈Icc (0:ℝ) 1 ∧ v=balancedPenalty γ a b}

def penalizedValue (γ : ℝ) : ℝ := sInf (penalizedValues γ)

/-- Any actual scalar optimizer realizes the infimum. -/
theorem penalizedValue_eq_of_minimizer {γ a b : ℝ}
    (h : IsBalancedPenalizedMinimizer γ a b) :
    penalizedValue γ=balancedPenalty γ a b := by
  apply IsLeast.csInf_eq
  refine ⟨⟨a,b,h.1,h.2.1,rfl⟩,?_⟩
  rintro v ⟨c,d,hc,hd,rfl⟩
  exact h.2.2 c d hc hd

/-- The infimum is a genuine minimum for every scalar penalty. -/
theorem penalizedValue_attained (γ : ℝ) :
    ∃ a b : ℝ, a∈Icc (0:ℝ) 1 ∧ b∈Icc (0:ℝ) 1 ∧
      penalizedValue γ=balancedPenalty γ a b := by
  obtain ⟨a,b,h⟩ := exists_balancedPenalizedMinimizer γ
  exact ⟨a,b,h.1,h.2.1,penalizedValue_eq_of_minimizer h⟩

theorem penalizedValue_le {γ a b : ℝ} (ha : a∈Icc (0:ℝ) 1)
    (hb : b∈Icc (0:ℝ) 1) : penalizedValue γ≤balancedPenalty γ a b := by
  obtain ⟨c,d,h⟩ := exists_balancedPenalizedMinimizer γ
  rw [penalizedValue_eq_of_minimizer h]
  exact h.2.2 a b ha hb

/-- The literal value conclusion in `prop:pen(a)`. -/
theorem penalizedValue_below_critical {γ : ℝ} (hγ : 0<γ) (hc : γ<criticalPenalty) :
    penalizedValue γ=constantMinimum γ := by
  have h := (penalizedMinimizer_below_critical hγ hc (constantRoot γ) (constantRoot γ)).mpr ⟨rfl,rfl⟩
  rw [penalizedValue_eq_of_minimizer h,balancedPenalty_diagonal]
  rfl

/-- Both equalities in `prop:pen(b)`. -/
theorem penalizedValue_at_critical :
    penalizedValue criticalPenalty=constantMinimum criticalPenalty ∧
    penalizedValue criticalPenalty=balancedPenalty criticalPenalty
      (branchA penalizedCrossing) (branchB penalizedCrossing) := by
  have hconst := (penalizedMinimizer_at_critical largeTarget largeTarget).mpr (Or.inl ⟨rfl,rfl⟩)
  have hbranch := (penalizedMinimizer_at_critical (branchA penalizedCrossing)
    (branchB penalizedCrossing)).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨?_,penalizedValue_eq_of_minimizer hbranch⟩
  rw [penalizedValue_eq_of_minimizer hconst,balancedPenalty_diagonal]
  rfl

/-- The branch minimum value above the transition. -/
theorem penalizedValue_above_critical {γ z : ℝ} (hγ : criticalPenalty<γ)
    (hz : z∈Ioo (0:ℝ) penalizedCrossing) (hμ : branchMu z=3*γ) :
    penalizedValue γ=balancedPenalty γ (branchA z) (branchB z) :=
  penalizedValue_eq_of_minimizer
    ((penalizedMinimizer_above_critical hγ hz hμ _ _).mpr ⟨rfl,rfl⟩)

/-- The unpenalized endpoint is attained by the constant one graphon. -/
theorem penalizedValue_zero : penalizedValue 0=0 := by
  have h : IsBalancedPenalizedMinimizer 0 1 1 := by
    refine ⟨by norm_num,by norm_num,?_⟩
    intro a b ha hb
    simpa [balancedPenalty,balancedCost,entropy] using balancedCost_nonneg ha.1 hb.1
  rw [penalizedValue_eq_of_minimizer h]
  simp [balancedPenalty,balancedCost,entropy]

end SparseLowerTail.Section07

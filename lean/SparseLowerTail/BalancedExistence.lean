import SparseLowerTail.Balanced
import Mathlib.Topology.Order.Compact

/-! Attainment of the finite-dimensional balanced variational problem. -/
noncomputable section
open Set
namespace SparseLowerTail

theorem continuous_balancedTriangle :
    Continuous (fun p : ℝ × ℝ => balancedTriangle p.1 p.2) := by
  unfold balancedTriangle
  fun_prop

theorem continuous_balancedCost :
    Continuous (fun p : ℝ × ℝ => balancedCost p.1 p.2) := by
  exact ((continuous_entropy.comp continuous_fst).add
    (continuous_entropy.comp continuous_snd)).div_const 2

/-- Existence only; uniqueness and the branch/crossing classification are still
separate obligations in Section 4 of the paper. -/
theorem exists_balancedMinimizer {r : ℝ} (hr : r ∈ Icc 0 1) :
    ∃ a b : ℝ, IsBalancedMinimizer r a b := by
  let K : Set (ℝ × ℝ) := {p | BalancedFeasible r p.1 p.2}
  have hK : IsCompact K := by
    have heq : K = ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1)) ∩
        {p : ℝ × ℝ | balancedTriangle p.1 p.2 ≤ r^3} := by
      ext p
      simp only [K, BalancedFeasible, mem_setOf_eq, mem_inter_iff, mem_prod]
      tauto
    rw [heq]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_balancedTriangle continuous_const)
  have hne : K.Nonempty := ⟨(r,r), balanced_diagonal_feasible hr⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne continuous_balancedCost.continuousOn
  refine ⟨p.1, p.2, hp, ?_⟩
  intro c d hcd
  exact hmin (show (c,d) ∈ K from hcd)

/-- The balanced infimum is attained; this is not an existence proof for the
unrestricted graphon problem. -/
theorem balancedValue_attained {r : ℝ} (hr : r ∈ Icc 0 1) :
    ∃ a b : ℝ, BalancedFeasible r a b ∧ balancedCost a b = balancedValue r := by
  obtain ⟨a, b, h⟩ := exists_balancedMinimizer hr
  exact ⟨a, b, isBalancedMinimizer_iff.mp h⟩

end SparseLowerTail

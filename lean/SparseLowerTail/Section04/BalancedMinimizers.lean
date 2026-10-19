import SparseLowerTail.Section04.BalancedPhase
import SparseLowerTail.Section04.BalancedStationary

/-!
# Identifying unrestricted minimizers once balancedness is known

The final comparison step in `cor:bipodalmin`. The difficult assertion that an
unrestricted minimizer has balanced form is not assumed globally: it is an
explicit premise for this bridge.
-/
noncomputable section
open Set
namespace SparseLowerTail

/-- A balanced unrestricted minimizer also minimizes the scalar balanced
problem and witnesses equality of the two variational values. -/
theorem IsBalanced.minimizer_bridge {r a b : ℝ} {U : Graphon}
    (hr : r ∈ Icc (0 : ℝ) 1) (hU : IsMinimizer r U) (hB : IsBalanced U a b) :
    IsBalancedMinimizer r a b ∧ value r = balancedValue r := by
  obtain ⟨ha,hb⟩ := hB.values_mem_Icc
  have hf : BalancedFeasible r a b := ⟨ha,hb,by
    rw [← hB.triangle_eq ha hb]
    exact hU.1⟩
  have hc := hB.cost_eq ha hb
  have hval := (isMinimizer_iff.mp hU).2
  have he : value r = balancedValue r := le_antisymm (value_le_balancedValue hr) (by
    rw [← hval,hc]
    exact balancedValue_le_cost hf)
  refine ⟨isBalancedMinimizer_iff.mpr ⟨hf,?_⟩,he⟩
  exact hc.symm.trans (hval.trans he)

namespace Section04

/-- The candidate parameters are forced by the scalar classification once a
minimizer is known to be balanced. -/
theorem balanced_minimizer_below_threshold {r a b : ℝ} {U : Graphon}
    (hr : r ∈ Ioo (0 : ℝ) threshold) (hU : IsMinimizer r U) (hB : IsBalanced U a b) :
    a = branchA (leftBranch r) ∧ b = branchB (leftBranch r) ∧ value r = balancedValue r := by
  have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le,(hr.2.trans threshold_mem_Ioo.2).le⟩
  obtain ⟨hm,he⟩ := hB.minimizer_bridge hr1 hU
  have hrt : r ∈ Ioo (0 : ℝ) transitionTarget := by
    simpa only [threshold_eq_transitionTarget] using hr
  have hab := (balancedMinimizer_below_transition hrt a b).mp hm
  exact ⟨hab.1,hab.2,he⟩

/-- At the critical target, any balanced minimizer is either the constant pair
or the unique nonconstant crossing pair. -/
theorem balanced_minimizer_at_threshold {a b : ℝ} {U : Graphon}
    (hU : IsMinimizer threshold U) (hB : IsBalanced U a b) :
    ((a=threshold ∧ b=threshold) ∨
      (a=branchA (leftBranch threshold) ∧ b=branchB (leftBranch threshold))) ∧
    value threshold = balancedValue threshold := by
  obtain ⟨hm,he⟩ := hB.minimizer_bridge
    ⟨threshold_mem_Ioo.1.le,threshold_mem_Ioo.2.le⟩ hU
  refine ⟨?_,he⟩
  rw [threshold_eq_transitionTarget] at hm ⊢
  exact (balancedMinimizer_at_transition a b).mp hm

end Section04
end SparseLowerTail

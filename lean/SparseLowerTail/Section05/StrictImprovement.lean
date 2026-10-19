import SparseLowerTail.Section04.BalancedPhase
import SparseLowerTail.Section04.ActiveConstraint

/-!
# Unrestricted strict improvement below the threshold

Theorem `thm:threshold`(iii), using the actual balanced phase classification.
This proves a strict upper bound for the unrestricted value and excludes all
constant minimizers. It does not prove the reverse variational inequality.
-/
noncomputable section
open Set MeasureTheory
namespace SparseLowerTail

/-- A constant representative of a graphon necessarily has its value in [0,1]. -/
theorem IsConstant.mem_Icc {U : Graphon} {c : ℝ} (h : IsConstant U c) : c ∈ Icc 0 1 := by
  obtain ⟨p,hp,hc⟩ := (U.bounded.and h).exists
  simpa only [hc] using hp

namespace Section05
open Section04

/-- Below the threshold, the explicit balanced branch strictly improves on the
constant even in the unrestricted graphon problem. -/
theorem value_le_branchCost_lt_entropy {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) threshold) :
    value r ≤ balancedCost (branchA (leftBranch r)) (branchB (leftBranch r)) ∧
      balancedCost (branchA (leftBranch r)) (branchB (leftBranch r)) < entropy r := by
  have hrt : r ∈ Ioo (0 : ℝ) transitionTarget := by
    simpa only [threshold_eq_transitionTarget] using hr
  have hb := balancedValue_below_transition hrt
  have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le,(hr.2.trans threshold_mem_Ioo.2).le⟩
  exact ⟨by rw [← hb.1]; exact value_le_balancedValue hr1, by rw [← hb.1]; exact hb.2.2⟩

theorem value_lt_entropy_below_threshold {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) threshold) :
    value r < entropy r := by
  have h := value_le_branchCost_lt_entropy hr
  exact h.1.trans_lt h.2

/-- No graphon minimizer below the threshold is almost everywhere constant,
even if the putative constant value is not specified in advance. -/
theorem no_constant_minimizer_below_threshold {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) threshold) {U : Graphon} (hm : IsMinimizer r U) :
    ∀ c : ℝ, ¬IsConstant U c := by
  intro c hc
  have hcb := hc.mem_Icc
  have ht := triangle_congr_ae (U := U) (W := constant c hcb) hc
  rw [triangle_constant] at ht
  have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1,hr.2.trans threshold_mem_Ioo.2⟩
  rw [minimizer_triangle_eq hr1 hm] at ht
  have hcr : r = c := (show Odd (3 : ℕ) by decide).strictMono_pow.injective ht
  have hf := cost_congr_ae (U := U) (W := constant c hcb) hc
  rw [cost_constant,← hcr,(isMinimizer_iff.mp hm).2] at hf
  exact (value_lt_entropy_below_threshold hr).ne hf

end Section05
end SparseLowerTail

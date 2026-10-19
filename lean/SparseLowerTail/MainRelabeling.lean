import SparseLowerTail.MainStatement
import SparseLowerTail.Section02.RelabelBalanced

/-! The manuscript's relabeling formulation of the main theorem.
These deductions do not prove MainTheorem: it remains an explicit input.
They ensure that its measurable-partition optimizer clauses give precisely
the pullback statements used in thm:main, with the CDF input visible. -/

noncomputable section
namespace SparseLowerTail
open Set Section02

/-- At the transition, replace the partition clause with actual measure-preserving
pullbacks of the canonical balanced graphon, equal almost everywhere. -/
theorem MainTheorem.at_transition_relabeling (h : MainTheorem)
    (hCDF : ClassicalCDFTransport) :
    ∃ a b : ℝ, ∃ ha : a ∈ Icc (0 : ℝ) 1, ∃ hb : b ∈ Icc (0 : ℝ) 1,
      0 < a ∧ a < threshold ∧ threshold < b ∧ b < 1 ∧
      IsBalancedMinimizer threshold a b ∧
      ∀ U : Graphon, IsMinimizer threshold U ↔
        IsConstant U threshold ∨ IsBalancedRelabeling U a b ha hb := by
  obtain ⟨a, b, ha0, hat, htb, hb1, hmin, hclass⟩ := h.at_transition
  have ha : a ∈ Icc (0 : ℝ) 1 := ⟨ha0.le, (hat.trans (htb.trans hb1)).le⟩
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨(ha0.trans (hat.trans htb)).le, hb1.le⟩
  refine ⟨a, b, ha, hb, ha0, hat, htb, hb1, hmin, ?_⟩
  intro U
  rw [hclass U, isBalanced_iff_relabel hCDF ha hb]

/-- Below the transition the scalar pair stays unique, and every graphon
optimizer is an almost-everywhere pullback of its canonical balanced graphon. -/
theorem MainTheorem.below_transition_relabeling (h : MainTheorem)
    (hCDF : ClassicalCDFTransport) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) threshold) :
    ∃ a b : ℝ, ∃ ha : a ∈ Icc (0 : ℝ) 1, ∃ hb : b ∈ Icc (0 : ℝ) 1,
      0 < a ∧ a < r ∧ r < b ∧ b < 1 ∧
      IsBalancedMinimizer r a b ∧
      (∀ c d : ℝ, IsBalancedMinimizer r c d → c = a ∧ d = b) ∧
      ∀ U : Graphon, IsMinimizer r U ↔ IsBalancedRelabeling U a b ha hb := by
  obtain ⟨a, b, ha0, har, hrb, hb1, hmin, hunique, hclass⟩ := h.below_transition r hr
  have ha : a ∈ Icc (0 : ℝ) 1 := ⟨ha0.le, (har.trans (hrb.trans hb1)).le⟩
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨(ha0.trans (har.trans hrb)).le, hb1.le⟩
  refine ⟨a, b, ha, hb, ha0, har, hrb, hb1, hmin, hunique, ?_⟩
  intro U
  exact (hclass U).trans (isBalanced_iff_relabel hCDF ha hb)

end SparseLowerTail

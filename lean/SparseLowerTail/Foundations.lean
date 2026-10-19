import SparseLowerTail.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Basic well-posedness checks for the variational definitions. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail

theorem entropy_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ entropy x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x; simp
  · have hi := Real.one_sub_inv_le_log_of_pos h
    have hm := mul_le_mul_of_nonneg_left hi (le_of_lt h)
    have hc : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h)
    unfold entropy
    nlinarith

theorem entropy_le_one {x : ℝ} (hx : x ∈ Icc 0 1) : entropy x ≤ 1 := by
  have hl := Real.log_nonpos hx.1 hx.2
  have hm := mul_nonpos_of_nonneg_of_nonpos hx.1 hl
  unfold entropy
  linarith [hx.1]

theorem continuous_entropy : Continuous entropy := by
  exact (Real.continuous_mul_log.sub continuous_id).add continuous_const

theorem cost_integrable (U : Graphon) :
    Integrable (fun p => entropy (U p)) squareMeasure := by
  apply Integrable.of_bound
    (continuous_entropy.measurable.comp_aemeasurable U.measurable).aestronglyMeasurable 1
  filter_upwards [U.bounded] with p hp
  change ‖entropy (U p)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (entropy_nonneg hp.1)]
  exact entropy_le_one hp

theorem cost_nonneg (U : Graphon) : 0 ≤ cost U := by
  apply integral_nonneg_of_ae
  filter_upwards [U.bounded] with p hp
  exact entropy_nonneg hp.1

theorem cost_le_one (U : Graphon) : cost U ≤ 1 := by
  have h : cost U ≤ ∫ _ : ℝ × ℝ, (1 : ℝ) ∂squareMeasure := by
    apply integral_mono_ae (cost_integrable U) (integrable_const 1)
    filter_upwards [U.bounded] with p hp
    exact entropy_le_one hp
  simpa using h

theorem feasible_costs_bddBelow (r : ℝ) :
    BddBelow {v | ∃ U : Graphon, Feasible r U ∧ cost U = v} := by
  refine ⟨0, ?_⟩
  rintro v ⟨U, _, rfl⟩
  exact cost_nonneg U

theorem value_le_cost {r : ℝ} {U : Graphon} (hU : Feasible r U) :
    value r ≤ cost U := csInf_le (feasible_costs_bddBelow r) ⟨U, hU, rfl⟩

theorem value_nonneg {r : ℝ} (hr : r ∈ Icc 0 1) : 0 ≤ value r := by
  apply le_csInf
    (show {v | ∃ U : Graphon, Feasible r U ∧ cost U = v}.Nonempty from
      ⟨_, constant r hr, constant_feasible r hr, rfl⟩)
  rintro v ⟨U, _, rfl⟩
  exact cost_nonneg U

theorem value_le_entropy {r : ℝ} (hr : r ∈ Icc 0 1) : value r ≤ entropy r := by
  simpa using value_le_cost (constant_feasible r hr)

/-- The order-based optimizer definition agrees with the paper's equality to V.
This does not assert existence of a minimizer. -/
theorem isMinimizer_iff {r : ℝ} {U : Graphon} :
    IsMinimizer r U ↔ Feasible r U ∧ cost U = value r := by
  constructor
  · rintro ⟨hf, hmin⟩
    refine ⟨hf, le_antisymm ?_ (value_le_cost hf)⟩
    unfold value
    refine le_csInf ?_ ?_
    · exact ⟨cost U, U, hf, rfl⟩
    · rintro v ⟨W, hW, rfl⟩
      exact hmin W hW
  · rintro ⟨hf, heq⟩
    refine ⟨hf, fun W hW => ?_⟩
    rw [heq]
    exact value_le_cost hW

theorem balanced_diagonal_feasible {r : ℝ} (hr : r ∈ Icc 0 1) :
    BalancedFeasible r r r := ⟨hr, hr, by simp⟩

theorem balancedCost_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ balancedCost a b := by
  exact div_nonneg (add_nonneg (entropy_nonneg ha) (entropy_nonneg hb)) (by norm_num)

theorem balanced_costs_bddBelow (r : ℝ) :
    BddBelow {v | ∃ a b : ℝ, BalancedFeasible r a b ∧ balancedCost a b = v} := by
  refine ⟨0, ?_⟩
  rintro v ⟨a, b, hf, rfl⟩
  exact balancedCost_nonneg hf.1.1 hf.2.1.1

theorem balancedValue_le_cost {r a b : ℝ} (hf : BalancedFeasible r a b) :
    balancedValue r ≤ balancedCost a b :=
  csInf_le (balanced_costs_bddBelow r) ⟨a, b, hf, rfl⟩

theorem balancedValue_nonneg {r : ℝ} (hr : r ∈ Icc 0 1) :
    0 ≤ balancedValue r := by
  unfold balancedValue
  refine le_csInf ?_ ?_
  · exact ⟨balancedCost r r, r, r, balanced_diagonal_feasible hr, rfl⟩
  · rintro v ⟨a, b, hf, rfl⟩
    exact balancedCost_nonneg hf.1.1 hf.2.1.1

theorem balancedValue_le_entropy {r : ℝ} (hr : r ∈ Icc 0 1) :
    balancedValue r ≤ entropy r := by
  simpa using balancedValue_le_cost (balanced_diagonal_feasible hr)

theorem isBalancedMinimizer_iff {r a b : ℝ} :
    IsBalancedMinimizer r a b ↔
      BalancedFeasible r a b ∧ balancedCost a b = balancedValue r := by
  constructor
  · rintro ⟨hf, hmin⟩
    refine ⟨hf, le_antisymm ?_ (balancedValue_le_cost hf)⟩
    unfold balancedValue
    refine le_csInf ?_ ?_
    · exact ⟨balancedCost a b, a, b, hf, rfl⟩
    · rintro v ⟨c, d, hcd, rfl⟩
      exact hmin c d hcd
  · rintro ⟨hf, heq⟩
    refine ⟨hf, fun c d hcd => ?_⟩
    rw [heq]
    exact balancedValue_le_cost hcd

end SparseLowerTail

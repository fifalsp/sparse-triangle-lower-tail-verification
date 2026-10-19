import SparseLowerTail.Section05.CoverConstantDigits
import SparseLowerTail.Section05.LogBoxSubdivision

/-! Elementary, uniformly valid exponential enclosures used by actual
non-apex box certificates. -/
noncomputable section
namespace SparseLowerTail.Section05
open Numerics

/-- The lower tangent and reciprocal upper tangent bound exp(-x). -/
theorem exp_neg_linear_bounds {x l u : ℝ} (hl : 0 ≤ l) (hx : x ∈ Set.Icc l u) :
    Bounds (Real.exp (-x)) (1-u) (1/(1+l)) := by
  constructor
  · have h := Real.add_one_le_exp (-x)
    linarith [hx.2]
  · rw [Real.exp_neg,one_div]
    apply inv_anti₀ (by linarith : 0 < 1+l)
    have h := Real.add_one_le_exp x
    linarith [hx.1]

theorem log_exp_neg_bounds {x l u : ℝ} (hx : x ∈ Set.Icc l u) :
    Bounds (Real.log (Real.exp (-x))) (-u) (-l) := by
  rw [Real.log_exp]
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

/-- A concrete exponential bound, proved by a short Taylor expansion and
raising to the sixteenth power, sufficient for an entire large tail box. -/
theorem exp_neg_eight_upper : Real.exp (-8) ≤ 1/2900 := by
  have h := exp_taylor_bounds (x := (1/2:ℝ)) (by norm_num) (n := 8) (by norm_num)
  have hlo : (16487/10000 : ℝ) ≤ Real.exp (1/2) := by
    norm_num [Finset.sum_range_succ,Nat.factorial] at h
    linarith [h.1]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 16487/10000) hlo 16
  have he : Real.exp (8:ℝ) = Real.exp (1/2)^16 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h8 : (2900:ℝ) ≤ Real.exp 8 := by
    rw [he]
    exact le_trans (by norm_num) hp
  rw [Real.exp_neg,one_div]
  exact inv_anti₀ (by norm_num) h8

/-- The whole semi-infinite tail has a uniform small exponential upper bound. -/
theorem exp_neg_tail_bounds {x : ℝ} (hx : 8 ≤ x) :
    Bounds (Real.exp (-x)) 0 (1/2900) :=
  ⟨le_of_lt (Real.exp_pos _),
    (Real.exp_le_exp.mpr (neg_le_neg hx)).trans exp_neg_eight_upper⟩

end SparseLowerTail.Section05

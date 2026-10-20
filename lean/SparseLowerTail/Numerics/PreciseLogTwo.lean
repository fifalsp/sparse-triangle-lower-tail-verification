import SparseLowerTail.Numerics.Intervals

/-! A precise logarithm enclosure for the current manuscript's crossing proof. -/
noncomputable section
namespace SparseLowerTail.Numerics
set_option maxHeartbeats 4000000

theorem log_two_bounds_40 : Bounds (Real.log 2)
    (6931471805599453094172321214581765680755/10^40) (6931471805599453094172321214581765680756/10^40) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/2 : ℝ)) (by norm_num) 160
  norm_num [Finset.sum_range_succ] at h
  rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

end SparseLowerTail.Numerics

import SparseLowerTail.Section05.RelaxedLaw
import SparseLowerTail.Numerics.IntervalArithmetic

/-! Coarse but kernel-checked enclosures of exact critical constants for cover
arithmetic. No certificate output or rounded floating-point value is trusted. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section04 Numerics

theorem criticalA_coarse_bounds : Bounds criticalA (17/1000) (18/1000) := by
  exact transition_digits.1.weaken (by norm_num) (by norm_num)

theorem criticalB_coarse_bounds : Bounds criticalB (849/1000) (850/1000) := by
  exact transition_digits.2.1.weaken (by norm_num) (by norm_num)

theorem critical_logA_lower : -5 ≤ Real.log criticalA := by
  have ha := criticalA_coarse_bounds
  have ha0 : 0 < criticalA := by linarith [ha.1]
  have h64 : 1 ≤ 64*criticalA := by linarith [ha.1]
  have hp := Real.log_nonneg h64
  have he : Real.log (64*criticalA)=6*Real.log 2+Real.log criticalA := by
    rw [show (64:ℝ)=(2:ℝ)^6 by norm_num,
      Real.log_mul (by positivity) (ne_of_gt ha0),Real.log_pow]
    norm_num
  rw [he] at hp
  have hb := log_two_bounds_22.2
  linarith

/-- Deliberately coarse, sufficient for a first non-apex certificate box. -/
theorem criticalOmega_coarse_bounds : Bounds criticalOmega 0 2 := by
  have ha := criticalA_coarse_bounds
  have hb := criticalB_coarse_bounds
  have hl := critical_logA_lower
  have ha0 : 0 ≤ criticalA := by linarith [ha.1]
  have hb0 : 0 < criticalB := by linarith [hb.1]
  have hb1 : criticalB ≤ 1 := by linarith [hb.2]
  have hlogb := Real.log_nonpos (le_of_lt hb0) hb1
  have hea : 892/1000 ≤ entropy criticalA := by
    have h := mul_le_mul_of_nonneg_left hl ha0
    unfold entropy
    nlinarith [ha.2]
  have heb : entropy criticalB ≤ 151/1000 := by
    have h := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb0) hlogb
    unfold entropy
    nlinarith [hb.1]
  constructor
  · exact le_of_lt criticalOmega_pos
  · unfold criticalOmega
    apply (div_le_iff₀ critical_entropy_gap_pos).mpr
    linarith [ha.1,hb.2]

theorem criticalTriangle_checked_bounds : Bounds criticalTriangle
    (9217366/10^9) (9217368/10^9) := by
  exact (threshold_digits.pow (by norm_num) 3).weaken (by norm_num) (by norm_num)

end SparseLowerTail.Section05

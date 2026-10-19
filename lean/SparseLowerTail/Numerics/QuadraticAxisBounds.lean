import Mathlib.Tactic

/-! The three one-coordinate quadratic bounds used by the family verifier.
The positive-curvature and endpoint cases preserve improvements that would
be lost by replacing the entire quadratic term by an absolute error. -/
noncomputable section
namespace SparseLowerTail.Numerics

/-- The interval-safe bound, valid for either sign of the curvature. -/
theorem quadratic_axis_basic {g h d r P : ℝ} (hg : |g|≤P) (hd : |d|≤r) :
    -P*r+min 0 h*r^2/2 ≤ g*d+h*d^2/2 := by
  have hr : 0≤r := (abs_nonneg d).trans hd
  have hlin : -P*r≤g*d := by
    have hh := mul_le_mul hg hd (abs_nonneg d) ((abs_nonneg g).trans hg)
    rw [←abs_mul] at hh
    linarith [neg_abs_le (g*d)]
  have hd2 : d^2≤r^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hquad : min 0 h*r^2≤h*d^2 := by
    exact (mul_le_mul_of_nonpos_left hd2 (min_le_left 0 h)).trans
      (mul_le_mul_of_nonneg_right (min_le_right 0 h) (sq_nonneg d))
  linarith

/-- Unconstrained minimum of a positive-curvature quadratic. -/
theorem quadratic_axis_vertex {g h d P : ℝ} (hg : |g|≤P) (hh : 0<h) :
    -P^2/(2*h) ≤ g*d+h*d^2/2 := by
  have hg2 : g^2≤P^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg g) hg 2
  apply (div_le_iff₀ (by positivity : 0<2*h)).mpr
  nlinarith [sq_nonneg (g+h*d)]

/-- If the stationary point lies outside the allowed interval, use its
endpoint. A lower bound on |g| certifies this case. -/
theorem quadratic_axis_endpoint {g h d r P m : ℝ}
    (hg : |g|≤P) (hm : m≤|g|) (hd : |d|≤r) (hh : 0<h) (hfar : h*r≤m) :
    -P*r+h*r^2/2 ≤ g*d+h*d^2/2 := by
  have hr : 0≤r := (abs_nonneg d).trans hd
  have hgr : h*r≤|g| := hfar.trans hm
  have hx : 0≤r-|d| := sub_nonneg.mpr hd
  have hfactor : 0≤|g|-h*(r+|d|)/2 := by nlinarith
  have hp := mul_nonneg hx hfactor
  have hlin : -(|g| * |d|)≤g*d := by
    simpa only [←abs_mul] using neg_abs_le (g*d)
  have hpgr := mul_le_mul_of_nonneg_right hg hr
  have hsq : |d|^2=d^2 := sq_abs d
  nlinarith

/-- A verifier may choose any of the three certified candidates. The
numeric choice itself is not a mathematical hypothesis about the function. -/
theorem quadratic_axis_chosen {g h d r P m β : ℝ}
    (hg : |g|≤P) (hm : m≤|g|) (hd : |d|≤r)
    (hchoice : β≤-P*r+min 0 h*r^2/2 ∨
      (0<h ∧ β≤-P^2/(2*h)) ∨
      (0<h ∧ h*r≤m ∧ β≤-P*r+h*r^2/2)) :
    β≤g*d+h*d^2/2 := by
  rcases hchoice with hb | ⟨hh,hb⟩ | ⟨hh,hfar,hb⟩
  · exact hb.trans (quadratic_axis_basic hg hd)
  · exact hb.trans (quadratic_axis_vertex hg hh)
  · exact hb.trans (quadratic_axis_endpoint hg hm hd hh hfar)

end SparseLowerTail.Numerics

import SparseLowerTail.Numerics.Intervals

/-! Reusable kernel-checked operations for generated cover certificates.
Rational endpoints are proposals; the arithmetic and analytic enclosure
obligations in the statements are checked by Lean. -/
noncomputable section
namespace SparseLowerTail.Numerics

/-- An affine function is bounded by bounds at both endpoints. -/
theorem Bounds.mul_const_corners {x l u c L U : ℝ} (hx : Bounds x l u)
    (hll : L ≤ l*c) (hul : L ≤ u*c) (hlu : l*c ≤ U) (huu : u*c ≤ U) :
    Bounds (x*c) L U := by
  rcases le_total 0 c with hc | hc
  · constructor
    · exact hll.trans (mul_le_mul_of_nonneg_right hx.1 hc)
    · exact (mul_le_mul_of_nonneg_right hx.2 hc).trans huu
  · constructor
    · exact hul.trans (mul_le_mul_of_nonpos_right hx.2 hc)
    · exact (mul_le_mul_of_nonpos_right hx.1 hc).trans hlu

/-- Signed interval multiplication, using all four exact corner products. -/
theorem Bounds.mul_corners {x l u y v w L U : ℝ}
    (hx : Bounds x l u) (hy : Bounds y v w)
    (hll : L ≤ l*v) (hlu : L ≤ l*w) (hul : L ≤ u*v) (huu : L ≤ u*w)
    (hll' : l*v ≤ U) (hlu' : l*w ≤ U) (hul' : u*v ≤ U) (huu' : u*w ≤ U) :
    Bounds (x*y) L U := by
  have hl : Bounds (l*y) L U := by
    simpa only [mul_comm] using hy.mul_const_corners (c := l) (L := L) (U := U)
      (by simpa [mul_comm] using hll) (by simpa [mul_comm] using hlu)
      (by simpa [mul_comm] using hll') (by simpa [mul_comm] using hlu')
  have hu : Bounds (u*y) L U := by
    simpa only [mul_comm] using hy.mul_const_corners (c := u) (L := L) (U := U)
      (by simpa [mul_comm] using hul) (by simpa [mul_comm] using huu)
      (by simpa [mul_comm] using hul') (by simpa [mul_comm] using huu')
  exact hx.mul_const_corners hl.1 hu.1 hl.2 hu.2

/-- Exponential monotonicity lifts endpoint certificates to whole intervals. -/
theorem Bounds.exp_of_endpoints {x l u L U : ℝ} (hx : Bounds x l u)
    (hl : L ≤ Real.exp l) (hu : Real.exp u ≤ U) : Bounds (Real.exp x) L U :=
  ⟨hl.trans (Real.exp_le_exp.mpr hx.1), (Real.exp_le_exp.mpr hx.2).trans hu⟩

/-- Logarithm monotonicity lifts endpoint certificates to positive intervals. -/
theorem Bounds.log_of_endpoints {x l u L U : ℝ} (hx : Bounds x l u)
    (hl0 : 0 < l) (hl : L ≤ Real.log l) (hu : Real.log u ≤ U) :
    Bounds (Real.log x) L U :=
  ⟨hl.trans (Real.log_le_log hl0 hx.1),
    (Real.log_le_log (hl0.trans_le hx.1) hx.2).trans hu⟩

/-- Taylor enclosure of exp on [-1,1], in a form used by proof generators. -/
theorem exp_taylor_bounds {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    Bounds (Real.exp x)
      ((∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ))-
        |x|^n*((n+1 : ℕ)/(n.factorial*n) : ℝ))
      ((∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ))+
        |x|^n*((n+1 : ℕ)/(n.factorial*n) : ℝ)) := by
  have h := abs_le.mp (Real.exp_bound hx hn)
  constructor <;> linarith

/-- Repeated squaring extends a short-argument exponential enclosure. -/
theorem Bounds.exp_scale_pow {x l u : ℝ} (h : Bounds (Real.exp x) l u)
    (hl : 0 ≤ l) (n : ℕ) : Bounds (Real.exp ((n : ℝ)*x)) (l^n) (u^n) := by
  simpa only [Real.exp_nat_mul] using h.pow hl n

/-- Taylor enclosure of log(1-x), with a proved remainder. -/
theorem log_taylor_bounds {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    Bounds (Real.log (1-x))
      (-(∑ i ∈ Finset.range n, x^(i+1)/(i+1 : ℝ))-|x|^(n+1)/(1-|x|))
      (-(∑ i ∈ Finset.range n, x^(i+1)/(i+1 : ℝ))+|x|^(n+1)/(1-|x|)) := by
  have h := abs_le.mp (Real.abs_log_sub_add_sum_range_le hx n)
  constructor <;> linarith

end SparseLowerTail.Numerics

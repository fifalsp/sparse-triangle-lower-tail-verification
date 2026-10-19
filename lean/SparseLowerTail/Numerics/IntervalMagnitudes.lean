import SparseLowerTail.Numerics.DyadicFiniteSum

/-! Rational magnitude bounds and propagation through a certified error. -/
namespace SparseLowerTail.Numerics
namespace RationalInterval

def absUpper (I : RationalInterval) : ℚ := max (-I.lower) I.upper
def absLower (I : RationalInterval) : ℚ := max 0 (max I.lower (-I.upper))

theorem absUpper_bound {I : RationalInterval} {x : ℝ} (hx : I.contains x) :
    |x|≤(I.absUpper : ℝ) := by
  simp only [absUpper,Rat.cast_max,Rat.cast_neg]
  exact abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans (by simpa using hx.1),
    hx.2.trans (le_max_right _ _)⟩

theorem absLower_bound {I : RationalInterval} {x : ℝ} (hx : I.contains x) :
    (I.absLower : ℝ)≤|x| := by
  simp only [absLower,Rat.cast_max,Rat.cast_neg,Rat.cast_zero,max_le_iff]
  exact ⟨abs_nonneg _,hx.1.trans (le_abs_self _),
    (neg_le_neg hx.2).trans (neg_le_abs _)⟩

/-- Both sides of the gradient-magnitude interval are needed by the
endpoint quadratic candidate. -/
theorem magnitude_bounds_of_error {I : RationalInterval} {x y E : ℝ}
    (hx : I.contains x) (he : |y-x|≤E) :
    (I.absLower : ℝ)-E≤|y| ∧ |y|≤(I.absUpper : ℝ)+E := by
  have hy := abs_add_le (y-x) x
  have hxx := abs_add_le (x-y) y
  simp only [sub_add_cancel] at hy hxx
  rw [abs_sub_comm x y] at hxx
  constructor <;> linarith [absLower_bound hx,absUpper_bound hx]

end RationalInterval

/-- Intervals are convex; useful for the L and q segments in leaf soundness. -/
theorem Bounds.segment {a b x y s : ℝ} (hx : Bounds x a b) (hy : Bounds y a b)
    (hs0 : 0≤s) (hs1 : s≤1) : Bounds (x+s*(y-x)) a b := by
  constructor
  · nlinarith [_root_.mul_nonneg hs0 (sub_nonneg.mpr hy.1),
      _root_.mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hx.1)]
  · nlinarith [_root_.mul_nonneg hs0 (sub_nonneg.mpr hy.2),
      _root_.mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hx.2)]

theorem DyadicInterval.toRational_absUpper (I : DyadicInterval) :
    (I.toRational.absUpper : ℝ)=(I.absBound : ℝ)/DyadicInterval.scale := by
  simp only [RationalInterval.absUpper,DyadicInterval.toRational,DyadicInterval.absBound,
    Rat.cast_max,Rat.cast_neg,Rat.cast_div,Rat.cast_intCast,Int.cast_max,Int.cast_neg]
  simpa only [neg_div] using max_div_div_right DyadicInterval.scale_real_pos.le (-(I.lower : ℝ)) (I.upper : ℝ)

end SparseLowerTail.Numerics

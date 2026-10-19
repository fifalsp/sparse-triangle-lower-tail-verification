import SparseLowerTail.Numerics.DyadicInterval

/-! Fail-closed reciprocal enclosures, for rational certificate coefficients.
An interval meeting zero is rejected rather than assigned a false bound. -/
namespace SparseLowerTail.Numerics.DyadicInterval

def invPositive (I : DyadicInterval) : DyadicInterval :=
  ⟨scale^2/I.upper,ceilDiv (scale^2) I.lower⟩

theorem invPositive_contains {I : DyadicInterval} {x : ℝ}
    (hx : I.contains x) (hl : 0<I.lower) : (invPositive I).contains x⁻¹ := by
  have hsl := scale_real_pos
  have hlr : (0:ℝ)<(I.lower:ℝ)/scale := div_pos (by exact_mod_cast hl) hsl
  have hxr := hlr.trans_le hx.1
  have hur : (0:ℝ)<(I.upper:ℝ) := (div_pos_iff.mp (hxr.trans_le hx.2)).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hu : (0:ℤ)<I.upper := by exact_mod_cast hur
  have hlo := (rounded_div_bounds (scale^2) I.upper hu).1
  have hhi := (rounded_div_bounds (scale^2) I.lower hl).2
  have helu : ((scale^2:ℤ):ℝ)/(I.upper:ℝ)/scale=1/((I.upper:ℝ)/scale) := by
    push_cast
    field_simp
  have hell : ((scale^2:ℤ):ℝ)/(I.lower:ℝ)/scale=1/((I.lower:ℝ)/scale) := by
    push_cast
    field_simp
  rw [helu] at hlo
  rw [hell] at hhi
  refine ⟨?_,?_⟩
  · exact hlo.trans (by simpa using one_div_le_one_div_of_le hxr hx.2)
  · have hh : x⁻¹≤1/((I.lower:ℝ)/scale) := by
      simpa using one_div_le_one_div_of_le hlr hx.1
    exact hh.trans hhi

/-- Signed reciprocal, defined only for a box separated from zero. -/
def inv? (I : DyadicInterval) : Option DyadicInterval :=
  if 0<I.lower then some (invPositive I)
  else if I.upper<0 then some ((invPositive I.neg).neg)
  else none

theorem inv?_contains {I J : DyadicInterval} {x : ℝ} (hx : I.contains x)
    (hJ : I.inv?=some J) : J.contains x⁻¹ := by
  unfold inv? at hJ
  split_ifs at hJ with hp hn
  · cases hJ
    exact invPositive_contains hx hp
  · cases hJ
    have hneg := invPositive_contains (neg_contains hx)
      (show 0<I.neg.lower by simpa [neg] using neg_pos.mpr hn)
    simpa only [inv_neg,neg_neg] using neg_contains hneg

end SparseLowerTail.Numerics.DyadicInterval

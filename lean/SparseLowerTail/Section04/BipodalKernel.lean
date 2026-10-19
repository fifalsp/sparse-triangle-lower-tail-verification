import SparseLowerTail.Section04.BipodalDefinitions

/-! The pointwise positivity part of the integral proof of `lem:J`. -/
noncomputable section
open Set
namespace SparseLowerTail.Section04

theorem bipodalOmega_swap (x y s t : ℝ) : bipodalOmega x y s t = bipodalOmega x y t s := by
  unfold bipodalOmega bipodalBilinear
  ring

theorem bipodalOmega_low {x y s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ y) :
    bipodalOmega x y s t = (1-y)*y*(s-x)*(t-x)*(1-(s+t)/2) := by
  have hsy : s-y ≤ 0 := by linarith
  have hty : t-y ≤ 0 := by linarith
  have hs2 : s^2-y^2 ≤ 0 := by nlinarith
  have ht2 : t^2-y^2 ≤ 0 := by nlinarith
  simp [bipodalOmega,bipodalBilinear,bipodalPhi,max_eq_right hsy,max_eq_right hty,
    max_eq_right hs2,max_eq_right ht2]
  ring

theorem bipodalOmega_high {x y s t : ℝ} (hy : 0 ≤ y) (hs : y ≤ s) (ht : y ≤ t) :
    bipodalOmega x y s t = (y-x)/2*
      ((1-x*y)*((1-s)-(1-t))^2+(1-s)*(1-t)*
        (2*(x+y-2*x*y)-(x+y)*((1-s)+(1-t)))) := by
  have hsy : 0 ≤ s-y := sub_nonneg.mpr hs
  have hty : 0 ≤ t-y := sub_nonneg.mpr ht
  have hs2 : 0 ≤ s^2-y^2 := by nlinarith
  have ht2 : 0 ≤ t^2-y^2 := by nlinarith
  simp [bipodalOmega,bipodalBilinear,bipodalPhi,max_eq_left hsy,max_eq_left hty,
    max_eq_left hs2,max_eq_left ht2]
  ring

theorem bipodalOmega_mixed {x y s t : ℝ} (hs : 0 ≤ s) (hsy : s ≤ y) (hyt : y ≤ t) :
    bipodalOmega x y s t = (s-x)/2*
      ((1-y)*y*(t-x)*(1-s+(1-t))+(t-y)*((1-x)*(t-y)-(1-y)*(s-x))) := by
  have hsy' : s-y ≤ 0 := sub_nonpos.mpr hsy
  have hty : 0 ≤ t-y := sub_nonneg.mpr hyt
  have hs2 : s^2-y^2 ≤ 0 := by nlinarith
  have ht2 : 0 ≤ t^2-y^2 := by nlinarith
  simp [bipodalOmega,bipodalBilinear,bipodalPhi,max_eq_right hsy',max_eq_left hty,
    max_eq_right hs2,max_eq_left ht2]
  ring

/-- The mixed-region affine interpolation identity. Its remainder is
nonnegative on x≤s≤y≤t≤1. -/
theorem bipodalOmega_mixed_compare_identity {x y s t : ℝ}
    (hs : 0 ≤ s) (hsy : s ≤ y) (hyt : y ≤ t) :
    (y-x)*bipodalOmega x y s t = (s-x)*bipodalOmega x y y t+
      (y-x)*(s-x)*(y-s)*(1-y)*(y*(t-x)+(t-y))/2 := by
  rw [bipodalOmega_mixed hs hsy hyt,
    bipodalOmega_mixed (hs.trans hsy) (le_refl y) hyt]
  ring

private theorem high_factor_pos {x y s t : ℝ} (hx : 0 < x) (hxy : x < y)
    (_hy : y < 1) (hs : s ∈ Icc y 1) (ht : t ∈ Icc y 1) :
    0 < 2*(x+y-2*x*y)-(x+y)*((1-s)+(1-t)) := by
  have hm : (x+y)*((1-s)+(1-t)) ≤ (x+y)*(2*(1-y)) :=
    mul_le_mul_of_nonneg_left (by linarith [hs.1,ht.1]) (by linarith)
  have hp : 0 < 2*y*(y-x) := mul_pos (by linarith) (sub_pos.mpr hxy)
  nlinarith

private theorem one_sub_mul_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    0 < 1-x*y := by
  have h := mul_lt_mul_of_pos_left hy hx
  nlinarith

theorem bipodalOmega_high_nonneg {x y s t : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < 1) (hs : s ∈ Icc y 1) (ht : t ∈ Icc y 1) :
    0 ≤ bipodalOmega x y s t := by
  rw [bipodalOmega_high (hx.trans hxy).le hs.1 ht.1]
  have hfac := high_factor_pos hx hxy hy hs ht
  have hS := one_sub_mul_pos hx hxy hy
  have hp : 0 ≤ 1-s := sub_nonneg.mpr hs.2
  have hq : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have he : 0 < y-x := sub_pos.mpr hxy
  positivity

/-- In the upper region, it suffices that the first coordinate is below one
for strict positivity; this also covers the mixed region's boundary (y,t). -/
theorem bipodalOmega_high_pos {x y s t : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < 1) (hs : s ∈ Ico y 1) (ht : t ∈ Icc y 1) :
    0 < bipodalOmega x y s t := by
  rw [bipodalOmega_high (hx.trans hxy).le hs.1 ht.1]
  have hfac := high_factor_pos hx hxy hy ⟨hs.1,hs.2.le⟩ ht
  have hS := one_sub_mul_pos hx hxy hy
  have hp : 0 < 1-s := sub_pos.mpr hs.2
  have hq : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have he : 0 < y-x := sub_pos.mpr hxy
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · simp only [sub_self,sub_zero,mul_zero,zero_mul,add_zero]
    positivity
  · have hq' : 0 < 1-t := sub_pos.mpr ht1
    positivity

theorem bipodalOmega_mixed_nonneg {x y s t : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < 1) (hs : s ∈ Icc x y) (ht : t ∈ Icc y 1) :
    0 ≤ bipodalOmega x y s t := by
  have hid := bipodalOmega_mixed_compare_identity (x := x) (hx.le.trans hs.1) hs.2 ht.1
  have hbase := bipodalOmega_high_pos hx hxy hy ⟨le_rfl,hy⟩ ht
  have he : 0 < y-x := sub_pos.mpr hxy
  have hp : 0 ≤ s-x := sub_nonneg.mpr hs.1
  have hq : 0 ≤ y-s := sub_nonneg.mpr hs.2
  have hβ : 0 < 1-y := sub_pos.mpr hy
  have htx : 0 < t-x := sub_pos.mpr (hxy.trans_le ht.1)
  have hty : 0 ≤ t-y := sub_nonneg.mpr ht.1
  have hrem : 0 ≤ (y-x)*(s-x)*(y-s)*(1-y)*(y*(t-x)+(t-y))/2 := by
    have hyp := hx.trans hxy
    positivity
  have hfirst : 0 ≤ (s-x)*bipodalOmega x y y t := mul_nonneg hp hbase.le
  nlinarith

theorem bipodalOmega_mixed_pos {x y s t : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < 1) (hs : s ∈ Ioc x y) (ht : t ∈ Icc y 1) :
    0 < bipodalOmega x y s t := by
  have hid := bipodalOmega_mixed_compare_identity (x := x) (hx.trans hs.1).le hs.2 ht.1
  have hbase := bipodalOmega_high_pos hx hxy hy ⟨le_rfl,hy⟩ ht
  have he : 0 < y-x := sub_pos.mpr hxy
  have hp : 0 < s-x := sub_pos.mpr hs.1
  have hq : 0 ≤ y-s := sub_nonneg.mpr hs.2
  have hβ : 0 < 1-y := sub_pos.mpr hy
  have htx : 0 < t-x := sub_pos.mpr (hxy.trans_le ht.1)
  have hty : 0 ≤ t-y := sub_nonneg.mpr ht.1
  have hrem : 0 ≤ (y-x)*(s-x)*(y-s)*(1-y)*(y*(t-x)+(t-y))/2 := by
    have hyp := hx.trans hxy
    positivity
  have hfirst : 0 < (s-x)*bipodalOmega x y y t := mul_pos hp hbase
  nlinarith

/-- Nonnegativity throughout the closed integration square. -/
theorem bipodalOmega_nonneg {x y s t : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < 1) (hs : s ∈ Icc x 1) (ht : t ∈ Icc x 1) :
    0 ≤ bipodalOmega x y s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [bipodalOmega_swap]
    exact this ht hs (le_of_not_ge hst)
  by_cases hty : t ≤ y
  · rw [bipodalOmega_low (hx.le.trans hs.1) hst hty]
    have hp : 0 ≤ s-x := sub_nonneg.mpr hs.1
    have hq : 0 ≤ t-x := sub_nonneg.mpr ht.1
    have hβ : 0 < 1-y := sub_pos.mpr hy
    have hy0 := hx.trans hxy
    have hf : 0 < 1-(s+t)/2 := by linarith
    positivity
  · by_cases hsy : s ≤ y
    · exact bipodalOmega_mixed_nonneg hx hxy hy ⟨hs.1,hsy⟩ ⟨(lt_of_not_ge hty).le,ht.2⟩
    · exact bipodalOmega_high_nonneg hx hxy hy ⟨(lt_of_not_ge hsy).le,hs.2⟩
        ⟨(lt_of_not_ge hty).le,ht.2⟩

/-- Strict positivity throughout the open square, as required by `lem:J`. -/
theorem bipodalOmega_pos {x y s t : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < 1) (hs : s ∈ Ioo x 1) (ht : t ∈ Ioo x 1) :
    0 < bipodalOmega x y s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [bipodalOmega_swap]
    exact this ht hs (le_of_not_ge hst)
  by_cases hty : t ≤ y
  · rw [bipodalOmega_low (hx.trans hs.1).le hst hty]
    have hp : 0 < s-x := sub_pos.mpr hs.1
    have hq : 0 < t-x := sub_pos.mpr ht.1
    have hβ : 0 < 1-y := sub_pos.mpr hy
    have hy0 := hx.trans hxy
    have hf : 0 < 1-(s+t)/2 := by linarith
    positivity
  · by_cases hsy : s ≤ y
    · exact bipodalOmega_mixed_pos hx hxy hy ⟨hs.1,hsy⟩ ⟨(lt_of_not_ge hty).le,ht.2.le⟩
    · exact bipodalOmega_high_pos hx hxy hy ⟨(lt_of_not_ge hsy).le,hs.2⟩
        ⟨(lt_of_not_ge hty).le,ht.2.le⟩

/-- Strict positivity on the edge needed for the single integral in Jrep. -/
theorem bipodalOmega_single_pos {x y s : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < 1) (hs : s ∈ Ioo x 1) : 0 < bipodalOmega x y s 1 := by
  by_cases hsy : s ≤ y
  · exact bipodalOmega_mixed_pos hx hxy hy ⟨hs.1,hsy⟩ ⟨hy.le,le_rfl⟩
  · exact bipodalOmega_high_pos hx hxy hy ⟨(lt_of_not_ge hsy).le,hs.2⟩ ⟨hy.le,le_rfl⟩

end SparseLowerTail.Section04

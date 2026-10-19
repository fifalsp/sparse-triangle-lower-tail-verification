import SparseLowerTail.Section05.CriticalEnclosureBounds

/-! Certified endpoint confinement for the critical mean interval. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Section02 Section04 Numerics

private theorem endpointLog0 : Bounds (Real.log (131/625:ℝ)) (-1563/1000) (-1562/1000) := by
  have hh := log_taylor_bounds (x := (101/625:ℝ)) (by norm_num) 15
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (524/625:ℝ)=2*Real.log 2+Real.log (131/625:ℝ) := by
    rw [show (524/625:ℝ)=(2:ℝ)^2*(131/625:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

private theorem endpointLog1 : Bounds (Real.log (2097/10000:ℝ)) (-1563/1000) (-1562/1000) := by
  have hh := log_taylor_bounds (x := (403/2500:ℝ)) (by norm_num) 15
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2097/2500:ℝ)=2*Real.log 2+Real.log (2097/10000:ℝ) := by
    rw [show (2097/2500:ℝ)=(2:ℝ)^2*(2097/10000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

theorem threshold_log_coarse : Bounds (Real.log threshold) (-1563/1000) (-1562/1000) := by
  apply Bounds.log_of_endpoints (l := 2096/10000) (u := 2097/10000)
  · constructor <;> linarith [threshold_digits.1,threshold_digits.2]
  · norm_num
  · convert endpointLog0.1 using 1; norm_num
  · exact endpointLog1.2

/-- The true isolation endpoint is to the right of .2182. -/
theorem criticalMeanLower_ge_2182 : (2182/10000:ℝ)≤criticalMeanLower := by
  have hr := threshold_digits
  have hl := threshold_log_coarse
  have hb : (1235/1000:ℝ)≤beta threshold := by
    have hh := beta_interval_lower (lo := (2096696762/10^10:ℝ)) (hi := threshold)
      (by norm_num) threshold_mem_Ioo.2 ⟨hr.1,le_rfl⟩ hl.2 (by norm_num)
    exact (by norm_num : (1235/1000:ℝ)≤
      ((2096696762/10^10:ℝ)-1-(-1562/1000))/(1-(2096696762/10^10:ℝ))^2).trans hh
  have hb0 : 0≤beta threshold := le_trans (by norm_num) hb
  have hn : 9*(1235/1000:ℝ)^3*(2096696762/10^10:ℝ)^4≤9*(beta threshold)^3*threshold^4 := by
    gcongr
    exact hr.1
  have hden : (-Real.log threshold)^3≤(1563/1000:ℝ)^3 := by
    apply pow_le_pow_left₀
    · linarith [hl.2]
    · linarith [hl.1]
  have hden0 : 0<(-Real.log threshold)^3 := by
    have hh : 0< -Real.log threshold := by linarith [hl.2]
    positivity
  have hratio := div_le_div₀ (by positivity : 0≤9*(beta threshold)^3*threshold^4) hn hden0 hden
  have hnum : (2182/10000:ℝ)≤(2096696762/10^10:ℝ)+
      9*(1235/1000:ℝ)^3*(2096696762/10^10:ℝ)^4/(1563/1000:ℝ)^3 := by norm_num
  unfold criticalMeanLower isolatedMean
  linarith [hr.1]

/-- The true Goodman endpoint lies below .5095. -/
theorem criticalMeanUpper_le_5095 : criticalMeanUpper≤(5095/10000:ℝ) := by
  have ht := criticalTriangle_sharp_bounds
  have ht0 : 0≤criticalTriangle := le_trans (by norm_num) ht.1
  have hs := Real.sq_sqrt (show 0≤1+8*criticalTriangle by positivity)
  have hsn := Real.sqrt_nonneg (1+8*criticalTriangle)
  unfold criticalMeanUpper
  nlinarith [ht.2]

end SparseLowerTail.Section05.CoverGeometry

import SparseLowerTail.Section02.TriangleL2

/-! Quantitative isolation and the edge--triangle entropy lower bound in Section 2. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section02

/-- The actual L² distance from a constant. -/
def l2Deviation (U : Graphon) (s : ℝ) : ℝ := Real.sqrt (squareDeviation U s)

theorem l2Deviation_nonneg (U : Graphon) (s : ℝ) : 0 ≤ l2Deviation U s := Real.sqrt_nonneg _

theorem l2Deviation_sq (U : Graphon) (s : ℝ) : (l2Deviation U s)^2 = squareDeviation U s :=
  Real.sq_sqrt (squareDeviation_nonneg U s)

theorem l2Deviation_pos {U : Graphon} {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1)
    (hn : ¬IsConstant U s) : 0 < l2Deviation U s := by
  apply Real.sqrt_pos.mpr
  exact lt_of_le_of_ne (squareDeviation_nonneg U s)
    (fun he => hn ((squareDeviation_eq_zero_iff U hs).mp he.symm))

theorem abs_centeredTriangle_le (U : Graphon) (s : ℝ) :
    |signedTriangle (centeredKernel U s)| ≤ (l2Deviation U s)^3 :=
  abs_signedTriangle_le (centered_bounded U s)

/-- The triangle constraint bounds the mean excess by the cubic L² distance. -/
theorem mean_excess_le_cube {U : Graphon} {r : ℝ} (hr : 0 ≤ r) (hf : Feasible r U) :
    3*r^2*(edgeDensity U-r) ≤ (l2Deviation U r)^3 := by
  have he := triangle_centered_expansion U r
  have ht := abs_centeredTriangle_le U r
  have hneg := neg_le_abs (signedTriangle (centeredKernel U r))
  have hdeg := mul_nonneg hr (degreeEnergy_nonneg U r)
  change triangle U ≤ r^3 at hf
  nlinarith

/-- M(r) from manuscript eq:Mr. -/
def isolatedMean (r : ℝ) : ℝ := r+9*(beta r)^3*r^4/(-Real.log r)^3

theorem isolatedMean_gt {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) : r < isolatedMean r := by
  have hb : 0 < beta r := lt_of_lt_of_le (by norm_num) (beta_ge_half hr)
  have hL : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr.1 hr.2)
  unfold isolatedMean
  have hp : 0 < 9*(beta r)^3*r^4/(-Real.log r)^3 :=
    div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hb _)) (pow_pos hr.1 _)) (pow_pos hL _)
  linarith

/-- Continuity of the isolation coefficient on its natural open domain. -/
theorem continuousAt_beta {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) : ContinuousAt beta r := by
  have hr0 : r ≠ 0 := hr.1.ne'
  have hd : (1-r)^2 ≠ 0 := pow_ne_zero 2 (by linarith [hr.2])
  unfold beta
  fun_prop (disch := aesop)

/-- The mean separation function is continuous, as asserted after eq:Mr. -/
theorem continuousOn_isolatedMean : ContinuousOn isolatedMean (Ioo (0:ℝ) 1) := by
  intro r hr
  apply ContinuousAt.continuousWithinAt
  have hb := continuousAt_beta hr
  have hr0 : r ≠ 0 := hr.1.ne'
  have hlog : -Real.log r ≠ 0 := (neg_pos.mpr (Real.log_neg hr.1 hr.2)).ne'
  have hd : (-Real.log r)^3 ≠ 0 := pow_ne_zero 3 hlog
  unfold isolatedMean
  fun_prop (disch := aesop)

/-- Full manuscript lem:isolation, including both the norm and mean bounds. -/
theorem isolation {U : Graphon} {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1)
    (hf : Feasible r U) (hc : cost U ≤ entropy r) (hn : ¬IsConstant U r) :
    3*beta r*r^2/(-Real.log r) ≤ l2Deviation U r ∧ isolatedMean r ≤ edgeDensity U := by
  let L := -Real.log r
  let z := l2Deviation U r
  have hL : 0 < L := neg_pos.mpr (Real.log_neg hr.1 hr.2)
  have hz : 0 < z := l2Deviation_pos ⟨hr.1.le,hr.2.le⟩ hn
  have hb : 0 < beta r := lt_of_lt_of_le (by norm_num) (beta_ge_half hr)
  have hbreg := graphon_bregman U hr
  rw [← l2Deviation_sq] at hbreg
  have hmean : beta r*z^2 ≤ L*(edgeDensity U-r) := by dsimp [L,z]; nlinarith
  have htri := mean_excess_le_cube hr.1.le hf
  change 3*r^2*(edgeDensity U-r) ≤ z^3 at htri
  have hprod : (3*beta r*r^2)*z^2 ≤ (L*z)*z^2 := by
    have h1 := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 3*r^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left htri hL.le
    nlinarith
  have hnorm : 3*beta r*r^2/L ≤ z := by
    apply (div_le_iff₀ hL).mpr
    have h := (mul_le_mul_iff_left₀ (sq_pos_of_pos hz)).mp hprod
    nlinarith
  refine ⟨hnorm, ?_⟩
  have hsquare : (3*beta r*r^2/L)^2 ≤ z^2 :=
    (sq_le_sq₀ (by positivity) hz.le).mpr hnorm
  have hbound : 9*(beta r)^3*r^4/L^3 ≤ edgeDensity U-r := by
    calc
      _ = beta r*(3*beta r*r^2/L)^2/L := by field_simp; ring
      _ ≤ beta r*z^2/L := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hb.le) hL.le
      _ ≤ edgeDensity U-r := (div_le_iff₀ hL).mpr (by nlinarith [hmean])
  change r+9*(beta r)^3*r^4/L^3 ≤ edgeDensity U
  linarith

/-- The centered triangle expansion gives the deficit estimate before taking powers. -/
theorem triangle_deficit_le_cube (U : Graphon) :
    max ((edgeDensity U)^3-triangle U) 0 ≤ (l2Deviation U (edgeDensity U))^3 := by
  have he := triangle_centered_expansion U (edgeDensity U)
  have ht := abs_centeredTriangle_le U (edgeDensity U)
  have hneg := neg_le_abs (signedTriangle (centeredKernel U (edgeDensity U)))
  have hdeg := mul_nonneg (edgeDensity_mem_Icc U).1 (degreeEnergy_nonneg U (edgeDensity U))
  apply max_le
  · nlinarith
  · exact pow_nonneg (l2Deviation_nonneg U _) _

/-- First assertion of manuscript lem:FB1. -/
theorem variance_ge_triangle_deficit (U : Graphon) :
    (max ((edgeDensity U)^3-triangle U) 0)^(2/3:ℝ) ≤ squareDeviation U (edgeDensity U) := by
  have h := Real.rpow_le_rpow (le_max_right _ _) (triangle_deficit_le_cube U) (by norm_num : (0:ℝ)≤2/3)
  have he : ((l2Deviation U (edgeDensity U))^3)^(2/3:ℝ) = (l2Deviation U (edgeDensity U))^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (l2Deviation_nonneg U _)]
    norm_num
  simpa only [he, l2Deviation_sq] using h

/-- Full cost inequality of manuscript lem:FB1. -/
theorem cost_ge_entropy_triangle_deficit {U : Graphon}
    (hm : edgeDensity U ∈ Ioo (0:ℝ) 1) :
    entropy (edgeDensity U)+beta (edgeDensity U)*
      (max ((edgeDensity U)^3-triangle U) 0)^(2/3:ℝ) ≤ cost U := by
  have hvar := variance_ge_triangle_deficit U
  have hb : 0 ≤ beta (edgeDensity U) := le_trans (by norm_num) (beta_ge_half hm)
  have hg := graphon_mean_bregman U hm
  have h := mul_le_mul_of_nonneg_left hvar hb
  linarith

end SparseLowerTail.Section02

import SparseLowerTail.Section07.PenalizedUpper

/-! The analytic bounds in `lem:smallparams(a)`, uniformly on the entire
small-parameter interval. Endpoint logarithm bounds are kernel checked. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04 Numerics

theorem small_branchLog_lower {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    (93/10:ℝ)<branchLog z := by
  have hl := Real.log_le_log hz hzZ
  have he := smallUpper_log.1
  rw [branchLog_eq_neg_log]
  norm_num only [smallParameterUpper] at hl
  linarith

theorem small_log_moments {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    Bounds (z*branchLog z) 0 (smallParameterUpper*(47/5)) ∧
    Bounds (z*(branchLog z)^2) 0 (smallParameterUpper*(47/5)^2) := by
  have hd (x : ℝ) (hx : 0<x) : HasDerivAt branchLog (-x⁻¹) x := by
    have he : branchLog=(fun t : ℝ => -Real.log t) := funext branchLog_eq_neg_log
    rw [he]
    exact (Real.hasDerivAt_log hx.ne').neg
  have hd1 (x : ℝ) (hx : 0<x) :
      HasDerivAt (fun t => t*branchLog t) (branchLog x-1) x := by
    convert (hasDerivAt_id x).mul (hd x hx) using 1
    simp only [id_eq]
    field_simp
    ring
  have hd2 (x : ℝ) (hx : 0<x) :
      HasDerivAt (fun t => t*(branchLog t)^2) ((branchLog x)^2-2*branchLog x) x := by
    convert (hasDerivAt_id x).mul ((hd x hx).pow 2) using 1
    simp only [id_eq,Pi.pow_apply]
    field_simp
    ring
  have hm1 : MonotoneOn (fun t => t*branchLog t) (Ioc (0:ℝ) smallParameterUpper) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · intro x hx; exact (hd1 x hx.1).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ioc] at hx; exact (hd1 x hx.1).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ioc] at hx; rw [(hd1 x hx.1).deriv]
      linarith [small_branchLog_lower hx.1 hx.2.le]
  have hm2 : MonotoneOn (fun t => t*(branchLog t)^2) (Ioc (0:ℝ) smallParameterUpper) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · intro x hx; exact (hd2 x hx.1).continuousAt.continuousWithinAt
    · intro x hx; rw [interior_Ioc] at hx; exact (hd2 x hx.1).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Ioc] at hx; rw [(hd2 x hx.1).deriv]
      nlinarith [small_branchLog_lower hx.1 hx.2.le]
  have hZ : smallParameterUpper∈Ioc (0:ℝ) smallParameterUpper := by norm_num [smallParameterUpper]
  have h1 := hm1 ⟨hz,hzZ⟩ hZ hzZ
  have h2 := hm2 ⟨hz,hzZ⟩ hZ hzZ
  have hL : 0≤branchLog z := by linarith [small_branchLog_lower hz hzZ]
  have hLZ : 0≤branchLog smallParameterUpper := by linarith [small_branchLog_lower hZ.1 hZ.2]
  have hLu : branchLog smallParameterUpper≤(47/5:ℝ) := by
    rw [branchLog_eq_neg_log]
    have h := smallUpper_log.2
    norm_num only [smallParameterUpper]
    linarith
  exact ⟨⟨mul_nonneg hz.le hL,h1.trans (mul_le_mul_of_nonneg_left hLu hZ.1.le)⟩,
    ⟨mul_nonneg hz.le (sq_nonneg _),h2.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hLZ hLu 2) hZ.1.le)⟩⟩

def branchDelta (z : ℝ) : ℝ := 2*z*branchLog z/(1-z)^2

theorem small_branchDelta_bounds {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    z≤branchDelta z ∧ branchDelta z≤(1/625:ℝ) := by
  have hz1 : z<1 := lt_of_le_of_lt hzZ (by norm_num [smallParameterUpper])
  have hL := small_branchLog_lower hz hzZ
  have hd : 0<(1-z)^2 := sq_pos_of_pos (sub_pos.mpr hz1)
  constructor
  · rw [branchDelta,le_div_iff₀ hd]
    have hden : (1-z)^2≤1 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hden hz.le
    nlinarith
  · have hm := (small_log_moments hz hzZ).1
    have hden : Bounds (1-z) (1-smallParameterUpper) 1 := ⟨by linarith,by linarith⟩
    have hh := ((Bounds.refl (2:ℝ)).mul_nonneg hm (by norm_num) (by norm_num)).div_pos
      (hden.pow (by norm_num [smallParameterUpper]) 2) (by norm_num)
      (by norm_num [smallParameterUpper])
    have he : branchDelta z=2*(z*branchLog z)/(1-z)^2 := by unfold branchDelta; ring
    rw [he]
    exact hh.2.trans (by norm_num [smallParameterUpper])

theorem small_branchB_bounds {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    Bounds (branchB z) (624/625) 1 := by
  have hd := small_branchDelta_bounds hz hzZ
  have he : branchB z=Real.exp (-branchDelta z) := by unfold branchB branchDelta; congr 1; ring
  have hh := Real.add_one_le_exp (-branchDelta z)
  rw [←he] at hh
  exact ⟨by linarith, (branchB_lt_one hz (lt_of_le_of_lt hzZ (by norm_num [smallParameterUpper]))).le⟩

theorem small_branch_mean_bounds {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    Bounds ((branchA z+branchB z)/2) (312/625) (1/2) := by
  have hb := small_branchB_bounds hz hzZ
  have hd := small_branchDelta_bounds hz hzZ
  have hz1 : z<1 := lt_of_le_of_lt hzZ (by norm_num [smallParameterUpper])
  have hprod : (1+z)*branchB z≤1 := by
    apply (Real.log_nonpos_iff (mul_nonneg (by linarith) (branchB_pos z).le)).mp
    rw [Real.log_mul (by positivity) (branchB_pos z).ne',log_branchB]
    have hl := Real.log_le_sub_one_of_pos (show 0<1+z by linarith)
    have hd1 := hd.1
    change z≤2*z*branchLog z/(1-z)^2 at hd1
    rw [show -2*z*branchLog z/(1-z)^2 = -(2*z*branchLog z/(1-z)^2) by ring]
    linarith
  constructor
  · unfold branchA; nlinarith [mul_nonneg hz.le (branchB_pos z).le,hb.1]
  · unfold branchA; nlinarith

theorem small_branchMu_lower {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    (93/5:ℝ)≤branchMu z := by
  have hL := small_branchLog_lower hz hzZ
  have hb := small_branchB_bounds hz hzZ
  have hz1 : z<1 := lt_of_le_of_lt hzZ (by norm_num [smallParameterUpper])
  have hd : 0<(1-z)^2*branchB z^2 := mul_pos (sq_pos_of_pos (sub_pos.mpr hz1)) (sq_pos_of_pos (branchB_pos z))
  have hd1 : (1-z)^2≤1 := by nlinarith
  have hb1 : branchB z^2≤1 := by nlinarith [hb.1,hb.2]
  have hdle : (1-z)^2*branchB z^2≤1 := by
    simpa using mul_le_mul hd1 hb1 (sq_nonneg _) (by norm_num : (0:ℝ)≤1)
  rw [branchMu,le_div_iff₀ hd]
  nlinarith

/-- The three expressions containing the unbounded multiplier are first
rewritten in terms of bounded logarithmic moments. -/
theorem small_multiplier_product_identities {z : ℝ} (hz : 0<z) (hz1 : z<1) :
    branchMu z*balancedTriangle (branchA z) (branchB z)=
      (z*branchLog z)*(z^2+3)*branchB z/(2*(1-z)^2) ∧
    (branchMu z)^2*balancedTriangle (branchA z) (branchB z)=
      (z*(branchLog z)^2)*(z^2+3)/((1-z)^4*branchB z) ∧
    branchMu z*branchDelta z/2=
      2*(z*(branchLog z)^2)/((1-z)^4*(branchB z)^2) := by
  have hd : 1-z≠0 := (sub_pos.mpr hz1).ne'
  have hb : branchB z≠0 := (branchB_pos z).ne'
  rw [branch_triangle]
  unfold branchMu branchDelta
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · field_simp

/-- `lem:smallparams(a)`, with no crossing or optimizer hypothesis. -/
theorem small_parameter_bounds {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    Bounds ((branchA z+branchB z)/2) (312/625) (1/2) ∧
    (93/5:ℝ)≤branchMu z ∧
    balancedTriangle (branchA z) (branchB z)≤(63/1000000:ℝ) ∧
    branchMu z*balancedTriangle (branchA z) (branchB z)≤(3/2500:ℝ) ∧
    (branchMu z)^2*balancedTriangle (branchA z) (branchB z)≤(23/1000:ℝ) ∧
    branchMu z*((1/2:ℝ)-(branchA z+branchB z)/2)≤(31/2000:ℝ) := by
  have hz1 : z<1 := lt_of_le_of_lt hzZ (by norm_num [smallParameterUpper])
  have hb := small_branchB_bounds hz hzZ
  have hzB : Bounds z 0 smallParameterUpper := ⟨hz.le,hzZ⟩
  have hd : Bounds (1-z) (1-smallParameterUpper) 1 := ⟨by linarith,by linarith⟩
  have hd2 := hd.pow (by norm_num [smallParameterUpper]) 2
  have hd4 := hd.pow (by norm_num [smallParameterUpper]) 4
  have hpol := (hzB.pow (by norm_num) 2).add (Bounds.refl (3:ℝ))
  have hm := small_log_moments hz hzZ
  have ht := (((hb.pow (by norm_num) 3).mul_nonneg hzB (by norm_num) (by norm_num)).mul_nonneg
    hpol (by norm_num) (by norm_num)).div_pos (Bounds.refl (4:ℝ)) (by norm_num) (by norm_num)
  have he := small_multiplier_product_identities hz hz1
  refine ⟨small_branch_mean_bounds hz hzZ,small_branchMu_lower hz hzZ,?_,?_,?_,?_⟩
  · have hid : balancedTriangle (branchA z) (branchB z)=branchB z^3*z*(z^2+3)/4 := by
      rw [branch_triangle]; ring
    rw [hid]
    exact ht.2.trans (by norm_num [smallParameterUpper])
  · rw [he.1]
    have h := (((hm.1.mul_nonneg hpol (by norm_num) (by norm_num)).mul_nonneg hb
      (by norm_num [smallParameterUpper]) (by norm_num))).div_pos
      ((Bounds.refl (2:ℝ)).mul_nonneg hd2 (by norm_num) (by positivity))
      (by norm_num) (by norm_num [smallParameterUpper])
    exact h.2.trans (by norm_num [smallParameterUpper])
  · rw [he.2.1]
    have h := (hm.2.mul_nonneg hpol (by norm_num) (by norm_num)).div_pos
      (hd4.mul_nonneg hb (by positivity) (by norm_num))
      (by norm_num) (by norm_num [smallParameterUpper])
    exact h.2.trans (by norm_num [smallParameterUpper])
  · have hgap : (1/2:ℝ)-(branchA z+branchB z)/2≤branchDelta z/2 := by
      have hh := Real.add_one_le_exp (-branchDelta z)
      have heB : Real.exp (-branchDelta z)=branchB z := by unfold branchB branchDelta; congr 1; ring
      rw [heB] at hh
      have ha := branchA_pos hz
      linarith
    have hfirst := mul_le_mul_of_nonneg_left hgap (branchMu_pos hz hz1).le
    have h := ((Bounds.refl (2:ℝ)).mul_nonneg hm.2 (by norm_num) (by norm_num)).div_pos
      (hd4.mul_nonneg (hb.pow (by norm_num) 2) (by positivity) (by norm_num))
      (by norm_num) (by norm_num [smallParameterUpper])
    have hlast : branchMu z*branchDelta z/2≤(31/2000:ℝ) := by
      rw [he.2.2]
      exact h.2.trans (by norm_num [smallParameterUpper])
    nlinarith

/-- The same bounds in the manuscript's notation `t = ρ(z)^3`. -/
theorem small_parameter_rho_bounds {z : ℝ} (hz : 0<z) (hzZ : z≤smallParameterUpper) :
    Bounds ((branchA z+branchB z)/2) (312/625) (1/2) ∧
    (93/5:ℝ)≤branchMu z ∧
    (branchRho z)^3≤(63/1000000:ℝ) ∧
    branchMu z*(branchRho z)^3≤(3/2500:ℝ) ∧
    (branchMu z)^2*(branchRho z)^3≤(23/1000:ℝ) ∧
    branchMu z*((1/2:ℝ)-(branchA z+branchB z)/2)≤(31/2000:ℝ) := by
  simpa only [branch_triangle_eq_rho_cube hz] using small_parameter_bounds hz hzZ

end SparseLowerTail.Section07

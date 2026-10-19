import SparseLowerTail.Section07.PenalizedGap

/-! The scalar fold function in `lem:fold`. Polynomial positivity uses a
sqrt-free version of the manuscript's quadratic-root estimates. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

def foldQ (z : ℝ) : ℝ := 2*z*(1+z)*branchLog z*(2*branchLog z-1+z)/(1-z)^3

def foldPolynomial (z L : ℝ) : ℝ :=
  2*(1+4*z+z^2)*L^2-(1-z)*(5+7*z)*L+(1-z)^2*(1+z)

/-- A strict rational lower bound for −log z on (0,1). -/
theorem branchLog_gt_rational {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    2*(1-z)/(1+z) < branchLog z := by
  let f : ℝ → ℝ := fun x => -Real.log x-2*(1-x)/(1+x)
  have hd : ∀ x ∈ Ioc (0:ℝ) 1,
      HasDerivAt f (-(1-x)^2/(x*(1+x)^2)) x := by
    intro x hx
    have hx0 := hx.1
    have h := ((Real.hasDerivAt_log (ne_of_gt hx0)).neg).sub
      ((((hasDerivAt_id x).const_sub 1).const_mul 2).div
        ((hasDerivAt_id x).const_add 1) (by dsimp; positivity))
    convert h using 1
    dsimp
    field_simp
    ring
  have hant : StrictAntiOn f (Ioc (0:ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hd x ⟨hx.1,hx.2.le⟩).deriv]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos (sub_pos.mpr hx.2)))
        (mul_pos hx.1 (sq_pos_of_pos (by linarith [hx.1])))
  have hh := hant ⟨hz.1,hz.2.le⟩ (by norm_num) hz.2
  simpa [f,branchLog_eq_neg_log,sub_pos] using hh

theorem log_ten_gt : (229/100:ℝ) < Real.log 10 := by
  have h := branchLog_gt_rational (by norm_num : (4/5:ℝ) ∈ Ioo 0 1)
  norm_num [branchLog] at h
  have he : Real.log (10:ℝ)=3*Real.log 2+Real.log (5/4:ℝ) := by
    rw [show (10:ℝ)=2^3*(5/4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

theorem foldPolynomial_pos {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    0 < foldPolynomial z (branchLog z) := by
  let L := branchLog z
  have hz0 := hz.1
  have hz1 := hz.2
  by_cases hzsmall : z ≤ 1/10
  · have hL : (229/100:ℝ) < L := by
      have hlog := Real.log_le_log hz.1 hzsmall
      have he : Real.log (1/10:ℝ) = -Real.log 10 := by rw [Real.log_div (by norm_num) (by norm_num)]; norm_num
      rw [he] at hlog
      dsimp [L]
      rw [branchLog_eq_neg_log]
      linarith [log_ten_gt]
    have h0 : 0 < 2*L^2-5*L+1 := by nlinarith
    have h1 : 0 < 8*L^2-2*L-1 := by nlinarith
    have h2 : 0 < 2*L^2+7*L-1 := by nlinarith
    have hid : foldPolynomial z L = (2*L^2-5*L+1)+
        z*(8*L^2-2*L-1)+z^2*(2*L^2+7*L-1)+z^3 := by unfold foldPolynomial; ring
    rw [hid]
    positivity
  · have hzlarge : 1/10 ≤ z := (lt_of_not_ge hzsmall).le
    let l : ℝ := 2*(1-z)/(1+z)
    have hL : l < L := branchLog_gt_rational hz
    have hl : 0 < l := div_pos (by linarith) (by linarith)
    have hcubic : 0 < z^3-3*z^2+11*z-1 := by
      have hh : 0 ≤ (z-1/10)*((z-1)^2+8) := mul_nonneg (by linarith) (by positivity)
      nlinarith [sq_nonneg (z-1/10)]
    have hpbase : foldPolynomial z l = (1-z)^2/(1+z)^2*(z^3-3*z^2+11*z-1) := by
      unfold foldPolynomial l
      field_simp
      ring
    have hp : 0 < foldPolynomial z l := by
      rw [hpbase]
      exact mul_pos (div_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos (by linarith))) hcubic
    have hslope : 0 < 4*(1+4*z+z^2)*l-(1-z)*(5+7*z) := by
      have he : 4*(1+4*z+z^2)*l-(1-z)*(5+7*z) =
          (1-z)/(1+z)*(3+20*z+z^2) := by unfold l; field_simp; ring
      rw [he]
      exact mul_pos (div_pos (sub_pos.mpr hz1) (by linarith)) (by positivity)
    have hid : foldPolynomial z L-foldPolynomial z l =
        (L-l)*(4*(1+4*z+z^2)*l-(1-z)*(5+7*z))+
          2*(1+4*z+z^2)*(L-l)^2 := by unfold foldPolynomial; ring
    have hm : 0 < (L-l)*(4*(1+4*z+z^2)*l-(1-z)*(5+7*z)) :=
      mul_pos (sub_pos.mpr hL) hslope
    have hn : 0 ≤ 2*(1+4*z+z^2)*(L-l)^2 := by positivity
    linarith

theorem foldQ_pos {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) : 0 < foldQ z := by
  have hz0 := hz.1
  have hz1 := hz.2
  have hL := branchLog_gt_rational hz
  have hLpos := branchLog_pos hz.1 hz.2
  have hLbound : 1-z < branchLog z := by
    have hrat : 1-z ≤ 2*(1-z)/(1+z) := by
      apply (le_div_iff₀ (by linarith : 0<1+z)).mpr
      nlinarith
    exact hrat.trans_lt hL
  unfold foldQ
  apply div_pos
  · exact mul_pos (by positivity) (by linarith)
  · exact pow_pos (sub_pos.mpr hz1) 3

theorem hasDerivAt_branchLog {z : ℝ} (hz : 0 < z) :
    HasDerivAt branchLog (-1/z) z := by
  have he : branchLog = fun x => -Real.log x := funext branchLog_eq_neg_log
  rw [he]
  convert (Real.hasDerivAt_log (ne_of_gt hz)).neg using 1
  simp [div_eq_mul_inv]

theorem hasDerivAt_foldQ {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    HasDerivAt foldQ (foldQ z*foldPolynomial z (branchLog z)/
      (z*(1-z^2)*branchLog z*(2*branchLog z-1+z))) z := by
  have hL := hasDerivAt_branchLog hz.1
  have hA := ((hL.const_mul 2).sub_const 1).add (hasDerivAt_id z)
  have hnum := ((((hasDerivAt_id z).const_mul 2).mul
    ((hasDerivAt_id z).const_add 1)).mul hL).mul hA
  have h := hnum.div (((hasDerivAt_id z).const_sub 1).pow 3)
    (by dsimp; exact pow_ne_zero 3 (ne_of_gt (sub_pos.mpr hz.2)))
  have hz0 : z ≠ 0 := ne_of_gt hz.1
  have h1 : 1-z ≠ 0 := ne_of_gt (sub_pos.mpr hz.2)
  have h2 : 1-z^2 ≠ 0 := by nlinarith [hz.1,hz.2]
  have hLp := branchLog_pos hz.1 hz.2
  have hLn : branchLog z ≠ 0 := ne_of_gt hLp
  have hAp : 0 < 2*branchLog z-1+z := by
    have hb := branchLog_gt_rational hz
    have hh : 1-z < branchLog z := lt_trans (by
      apply (lt_div_iff₀ (by linarith [hz.1] : 0<1+z)).mpr
      nlinarith [hz.1,hz.2]) hb
    linarith [hz.2]
  convert h using 1
  dsimp
  unfold foldQ foldPolynomial
  field_simp [hz0,h1,h2,hLn,ne_of_gt hAp]
  ring

theorem strictMonoOn_foldQ : StrictMonoOn foldQ (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro z hz
    exact (hasDerivAt_foldQ hz).continuousAt.continuousWithinAt
  · intro z hz
    have hi := interior_subset hz
    rw [(hasDerivAt_foldQ hi).deriv]
    have hLp := branchLog_pos hi.1 hi.2
    have hAp : 0 < 2*branchLog z-1+z := by
      have hh := branchLog_gt_rational hi
      have hrat : 1-z ≤ 2*(1-z)/(1+z) := by
        apply (le_div_iff₀ (by linarith [hi.1] : 0<1+z)).mpr
        nlinarith [hi.1,hi.2]
      linarith [hi.2]
    exact div_pos (mul_pos (foldQ_pos hi) (foldPolynomial_pos hi))
      (mul_pos (mul_pos (mul_pos hi.1 (by nlinarith [hi.1,hi.2])) hLp) hAp)

theorem foldQ_milli_lt_one : foldQ (1/1000:ℝ) < 1 := by
  have hL : branchLog (1/1000:ℝ) < 7 := by
    have hh := Real.log_lt_log (by norm_num : (0:ℝ)<1000)
      (by norm_num : (1000:ℝ)<2^10)
    rw [Real.log_pow] at hh
    norm_num [branchLog]
    norm_num at hh
    linarith [Real.log_two_lt_d9]
  have hp := branchLog_pos (by norm_num : (0:ℝ)<1/1000) (by norm_num : (1/1000:ℝ)<1)
  unfold foldQ
  norm_num only
  nlinarith [sq_nonneg (7-branchLog (1/1000:ℝ))]

theorem foldQ_fiftieth_gt_one : 1 < foldQ (1/50:ℝ) := by
  have hb := branchLog_gt_rational (by norm_num : (4/5:ℝ) ∈ Ioo 0 1)
  norm_num [branchLog] at hb
  have he : Real.log (50:ℝ)=5*Real.log 2+2*Real.log (5/4:ℝ) := by
    rw [show (50:ℝ)=2^5*(5/4)^2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
    norm_num
  have hL : (39/10:ℝ) < branchLog (1/50:ℝ) := by
    norm_num [branchLog]
    rw [he]
    linarith [Real.log_two_gt_d9]
  unfold foldQ
  norm_num only
  nlinarith [sq_nonneg (branchLog (1/50:ℝ)-39/10)]

theorem exists_unique_foldPoint :
    ∃! z, z ∈ Ioo (0:ℝ) 1 ∧ foldQ z=1 := by
  have hc : ContinuousOn foldQ (Icc (1/1000:ℝ) (1/50)) := by
    intro z hz
    exact (hasDerivAt_foldQ ⟨by linarith [hz.1],by linarith [hz.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc (by norm_num : (1/1000:ℝ)≤1/50) hc
    ⟨foldQ_milli_lt_one.le,foldQ_fiftieth_gt_one.le⟩
  have hz01 : z ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  refine ⟨z,⟨hz01,he⟩,?_⟩
  intro y hy
  exact strictMonoOn_foldQ.injOn hy.1 hz01 (hy.2.trans he.symm)

/-- The unique fold z_m, constructed from Q rather than assumed. -/
def foldPoint : ℝ := Classical.choose exists_unique_foldPoint

theorem foldPoint_spec : foldPoint ∈ Ioo (0:ℝ) 1 ∧ foldQ foldPoint=1 :=
  (Classical.choose_spec exists_unique_foldPoint).1

theorem foldPoint_bounds : (1/1000:ℝ)<foldPoint ∧ foldPoint<1/50 := by
  constructor
  · exact (strictMonoOn_foldQ.lt_iff_lt (by norm_num : (1/1000:ℝ)∈Ioo 0 1)
      foldPoint_spec.1).mp (by rw [foldPoint_spec.2]; exact foldQ_milli_lt_one)
  · exact (strictMonoOn_foldQ.lt_iff_lt foldPoint_spec.1
      (by norm_num : (1/50:ℝ)∈Ioo 0 1)).mp
      (by rw [foldPoint_spec.2]; exact foldQ_fiftieth_gt_one)

private def logMuExpression (z : ℝ) : ℝ :=
  Real.log 2+Real.log (branchLog z)-2*Real.log (1-z)+4*z*branchLog z/(1-z)^2

private theorem logMuExpression_eq {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    Real.log (branchMu z)=logMuExpression z := by
  have hL := ne_of_gt (branchLog_pos hz.1 hz.2)
  have h1 := ne_of_gt (sub_pos.mpr hz.2)
  have hb := ne_of_gt (branchB_pos z)
  rw [branchMu,Real.log_div (mul_ne_zero (by norm_num) hL)
    (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ hb)),
    Real.log_mul (by norm_num) hL,
    Real.log_mul (pow_ne_zero _ h1) (pow_ne_zero _ hb),
    Real.log_pow,Real.log_pow,branchB,Real.log_exp]
  unfold logMuExpression
  ring

/-- Exact logarithmic derivative in `lem:fold`(b). -/
theorem hasDerivAt_log_branchMu {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun x => Real.log (branchMu x)) ((foldQ z-1)/(z*branchLog z)) z := by
  have hL := hasDerivAt_branchLog hz.1
  have h1 := (hasDerivAt_id z).const_sub 1
  have h := (((hL.log (ne_of_gt (branchLog_pos hz.1 hz.2))).const_add (Real.log 2)).sub
    ((h1.log (ne_of_gt (sub_pos.mpr hz.2))).const_mul 2)).add
    ((((hasDerivAt_id z).const_mul 4).mul hL).div (h1.pow 2)
      (by dsimp; exact pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hz.2))))
  have hd : HasDerivAt logMuExpression ((foldQ z-1)/(z*branchLog z)) z := by
    convert h using 1
    dsimp
    unfold foldQ
    have hnz := ne_of_gt hz.1
    have hnL := ne_of_gt (branchLog_pos hz.1 hz.2)
    have hn1 := ne_of_gt (sub_pos.mpr hz.2)
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hz] with x hx
  exact logMuExpression_eq hx

theorem hasDerivAt_branchMu {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    HasDerivAt branchMu (branchMu z*(foldQ z-1)/(z*branchLog z)) z := by
  have h := (hasDerivAt_log_branchMu hz).exp
  rw [Real.exp_log (branchMu_pos hz.1 hz.2)] at h
  have h' : HasDerivAt (fun x => Real.exp (Real.log (branchMu x)))
      (branchMu z*(foldQ z-1)/(z*branchLog z)) z := by convert h using 1; ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hz] with x hx
  exact (Real.exp_log (branchMu_pos hx.1 hx.2)).symm

theorem deriv_branchMu_neg {z : ℝ} (hz : z ∈ Ioo (0:ℝ) foldPoint) :
    deriv branchMu z < 0 := by
  have hz01 : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1,hz.2.trans foldPoint_spec.1.2⟩
  rw [(hasDerivAt_branchMu hz01).deriv]
  have hq := strictMonoOn_foldQ hz01 foldPoint_spec.1 hz.2
  rw [foldPoint_spec.2] at hq
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (branchMu_pos hz01.1 hz01.2)
    (sub_neg.mpr hq)) (mul_pos hz.1 (branchLog_pos hz01.1 hz01.2))

theorem deriv_branchMu_pos {z : ℝ} (hz : z ∈ Ioo foldPoint (1:ℝ)) :
    0 < deriv branchMu z := by
  have hz01 : z ∈ Ioo (0:ℝ) 1 := ⟨foldPoint_spec.1.1.trans hz.1,hz.2⟩
  rw [(hasDerivAt_branchMu hz01).deriv]
  have hq := strictMonoOn_foldQ foldPoint_spec.1 hz01 hz.1
  rw [foldPoint_spec.2] at hq
  exact div_pos (mul_pos (branchMu_pos hz01.1 hz01.2) (sub_pos.mpr hq))
    (mul_pos hz01.1 (branchLog_pos hz01.1 hz01.2))

theorem strictAntiOn_branchMu_left : StrictAntiOn branchMu (Ioc (0:ℝ) foldPoint) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 foldPoint)
  · intro z hz
    exact (hasDerivAt_branchMu ⟨hz.1,hz.2.trans_lt foldPoint_spec.1.2⟩).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    exact deriv_branchMu_neg hz

theorem strictMonoOn_branchMu_right : StrictMonoOn branchMu (Ico foldPoint (1:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico foldPoint 1)
  · intro z hz
    exact (hasDerivAt_branchMu ⟨foldPoint_spec.1.1.trans_le hz.1,hz.2⟩).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ico] at hz
    exact deriv_branchMu_pos hz

/-- Determinant of the explicit scalar Hessian displayed in `lem:fold`(c). -/
def penalizedHessianDet (γ a b : ℝ) : ℝ :=
  ((1/a+3*γ*a)/2)*((1/b+3*γ*a)/2)-(3*γ*b/2)^2

/-- The exact fold/Hessian algebraic identity. -/
theorem penalizedHessianDet_branch {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    penalizedHessianDet (branchMu z/3) (branchA z) (branchB z) =
      (1-foldQ z)/(4*z*(branchB z)^2) := by
  have hz0 := ne_of_gt hz.1
  have hb0 := ne_of_gt (branchB_pos z)
  have h10 := ne_of_gt (sub_pos.mpr hz.2)
  unfold penalizedHessianDet branchA branchMu foldQ
  field_simp
  ring

end SparseLowerTail.Section07

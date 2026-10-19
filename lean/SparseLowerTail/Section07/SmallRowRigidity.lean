import SparseLowerTail.Section06.RowRigidity
import SparseLowerTail.Section07.SmallRigidityCoercivity
import SparseLowerTail.Section07.ApproximateEuler

/-! Small-tail row rigidity from the actual Euler equations. Strong monotonicity
of log replaces the manuscript's interpolation of insertion functionals. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04 Section06

private theorem observable_abs {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    BoundedObservable unitMeasure (fun x => |f x|) := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨?_,C,hC,?_⟩
  · simpa only [Real.norm_eq_abs] using hf.measurable.norm
  · simpa only [Real.norm_eq_abs,abs_abs] using hb

/-- A nonnegative kernel dominated by W has Q_U(f)≥−Q_W(|f|). -/
theorem rowQuadratic_lower_envelope {U W : Graphon}
    (hdom : ∀ᵐ p ∂squareMeasure, U p≤W p) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    -rowQuadratic W (fun x => |f x|)≤rowQuadratic U f := by
  have ha := observable_abs hf
  have hiU := (((hf.comp Measure.quasiMeasurePreserving_fst).mul (graphon_boundedObservable U)).mul
    (hf.comp Measure.quasiMeasurePreserving_snd)).integrable
  have hiW := (((ha.comp Measure.quasiMeasurePreserving_fst).mul (graphon_boundedObservable W)).mul
    (ha.comp Measure.quasiMeasurePreserving_snd)).integrable
  unfold rowQuadratic
  rw [← integral_neg]
  apply integral_mono_ae hiW.neg hiU
  filter_upwards [hdom,U.bounded] with p hp hU
  change -(|f p.1| *W p*|f p.2|)≤f p.1*U p*f p.2
  have hh := neg_abs_le (f p.1*U p*f p.2)
  rw [abs_mul,abs_mul,abs_of_nonneg hU.1] at hh
  have hd := mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg (f p.1)) (abs_nonneg (f p.2)))
  nlinarith

/-- The actual signed quadratic form under a small same-block envelope. -/
theorem rowQuadratic_lower_blockcap {P : Set ℝ} (hP : MeasurableSet P)
    {a : ℝ} (ha : a∈Icc (0:ℝ) 1) {U : Graphon}
    (hdom : ∀ᵐ p ∂squareMeasure, U p≤twoBlock P hP a 1 ha (by norm_num) p)
    {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    let p := unitMeasure.real P
    let q := unitMeasure.real Pᶜ
    let R := ∫ x in P, f x^2 ∂unitMeasure
    let T := ∫ x in Pᶜ, f x^2 ∂unitMeasure;
    -a*p*R-2*Real.sqrt (p*q)*Real.sqrt R*Real.sqrt T-a*q*T≤rowQuadratic U f := by
  dsimp only
  let X := ∫ x in P, |f x| ∂unitMeasure
  let Y := ∫ x in Pᶜ, |f x| ∂unitMeasure
  let R := ∫ x in P, f x^2 ∂unitMeasure
  let T := ∫ x in Pᶜ, f x^2 ∂unitMeasure
  let p := unitMeasure.real P
  let q := unitMeasure.real Pᶜ
  have hp : 0≤p := measureReal_nonneg
  have hq : 0≤q := measureReal_nonneg
  have hR : 0≤R := integral_nonneg fun _ => sq_nonneg _
  have hT : 0≤T := integral_nonneg fun _ => sq_nonneg _
  have hX : 0≤X := integral_nonneg fun _ => abs_nonneg _
  have hY : 0≤Y := integral_nonneg fun _ => abs_nonneg _
  have hXsq : X^2≤p*R := by
    simpa only [sq_abs] using block_integral_sq_le (observable_abs hf) P
  have hYsq : Y^2≤q*T := by
    simpa only [sq_abs] using block_integral_sq_le (observable_abs hf) Pᶜ
  have hXbound : X≤Real.sqrt p*Real.sqrt R := by
    rw [← Real.sqrt_mul hp]
    exact (Real.le_sqrt hX (mul_nonneg hp hR)).mpr hXsq
  have hYbound : Y≤Real.sqrt q*Real.sqrt T := by
    rw [← Real.sqrt_mul hq]
    exact (Real.le_sqrt hY (mul_nonneg hq hT)).mpr hYsq
  have hcross : X*Y≤Real.sqrt (p*q)*Real.sqrt R*Real.sqrt T := by
    have hh := mul_le_mul hXbound hYbound hY (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [Real.sqrt_mul hp]
    nlinarith
  have he := rowQuadratic_twoBlock hP a 1 ha (show (1:ℝ)∈Icc 0 1 by norm_num) (observable_abs hf)
  have hlow := rowQuadratic_lower_envelope hdom hf
  rw [he] at hlow
  unfold blockMean at hlow
  change -((a*((2*X)^2+(2*Y)^2)+2*1*(2*X)*(2*Y))/4)≤rowQuadratic U f at hlow
  change -a*p*R-2*Real.sqrt (p*q)*Real.sqrt R*Real.sqrt T-a*q*T≤_
  nlinarith [mul_le_mul_of_nonneg_left hXsq ha.1,mul_le_mul_of_nonneg_left hYsq ha.1]

set_option maxHeartbeats 600000 in
/-- Two stationary rows bounded by aμ on P and by 1 on its complement coincide.
The only graphon envelope assumption is the proved same-block cap. -/
theorem small_stationary_rows_eq {P : Set ℝ} (hP : MeasurableSet P)
    {μ ell : ℝ} (hμ : 18≤μ) (hell : 0<ell) {U : Graphon}
    (hdom : ∀ᵐ p ∂squareMeasure, U p≤twoBlock P hP
      (Real.exp (-((27/100)*μ))) 1
      ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by nlinarith)⟩ (by norm_num) p)
    {v w : ℝ → ℝ} (hv : AEMeasurable v unitMeasure) (hw : AEMeasurable w unitMeasure)
    (hbv : ∀ᵐ x ∂unitMeasure, ell≤v x ∧ v x≤1)
    (hbw : ∀ᵐ x ∂unitMeasure, ell≤w x ∧ w x≤1)
    (hvcap : ∀ᵐ x ∂unitMeasure, x∈P → v x≤Real.exp (-((27/100)*μ)))
    (hwcap : ∀ᵐ x ∂unitMeasure, x∈P → w x≤Real.exp (-((27/100)*μ)))
    (hEv : ∀ᵐ x ∂unitMeasure, Real.log (v x)+μ*rowOperator U v x=0)
    (hEw : ∀ᵐ x ∂unitMeasure, Real.log (w x)+μ*rowOperator U w x=0) :
    v=ᵐ[unitMeasure] w := by
  let a := Real.exp (-((27/100:ℝ)*μ))
  have ha := small_rigidity_weight_bounds hμ
  have hμ0 : 0≤μ := by linarith
  have hvb := profile_boundedObservable hv (hbv.mono fun x hx => ⟨(hell.trans_le hx.1).le,hx.2⟩)
  have hwb := profile_boundedObservable hw (hbw.mono fun x hx => ⟨(hell.trans_le hx.1).le,hx.2⟩)
  have hlv := profile_log_boundedObservable hv hell hbv
  have hlw := profile_log_boundedObservable hw hell hbw
  let f := fun x => v x-w x
  have hf : BoundedObservable unitMeasure f := by
    convert hvb.add (hwb.const_mul (-1)) using 1
    funext x; dsimp [f]; ring
  have hlogdiff : BoundedObservable unitMeasure (fun x => Real.log (v x)-Real.log (w x)) := by
    convert hlv.add (hlw.const_mul (-1)) using 1
    funext x; ring
  have hlog : weightedBlockNorm P a 1 0 f≤
      ∫ x, f x*(Real.log (v x)-Real.log (w x)) ∂unitMeasure := by
    apply integral_mono_ae (weightedBlockNorm_integrable hP a 1 0 hf) (hf.mul hlogdiff).integrable
    filter_upwards [hbv,hbw,hvcap,hwcap] with x hx hy hxc hyc
    have hvup : v x≤blockProfile P a 1 x+0 := by
      dsimp [blockProfile]
      split_ifs with hxp
      · simpa [a] using hxc hxp
      · simpa using hx.2
    have hwup : w x≤blockProfile P a 1 x+0 := by
      dsimp [blockProfile]
      split_ifs with hxp
      · simpa [a] using hyc hxp
      · simpa using hy.2
    exact log_strong_monotone (hell.trans_le hy.1) (hell.trans_le hx.1) hwup hvup
  have hzero := stationary_difference_identity U μ hvb hwb hlv hlw hEv hEw
  have hQ := rowQuadratic_lower_blockcap hP (a := a) ⟨ha.1.le,ha.2.1⟩ hdom hf
  let R := ∫ x in P, f x^2 ∂unitMeasure
  let T := ∫ x in Pᶜ, f x^2 ∂unitMeasure
  let p := unitMeasure.real P
  have hp : 0≤p := measureReal_nonneg
  have hp1 : p≤1 := by simpa [p] using measureReal_mono (μ := unitMeasure) (subset_univ P)
  have hq : unitMeasure.real Pᶜ=1-p := by simp [measureReal_compl hP,p]
  have hR : 0≤R := integral_nonneg fun _ => sq_nonneg _
  have hT : 0≤T := integral_nonneg fun _ => sq_nonneg _
  have hRsq := Real.sq_sqrt hR
  have hTsq := Real.sq_sqrt hT
  rw [weightedBlockNorm_eq hP a 1 0 hf] at hlog
  simp only [add_zero,div_one] at hlog
  change R/a+T≤_ at hlog
  change _+μ*rowQuadratic U f=0 at hzero
  change -a*p*R-2*Real.sqrt (p*unitMeasure.real Pᶜ)*Real.sqrt R*Real.sqrt T-a*unitMeasure.real Pᶜ*T≤_ at hQ
  rw [hq] at hQ
  have hlow := mul_le_mul_of_nonneg_left hQ hμ0
  have hform : (a⁻¹-μ*a*p)*(Real.sqrt R)^2-2*μ*Real.sqrt (p*(1-p))*Real.sqrt R*Real.sqrt T+
      (1-μ*a*(1-p))*(Real.sqrt T)^2≤0 := by
    rw [hRsq,hTsq]
    rw [div_eq_mul_inv] at hlog
    nlinarith
  have hnorms := small_rigidity_block_norms_zero hμ hp hp1 hform
  have htotal : (∫ x, f x^2 ∂unitMeasure)=0 := by
    have hisq : Integrable (fun x => f x^2) unitMeasure := by simpa only [pow_two] using (hf.mul hf).integrable
    have hs := integral_add_compl hP hisq
    change R+T=_ at hs
    rw [hnorms.1] at hRsq
    rw [hnorms.2] at hTsq
    nlinarith
  exact (profileL2Sq_eq_zero_iff hvb hwb).mp htotal

end SparseLowerTail.Section07

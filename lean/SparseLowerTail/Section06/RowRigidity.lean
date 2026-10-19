import SparseLowerTail.Section06.TwoWellRows
import SparseLowerTail.Section02.TriangleL2

/-! Quantitative identification of nearby stationary rows. The proof uses the
strong monotonicity of log directly, avoiding integration over row segments. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section06
open Section04 Section02

/-- Log is strongly monotone on every positive bounded interval. -/
theorem log_strong_monotone {x y R : ℝ} (hx : 0<x) (hy : 0<y)
    (hxR : x≤R) (hyR : y≤R) :
    (y-x)^2/R≤(y-x)*(Real.log y-Real.log x) := by
  have hR : 0<R := hx.trans_le hxR
  let f := fun t : ℝ => Real.log t-t/R
  have hm : MonotoneOn f (Ioc 0 R) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 R)
    · intro t ht
      exact ((Real.continuousAt_log ht.1.ne').sub (continuousAt_id.div_const R)).continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact ((Real.hasDerivAt_log ht.1.ne').sub ((hasDerivAt_id t).div_const R)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have hd : HasDerivAt f (t⁻¹-1/R) t := by
        convert (Real.hasDerivAt_log ht.1.ne').sub ((hasDerivAt_id t).div_const R) using 1
      rw [hd.deriv]
      have h := one_div_le_one_div_of_le ht.1 ht.2.le
      simpa only [one_div] using sub_nonneg.mpr h
  rcases le_total x y with hxy | hyx
  · have hh := hm ⟨hx,hxR⟩ ⟨hy,hyR⟩ hxy
    have hp := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hh)
    dsimp [f] at hp
    simp only [div_eq_mul_inv] at hp ⊢
    nlinarith
  · have hh := hm ⟨hy,hyR⟩ ⟨hx,hxR⟩ hyx
    have hp := mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hh)
    dsimp [f] at hp
    simp only [div_eq_mul_inv] at hp ⊢
    nlinarith

private theorem observable_restrict {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) (P : Set ℝ) :
    BoundedObservable (unitMeasure.restrict P) v := by
  obtain ⟨K,hK,hb⟩ := hv.bound
  exact ⟨hv.measurable.restrict,K,hK,ae_restrict_of_ae hb⟩

private theorem observable_abs {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) :
    BoundedObservable unitMeasure (fun x => |v x|) := by
  obtain ⟨K,hK,hb⟩ := hv.bound
  exact ⟨(by simpa only [Real.norm_eq_abs] using hv.measurable.norm),K,hK,hb.mono fun _ h => by simpa using h⟩

theorem block_integral_sq_le {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) (P : Set ℝ) :
    (∫ x in P,v x ∂unitMeasure)^2≤unitMeasure.real P*(∫ x in P,(v x)^2 ∂unitMeasure) := by
  have h := integral_mul_sq_le (observable_restrict hv P) (BoundedObservable.const (μ:=unitMeasure.restrict P) 1)
  simpa [mul_comm] using h

/-- Uniform kernel errors act on signed bounded profiles with their squared L² norm. -/
theorem abs_weighted_kernel_le {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K)
    {ζ : ℝ} (hζ : 0≤ζ) (hbound : ∀ᵐ p ∂squareMeasure,|K p|≤ζ)
    {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) :
    |∫ p,v p.1*K p*v p.2 ∂squareMeasure|≤ζ*(∫ x,(v x)^2 ∂unitMeasure) := by
  have hv1 : BoundedObservable squareMeasure (fun p => v p.1) := hv.comp Measure.quasiMeasurePreserving_fst
  have hv2 : BoundedObservable squareMeasure (fun p => v p.2) := hv.comp Measure.quasiMeasurePreserving_snd
  have hvi := ((hv1.mul hK).mul hv2).integrable
  have hva := observable_abs hv
  have hAi := ((hva.comp Measure.quasiMeasurePreserving_fst).mul
    (hva.comp Measure.quasiMeasurePreserving_snd)).integrable
  have hmono : (∫ p,|v p.1*K p*v p.2| ∂squareMeasure)≤
      ∫ p,ζ*(|v p.1| * |v p.2|) ∂squareMeasure := by
    apply integral_mono_ae hvi.norm (hAi.const_mul ζ)
    filter_upwards [hbound] with p hp
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    nlinarith [mul_nonneg (abs_nonneg (v p.1)) (abs_nonneg (v p.2)),
      mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg (v p.1)) (abs_nonneg (v p.2)))]
  have hprod : (∫ p,|v p.1| * |v p.2| ∂squareMeasure)=
      (∫ x,|v x| ∂unitMeasure)*(∫ x,|v x| ∂unitMeasure) := integral_prod_mul (μ:=unitMeasure) (ν:=unitMeasure)
        (fun x : ℝ => |v x|) (fun x : ℝ => |v x|)
  rw [integral_const_mul,hprod] at hmono
  have hCS := integral_mul_sq_le hva (BoundedObservable.const (μ:=unitMeasure) 1)
  simp only [mul_one,one_pow,integral_const,measureReal_univ_eq_one,smul_eq_mul,mul_one,
    sq_abs] at hCS
  have hn : |∫ p,v p.1*K p*v p.2 ∂squareMeasure|≤∫ p,|v p.1*K p*v p.2| ∂squareMeasure := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f:=fun p => v p.1*K p*v p.2) (μ:=squareMeasure)
  have hh := mul_le_mul_of_nonneg_left hCS hζ
  nlinarith

theorem rowQuadratic_uniform_bound {U W : Graphon} {ζ : ℝ} (hζ : 0≤ζ)
    (hbound : ∀ᵐ p ∂squareMeasure,|U p-W p|≤ζ) {v : ℝ → ℝ}
    (hv : BoundedObservable unitMeasure v) :
    |rowQuadratic U v-rowQuadratic W v|≤ζ*(∫ x,(v x)^2 ∂unitMeasure) := by
  have hK : BoundedObservable squareMeasure (fun p => U p-W p) := by
    simpa only [neg_one_mul,sub_eq_add_neg] using
      (graphon_boundedObservable U).add ((graphon_boundedObservable W).const_mul (-1))
  have h := abs_weighted_kernel_le hK hζ hbound hv
  have hiU := (((hv.comp Measure.quasiMeasurePreserving_fst).mul (graphon_boundedObservable U)).mul
    (hv.comp Measure.quasiMeasurePreserving_snd)).integrable
  have hiW := (((hv.comp Measure.quasiMeasurePreserving_fst).mul (graphon_boundedObservable W)).mul
    (hv.comp Measure.quasiMeasurePreserving_snd)).integrable
  have he : (fun p => v p.1*(U p-W p)*v p.2)=
      (fun p => v p.1*U p*v p.2-v p.1*W p*v p.2) := by funext p; ring
  rw [he,integral_sub hiU hiW] at h
  exact h

private theorem quadratic_nonneg {A B C x y : ℝ} (hA : 0<A) (hd : 0≤A*C-B^2) :
    0≤A*x^2+2*B*x*y+C*y^2 := by
  have he : A*(A*x^2+2*B*x*y+C*y^2)=(A*x+B*y)^2+(A*C-B^2)*y^2 := by ring
  have hp : 0≤A*(A*x^2+2*B*x*y+C*y^2) := by
    rw [he]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hd (sq_nonneg _))
  exact (mul_nonneg_iff_of_pos_left hA).mp hp

/-- A uniform finite-dimensional margin, allowing both block masses to be at most 1/2+η. -/
theorem exists_block_coercivity_margin {a b μ : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    ∃ η : ℝ,0<η ∧ 0<1/(a+η)-η ∧ 0<1/(b+η)-η ∧
      0<((1/(a+η)-η)/(1/2+η)+μ*a)*((1/(b+η)-η)/(1/2+η)+μ*a)-(μ*b)^2 := by
  have hb : 0<b := ha.trans hab
  let A := fun t : ℝ => 1/(a+t)-t
  let C := fun t : ℝ => 1/(b+t)-t
  let D := fun t : ℝ => (A t/(1/2+t)+μ*a)*(C t/(1/2+t)+μ*a)-(μ*b)^2
  have hAc : ContinuousAt A 0 := by dsimp [A]; fun_prop (disch := simpa using ha.ne')
  have hCc : ContinuousAt C 0 := by dsimp [C]; fun_prop (disch := simpa using hb.ne')
  have hDc : ContinuousAt D 0 := by dsimp [D]; fun_prop (disch := norm_num)
  have hA : 0<A 0 := by dsimp [A]; simp only [add_zero,sub_zero]; positivity
  have hC : 0<C 0 := by dsimp [C]; simp only [add_zero,sub_zero]; positivity
  have hD : 0<D 0 := by
    have h := wellHessian_det_pos ha hab hμ hEL
    dsimp [D,A,C]
    norm_num [div_eq_mul_inv] at h ⊢
    nlinarith
  have he : ∀ᶠ t : ℝ in 𝓝 0,0<A t ∧ 0<C t ∧ 0<D t :=
    (hAc.eventually (eventually_gt_nhds hA)).and
      ((hCc.eventually (eventually_gt_nhds hC)).and (hDc.eventually (eventually_gt_nhds hD)))
  have her : ∀ᶠ t : ℝ in 𝓝[>] 0,0<t ∧ 0<A t ∧ 0<C t ∧ 0<D t :=
    (show ∀ᶠ t : ℝ in 𝓝[>] 0,0<t from self_mem_nhdsWithin).and
      (he.filter_mono nhdsWithin_le_nhds)
  obtain ⟨η,hη,hAη,hCη,hDη⟩ := her.exists
  exact ⟨η,hη,hAη,hCη,hDη⟩

def weightedBlockNorm (P : Set ℝ) (a b η : ℝ) (v : ℝ → ℝ) : ℝ :=
  ∫ x,(v x)^2/(blockProfile P a b x+η) ∂unitMeasure

theorem weightedBlockNorm_eq {P : Set ℝ} (hP : MeasurableSet P) (a b η : ℝ)
    {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) :
    weightedBlockNorm P a b η v=(∫ x in P,(v x)^2 ∂unitMeasure)/(a+η)+
      (∫ x in Pᶜ,(v x)^2 ∂unitMeasure)/(b+η) := by
  classical
  have hi : Integrable (fun x => (v x)^2) unitMeasure := by simpa only [pow_two] using (hv.mul hv).integrable
  unfold weightedBlockNorm
  have he : (fun x => (v x)^2/(blockProfile P a b x+η))=
      P.piecewise (fun x => (v x)^2/(a+η)) (fun x => (v x)^2/(b+η)) := by
    funext x
    simp only [blockProfile,Set.piecewise]
    split_ifs <;> rfl
  rw [he,integral_piecewise hP (hi.div_const _).integrableOn (hi.div_const _).integrableOn,
    integral_div,integral_div]

/-- Coercivity for every signed bounded profile, including its within-block variance. -/
theorem block_coercivity {P : Set ℝ} (hP : MeasurableSet P)
    {a b μ η : ℝ} (ha : a∈Icc 0 1) (hb : b∈Icc 0 1) (hμ : 0≤μ) (hη : 0<η)
    (hA : 0<1/(a+η)-η) (hC : 0<1/(b+η)-η)
    (hD : 0≤((1/(a+η)-η)/(1/2+η)+μ*a)*((1/(b+η)-η)/(1/2+η)+μ*a)-(μ*b)^2)
    (hp : unitMeasure.real P≤1/2+η) (hpc : unitMeasure.real Pᶜ≤1/2+η)
    {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) :
    η*(∫ x,(v x)^2 ∂unitMeasure)≤weightedBlockNorm P a b η v+
      μ*rowQuadratic (twoBlock P hP a b ha hb) v := by
  let X := ∫ x in P,v x ∂unitMeasure
  let Y := ∫ x in Pᶜ,v x ∂unitMeasure
  let R := ∫ x in P,(v x)^2 ∂unitMeasure
  let S := ∫ x in Pᶜ,(v x)^2 ∂unitMeasure
  let M : ℝ := 1/2+η
  have hM : 0<M := by dsimp [M]; linarith
  have hR : 0≤R := integral_nonneg fun _ => sq_nonneg _
  have hS : 0≤S := integral_nonneg fun _ => sq_nonneg _
  have hX : X^2≤M*R := (block_integral_sq_le hv P).trans (mul_le_mul_of_nonneg_right hp hR)
  have hY : Y^2≤M*S := (block_integral_sq_le hv Pᶜ).trans (mul_le_mul_of_nonneg_right hpc hS)
  have hX' : ((1/(a+η)-η)/M)*X^2≤(1/(a+η)-η)*R := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hM).mpr
    nlinarith [mul_le_mul_of_nonneg_left hX hA.le]
  have hY' : ((1/(b+η)-η)/M)*Y^2≤(1/(b+η)-η)*S := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hM).mpr
    nlinarith [mul_le_mul_of_nonneg_left hY hC.le]
  have hq := quadratic_nonneg (x:=X) (y:=Y)
    (show 0<(1/(a+η)-η)/M+μ*a by
      exact add_pos_of_pos_of_nonneg (div_pos hA hM) (mul_nonneg hμ ha.1)) hD
  have hvi : Integrable (fun x => (v x)^2) unitMeasure := by simpa only [pow_two] using (hv.mul hv).integrable
  have hnorm : (∫ x,(v x)^2 ∂unitMeasure)=R+S := (integral_add_compl hP hvi).symm
  have hQ : rowQuadratic (twoBlock P hP a b ha hb) v=a*(X^2+Y^2)+2*b*X*Y := by
    rw [rowQuadratic_twoBlock hP a b ha hb hv]
    unfold blockMean
    dsimp [X,Y]
    ring
  rw [hnorm,weightedBlockNorm_eq hP a b η hv,hQ]
  change η*(R+S)≤R/(a+η)+S/(b+η)+μ*(a*(X^2+Y^2)+2*b*X*Y)
  simp only [div_eq_mul_inv] at hX' hY' hq ⊢
  nlinarith

theorem rowOperator_boundedObservable (U : Graphon) {v : ℝ → ℝ}
    (hv : BoundedObservable unitMeasure v) : BoundedObservable unitMeasure (rowOperator U v) :=
  ((graphon_boundedObservable U).mul (hv.comp Measure.quasiMeasurePreserving_snd)).integral_left

theorem rowOperator_sub_ae (U : Graphon) {v w : ℝ → ℝ}
    (hv : BoundedObservable unitMeasure v) (hw : BoundedObservable unitMeasure w) :
    ∀ᵐ x ∂unitMeasure,rowOperator U (fun y => v y-w y) x=rowOperator U v x-rowOperator U w x := by
  filter_upwards [boundedObservable_slices (graphon_boundedObservable U)] with x hx
  unfold rowOperator
  simp_rw [mul_sub]
  exact integral_sub (hx.mul hv).integrable (hx.mul hw).integrable

theorem rowQuadratic_pair (U : Graphon) {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) :
    rowQuadratic U v=(∫ x,v x*rowOperator U v x ∂unitMeasure) := by
  have hi := (((hv.comp Measure.quasiMeasurePreserving_fst).mul (graphon_boundedObservable U)).mul
    (hv.comp Measure.quasiMeasurePreserving_snd)).integrable
  rw [rowQuadratic,integral_prod _ hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  unfold rowOperator
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by ring

theorem profile_log_boundedObservable {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ᵐ x ∂unitMeasure,ell≤v x ∧ v x≤1) :
    BoundedObservable unitMeasure (fun x => Real.log (v x)) := by
  refine ⟨Real.measurable_log.comp_aemeasurable hv,|Real.log ell|,abs_nonneg _,?_⟩
  filter_upwards [hb] with x hx
  have hl := Real.log_le_log hell hx.1
  have hu := Real.log_nonpos (hell.trans_le hx.1).le hx.2
  rw [Real.norm_eq_abs,abs_of_nonpos hu]
  exact neg_le_abs (Real.log ell) |>.trans' (by linarith)

/-- Pairing two actual Euler--Lagrange equations with their difference. -/
theorem stationary_difference_identity (U : Graphon) (ν : ℝ) {v w : ℝ → ℝ}
    (hv : BoundedObservable unitMeasure v) (hw : BoundedObservable unitMeasure w)
    (hlv : BoundedObservable unitMeasure (fun x => Real.log (v x)))
    (hlw : BoundedObservable unitMeasure (fun x => Real.log (w x)))
    (hEv : ∀ᵐ x ∂unitMeasure,Real.log (v x)+ν*rowOperator U v x=0)
    (hEw : ∀ᵐ x ∂unitMeasure,Real.log (w x)+ν*rowOperator U w x=0) :
    (∫ x,(v x-w x)*(Real.log (v x)-Real.log (w x)) ∂unitMeasure)+
      ν*rowQuadratic U (fun x => v x-w x)=0 := by
  have hd : BoundedObservable unitMeasure (fun x => v x-w x) := by
    simpa only [neg_one_mul,sub_eq_add_neg] using hv.add (hw.const_mul (-1))
  have hld : BoundedObservable unitMeasure (fun x => Real.log (v x)-Real.log (w x)) := by
    simpa only [neg_one_mul,sub_eq_add_neg] using hlv.add (hlw.const_mul (-1))
  have hpair := (hd.mul (rowOperator_boundedObservable U hd)).integrable
  have he : (fun x => (v x-w x)*(Real.log (v x)-Real.log (w x))+
      ν*((v x-w x)*rowOperator U (fun y => v y-w y) x)) =ᵐ[unitMeasure] (fun _ => 0) := by
    filter_upwards [hEv,hEw,rowOperator_sub_ae U hv hw] with x hx hy hz
    rw [hz]
    linear_combination (v x-w x)*(hx-hy)
  have hi := integral_congr_ae he
  rw [integral_add (hd.mul hld).integrable (hpair.const_mul ν),integral_const_mul,
    ← rowQuadratic_pair U hd] at hi
  simpa using hi

theorem rowQuadratic_abs_le (U : Graphon) {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) :
    |rowQuadratic U v|≤∫ x,(v x)^2 ∂unitMeasure := by
  have hb : ∀ᵐ p ∂squareMeasure,|U p|≤1 := U.bounded.mono fun _ hp => by
    simpa only [abs_of_nonneg hp.1] using hp.2
  simpa only [one_mul] using abs_weighted_kernel_le (graphon_boundedObservable U) (by norm_num) hb hv

theorem weightedBlockNorm_integrable {P : Set ℝ} (hP : MeasurableSet P) (a b η : ℝ)
    {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v) :
    Integrable (fun x => (v x)^2/(blockProfile P a b x+η)) unitMeasure := by
  classical
  have hrec := blockProfile_boundedObservable hP (1/(a+η)) (1/(b+η))
  have hi := ((hv.mul hv).mul hrec).integrable
  convert hi using 1
  funext x
  simp only [blockProfile]
  split_ifs <;> simp only [div_eq_mul_inv,one_mul,pow_two]

/-- Two nearby stationary rows coincide once the concrete block quadratic margin
exceeds the kernel and multiplier errors. -/
theorem stationary_rows_eq_of_margin {P : Set ℝ} (hP : MeasurableSet P)
    {a b μ ν η ζ ell : ℝ} (ha : a∈Icc 0 1) (hb : b∈Icc 0 1)
    (hμ : 0≤μ) (hν : 0≤ν) (hη : 0<η) (hζ : 0≤ζ) (hell : 0<ell)
    (hA : 0<1/(a+η)-η) (hC : 0<1/(b+η)-η)
    (hD : 0≤((1/(a+η)-η)/(1/2+η)+μ*a)*((1/(b+η)-η)/(1/2+η)+μ*a)-(μ*b)^2)
    (hp : unitMeasure.real P≤1/2+η) (hpc : unitMeasure.real Pᶜ≤1/2+η)
    (herr : ν*ζ+|ν-μ|<η) {U : Graphon}
    (hU : ∀ᵐ p ∂squareMeasure,|U p-twoBlock P hP a b ha hb p|≤ζ)
    {v w : ℝ → ℝ} (hv : AEMeasurable v unitMeasure) (hw : AEMeasurable w unitMeasure)
    (hbv : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) (hbw : ∀ᵐ x ∂unitMeasure,w x∈Icc (0:ℝ) 1)
    (hvlo : ∀ᵐ x ∂unitMeasure,ell≤v x) (hwlo : ∀ᵐ x ∂unitMeasure,ell≤w x)
    (hvup : ∀ᵐ x ∂unitMeasure,v x≤blockProfile P a b x+η)
    (hwup : ∀ᵐ x ∂unitMeasure,w x≤blockProfile P a b x+η)
    (hEv : ∀ᵐ x ∂unitMeasure,Real.log (v x)+ν*rowOperator U v x=0)
    (hEw : ∀ᵐ x ∂unitMeasure,Real.log (w x)+ν*rowOperator U w x=0) :
    v =ᵐ[unitMeasure] w := by
  have hvb := profile_boundedObservable hv hbv
  have hwb := profile_boundedObservable hw hbw
  have hlv := profile_log_boundedObservable hv hell (hvlo.and (hbv.mono fun _ hx => hx.2))
  have hlw := profile_log_boundedObservable hw hell (hwlo.and (hbw.mono fun _ hx => hx.2))
  let d := fun x => v x-w x
  have hd : BoundedObservable unitMeasure d := by
    simpa only [d,neg_one_mul,sub_eq_add_neg] using hvb.add (hwb.const_mul (-1))
  have hld : BoundedObservable unitMeasure (fun x => Real.log (v x)-Real.log (w x)) := by
    simpa only [neg_one_mul,sub_eq_add_neg] using hlv.add (hlw.const_mul (-1))
  have hlog : weightedBlockNorm P a b η d≤
      ∫ x,(v x-w x)*(Real.log (v x)-Real.log (w x)) ∂unitMeasure := by
    apply integral_mono_ae (weightedBlockNorm_integrable hP a b η hd) (hd.mul hld).integrable
    filter_upwards [hvlo,hwlo,hvup,hwup] with x hvx hwx hvx' hwx'
    exact log_strong_monotone (hell.trans_le hwx) (hell.trans_le hvx) hwx' hvx'
  have hzero := stationary_difference_identity U ν hvb hwb hlv hlw hEv hEw
  have hcoer := block_coercivity hP ha hb hμ hη hA hC hD hp hpc hd
  have hdiff := rowQuadratic_uniform_bound hζ hU hd
  have hQB := rowQuadratic_abs_le (twoBlock P hP a b ha hb) hd
  let R := ∫ x,(d x)^2 ∂unitMeasure
  have hR : 0≤R := integral_nonneg fun _ => sq_nonneg _
  have hlow := mul_le_mul_of_nonneg_left (abs_le.mp hdiff).1 hν
  have hlow2 := neg_abs_le ((ν-μ)*rowQuadratic (twoBlock P hP a b ha hb) d)
  have hprod := mul_le_mul_of_nonneg_left hQB (abs_nonneg (ν-μ))
  rw [← abs_mul] at hprod
  have hupper : μ*rowQuadratic (twoBlock P hP a b ha hb) d-ν*rowQuadratic U d≤
      (ν*ζ+|ν-μ|)*R := by dsimp [R]; nlinarith
  have hRzero : R=0 := by
    have hz : (η-(ν*ζ+|ν-μ|))*R≤0 := by
      change (∫ x,(v x-w x)*(Real.log (v x)-Real.log (w x)) ∂unitMeasure)+ν*rowQuadratic U d=0 at hzero
      change η*R≤_ at hcoer
      nlinarith
    have hpos := sub_pos.mpr herr
    nlinarith
  exact (profileL2Sq_eq_zero_iff hvb hwb).mp hRzero

/-- Local uniqueness of a stationary row near either balanced well. The radius
controls the block mass, the multiplier, the kernel, and the row profiles. -/
theorem exists_stationary_row_radius {a b μ : ℝ} (ha : 0<a) (hab : a<b)
    (hb : b≤1) (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (P : Set ℝ) (hP : MeasurableSet P) (ν : ℝ) (U : Graphon)
      (v w : ℝ→ℝ), 0≤ν → |ν-μ|<δ → |unitMeasure.real P-1/2|<δ →
      (∀ᵐ p ∂squareMeasure,|U p-twoBlock P hP a b ⟨ha.le,hab.le.trans hb⟩ ⟨(ha.trans hab).le,hb⟩ p|≤δ) →
      AEMeasurable v unitMeasure → AEMeasurable w unitMeasure →
      (∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) → (∀ᵐ x ∂unitMeasure,w x∈Icc (0:ℝ) 1) →
      (∀ᵐ x ∂unitMeasure,|v x-blockProfile P a b x|≤δ) →
      (∀ᵐ x ∂unitMeasure,|w x-blockProfile P a b x|≤δ) →
      (∀ᵐ x ∂unitMeasure,Real.log (v x)+ν*rowOperator U v x=0) →
      (∀ᵐ x ∂unitMeasure,Real.log (w x)+ν*rowOperator U w x=0) →
      v =ᵐ[unitMeasure] w := by
  obtain ⟨η,hη,hA,hC,hD⟩ := exists_block_coercivity_margin ha hab hμ hEL
  let δ := min η (min (a/2) (min 1 (η/(2*(μ+2)))))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hdη : δ≤η := min_le_left _ _
  have hda : δ≤a/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : δ≤1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hde : δ≤η/(2*(μ+2)) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,hδ,?_⟩
  intro P hP ν U v w hν hνμ hp hU hv hw hbv hbw hvc hwc hEv hEw
  have hνb : ν≤μ+1 := by have hh := (abs_lt.mp hνμ).2; linarith
  have herr : ν*δ+|ν-μ|<η := by
    have he := (le_div_iff₀ (show 0<2*(μ+2) by positivity)).mp hde
    have hm := mul_le_mul_of_nonneg_right hνb hδ.le
    linarith
  have hp' : unitMeasure.real P≤1/2+η := by have hh := (abs_lt.mp hp).2; linarith
  have hpc : unitMeasure.real Pᶜ≤1/2+η := by
    rw [measureReal_compl hP,measureReal_univ_eq_one]
    have hh := (abs_lt.mp hp).1
    linarith
  have hg (x : ℝ) : a≤blockProfile P a b x := by
    classical
    dsimp [blockProfile]
    split_ifs <;> linarith
  have hvlo : ∀ᵐ x ∂unitMeasure,a/2≤v x := hvc.mono fun x hx => by
    have hh := (abs_le.mp hx).1
    have hhg := hg x
    linarith
  have hwlo : ∀ᵐ x ∂unitMeasure,a/2≤w x := hwc.mono fun x hx => by
    have hh := (abs_le.mp hx).1
    have hhg := hg x
    linarith
  have hvup : ∀ᵐ x ∂unitMeasure,v x≤blockProfile P a b x+η := hvc.mono fun x hx => by
    have hh := (abs_le.mp hx).2
    linarith
  have hwup : ∀ᵐ x ∂unitMeasure,w x≤blockProfile P a b x+η := hwc.mono fun x hx => by
    have hh := (abs_le.mp hx).2
    linarith
  exact stationary_rows_eq_of_margin hP ⟨ha.le,hab.le.trans hb⟩ ⟨(ha.trans hab).le,hb⟩
    hμ.le hν hη hδ.le (by positivity) hA hC hD.le hp' hpc herr hU hv hw hbv hbw
    hvlo hwlo hvup hwup hEv hEw

end SparseLowerTail.Section06

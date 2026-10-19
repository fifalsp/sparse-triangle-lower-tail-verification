import SparseLowerTail.Section06.TwoWellGrowth
import SparseLowerTail.Section06.InsertionLemma
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Deriv

/-! The strong Jensen reduction and quantitative two-well theorem for actual vertex profiles. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section04

def blockMean (v : ℝ → ℝ) (P : Set ℝ) : ℝ := 2*(∫ x in P,v x ∂unitMeasure)

def blockProfile (P : Set ℝ) (u w : ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x∈P then u else w

def profileL2Sq (v w : ℝ → ℝ) : ℝ := ∫ x,(v x-w x)^2 ∂unitMeasure

theorem profile_boundedObservable {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) : BoundedObservable unitMeasure v := by
  refine ⟨hv,1,by norm_num,?_⟩
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2

theorem profile_entropy_boundedObservable {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    BoundedObservable unitMeasure (fun x => entropy (v x)) := by
  refine ⟨continuous_entropy.measurable.comp_aemeasurable hv,1,by norm_num,?_⟩
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (entropy_nonneg hx.1)] using entropy_le_one hx

private theorem half_compl_mass {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) : unitMeasure Pᶜ=(1/2:ENNReal) := by
  rw [measure_compl hP (measure_ne_top _ _),measure_univ,hm]
  norm_num

private theorem half_mass_real {P : Set ℝ} (hm : unitMeasure P=(1/2:ENNReal)) :
    unitMeasure.real P=(1/2:ℝ) := by simp [Measure.real,hm]

theorem blockMean_mem {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) {P : Set ℝ}
    (hm : unitMeasure P=(1/2:ENNReal)) : blockMean v P∈Icc (0:ℝ) 1 := by
  have hvi := (profile_boundedObservable hv hb).integrable
  have hlo : 0≤∫ x in P,v x ∂unitMeasure := integral_nonneg_of_ae
    (ae_restrict_of_ae (hb.mono fun _ hx => hx.1))
  have hhi := integral_mono_ae hvi.integrableOn (integrable_const (μ:=unitMeasure.restrict P) (1:ℝ))
    (ae_restrict_of_ae (hb.mono fun _ hx => hx.2))
  rw [integral_const] at hhi
  simp only [Measure.real,Measure.restrict_apply_univ,hm,ENNReal.toReal_div,
    ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul,mul_one] at hhi
  constructor <;> dsimp [blockMean] <;> linarith

def strongEntropy (x : ℝ) : ℝ := entropy x-x^2/2

theorem continuous_strongEntropy : Continuous strongEntropy :=
  continuous_entropy.sub ((continuous_id.pow 2).div_const 2)

theorem convexOn_strongEntropy : ConvexOn ℝ (Icc (0:ℝ) 1) strongEntropy := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f':=fun x => Real.log x-x)
    (f'':=fun x => 1/x-1) (convex_Icc 0 1) continuous_strongEntropy.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hd := (hasDerivAt_entropy hx.1.ne').sub (((hasDerivAt_id x).pow 2).div_const 2)
    convert hd.hasDerivWithinAt using 1
    simp
  · intro x hx
    rw [interior_Icc] at hx
    simpa using ((Real.hasDerivAt_log hx.1.ne').sub (hasDerivAt_id x)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have h := (le_div_iff₀ hx.1).mpr (show (1:ℝ)*x≤1 by linarith [hx.2])
    linarith

/-- Strong Jensen on one half of the vertex space. -/
theorem half_entropy_jensen {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) {P : Set ℝ}
    (hm : unitMeasure P=(1/2:ENNReal)) :
    entropy (blockMean v P)/2+(∫ x in P,(v x)^2 ∂unitMeasure)/2-(blockMean v P)^2/4≤
      ∫ x in P,entropy (v x) ∂unitMeasure := by
  have hvb := profile_boundedObservable hv hb
  have hvi := hvb.integrable
  have hv2 : Integrable (fun x => (v x)^2) unitMeasure := by
    simpa only [pow_two] using (hvb.mul hvb).integrable
  have hhi := (profile_entropy_boundedObservable hv hb).integrable
  have hstrong : Integrable (fun x => strongEntropy (v x)) unitMeasure := hhi.sub (hv2.div_const 2)
  have hj := convexOn_strongEntropy.map_set_average_le continuous_strongEntropy.continuousOn
    isClosed_Icc (show unitMeasure P≠0 by rw [hm]; norm_num) (measure_ne_top _ _)
    (ae_restrict_of_ae hb) hvi.integrableOn hstrong.integrableOn
  rw [setAverage_eq,setAverage_eq] at hj
  simp only [smul_eq_mul,half_mass_real hm] at hj
  norm_num at hj
  change strongEntropy (blockMean v P)≤2*(∫ x in P,strongEntropy (v x) ∂unitMeasure) at hj
  unfold strongEntropy at hj
  rw [integral_sub hhi.integrableOn (hv2.div_const 2).integrableOn,integral_div] at hj
  linarith

theorem blockProfile_boundedObservable {P : Set ℝ} (hP : MeasurableSet P) (u w : ℝ) :
    BoundedObservable unitMeasure (blockProfile P u w) := by
  classical
  refine ⟨(measurable_const.ite hP measurable_const).aemeasurable,
    max |u| |w|,le_trans (abs_nonneg u) (le_max_left _ _),?_⟩
  apply Eventually.of_forall
  intro x
  simp only [blockProfile,Real.norm_eq_abs]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem integral_blockProfile {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) (u w : ℝ) :
    (∫ x,blockProfile P u w x ∂unitMeasure)=(u+w)/2 := by
  classical
  exact integral_half_partition hP hm u w

theorem integral_blockProfile_mul {P : Set ℝ} (hP : MeasurableSet P)
    {v : ℝ → ℝ} (hv : Integrable v unitMeasure) (u w : ℝ) :
    (∫ x,blockProfile P u w x*v x ∂unitMeasure)=
      u*(∫ x in P,v x ∂unitMeasure)+w*(∫ x in Pᶜ,v x ∂unitMeasure) := by
  classical
  simp only [blockProfile,ite_mul]
  rw [show (fun x => if x∈P then u*v x else w*v x)=P.piecewise (fun x => u*v x) (fun x => w*v x) from rfl]
  rw [integral_piecewise hP (hv.const_mul u).integrableOn (hv.const_mul w).integrableOn,
    integral_const_mul,integral_const_mul]

theorem profileL2Sq_blockProfile {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v)
    (u w : ℝ) :
    profileL2Sq v (blockProfile P u w)=
      (∫ x,(v x)^2 ∂unitMeasure)-2*(u*(∫ x in P,v x ∂unitMeasure)+
        w*(∫ x in Pᶜ,v x ∂unitMeasure))+(u^2+w^2)/2 := by
  classical
  have hB := blockProfile_boundedObservable hP u w
  have hv2 : Integrable (fun x => (v x)^2) unitMeasure := by simpa only [pow_two] using (hv.mul hv).integrable
  have hB2 : Integrable (fun x => (blockProfile P u w x)^2) unitMeasure := by
    simpa only [pow_two] using (hB.mul hB).integrable
  have hcross := (hB.mul hv).integrable
  have he : (fun x => (v x-blockProfile P u w x)^2)=
      (fun x => (v x)^2-2*(blockProfile P u w x*v x)+(blockProfile P u w x)^2) := by funext x; ring
  unfold profileL2Sq
  have hadd := integral_add (hv2.sub (hcross.const_mul 2)) hB2
  simp only [Pi.sub_apply] at hadd
  rw [he,hadd,integral_sub hv2 (hcross.const_mul 2),
    integral_const_mul,integral_blockProfile_mul hP hv.integrable]
  have hs : (fun x => (blockProfile P u w x)^2)=blockProfile P (u^2) (w^2) := by
    funext x
    simp only [blockProfile]
    split_ifs <;> rfl
  rw [hs,integral_blockProfile hP hm]

theorem profileL2Sq_nonneg (v w : ℝ → ℝ) : 0≤profileL2Sq v w :=
  integral_nonneg fun _ => sq_nonneg _

/-- Exact finite-rank quadratic form of the balanced kernel on any bounded profile. -/
theorem rowQuadratic_twoBlock {P : Set ℝ} (hP : MeasurableSet P)
    (a b : ℝ) (ha : a∈Icc 0 1) (hb : b∈Icc 0 1) {v : ℝ → ℝ}
    (hv : BoundedObservable unitMeasure v) :
    rowQuadratic (twoBlock P hP a b ha hb) v=
      (a*((blockMean v P)^2+(blockMean v Pᶜ)^2)+2*b*blockMean v P*blockMean v Pᶜ)/4 := by
  classical
  let B := twoBlock P hP a b ha hb
  have hi := (((hv.comp Measure.quasiMeasurePreserving_fst).mul (graphon_boundedObservable B)).mul
    (hv.comp Measure.quasiMeasurePreserving_snd)).integrable
  rw [rowQuadratic,integral_prod _ hi]
  have hinner : ∀ x : ℝ,(∫ y,v x*B (x,y)*v y ∂unitMeasure)=
      v x*blockProfile P (a*(∫ y in P,v y ∂unitMeasure)+b*(∫ y in Pᶜ,v y ∂unitMeasure))
        (b*(∫ y in P,v y ∂unitMeasure)+a*(∫ y in Pᶜ,v y ∂unitMeasure)) x := by
    intro x
    rw [show (fun y => v x*B (x,y)*v y)=(fun y => v x*(B (x,y)*v y)) from by funext y; ring,
      integral_const_mul]
    by_cases hx : x∈P
    · have he : (fun y => B (x,y))=blockProfile P a b := by
        funext y
        simp [B,twoBlock,blockValue,blockProfile,hx]
      have he' (y : ℝ) := congrFun he y
      simp_rw [he']
      rw [integral_blockProfile_mul hP hv.integrable]
      simp [blockProfile,hx]
    · have he : (fun y => B (x,y))=blockProfile P b a := by
        funext y
        simp [B,twoBlock,blockValue,blockProfile,hx]
      have he' (y : ℝ) := congrFun he y
      simp_rw [he']
      rw [integral_blockProfile_mul hP hv.integrable]
      simp [blockProfile,hx]
  simp_rw [hinner,mul_comm (v _) (blockProfile _ _ _ _)]
  rw [integral_blockProfile_mul hP hv.integrable]
  unfold blockMean
  ring

/-- The complete strong Jensen reduction `s6:jensen`. -/
theorem rowFunctional_twoBlock_jensen {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) (a b μ : ℝ)
    (ha : a∈Icc 0 1) (hb : b∈Icc 0 1) {v : ℝ → ℝ}
    (hv : AEMeasurable v unitMeasure) (hbound : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    scalarWell a b μ (blockMean v P) (blockMean v Pᶜ)+
      profileL2Sq v (blockProfile P (blockMean v P) (blockMean v Pᶜ))≤
      rowFunctional (twoBlock P hP a b ha hb) μ v := by
  have hvb := profile_boundedObservable hv hbound
  have hhi := (profile_entropy_boundedObservable hv hbound).integrable
  have hv2 : Integrable (fun x => (v x)^2) unitMeasure := by simpa only [pow_two] using (hvb.mul hvb).integrable
  have h1 := half_entropy_jensen hv hbound hm
  have h2 := half_entropy_jensen hv hbound (half_compl_mass hP hm)
  have he := integral_add_compl hP hhi
  have hs := integral_add_compl hP hv2
  rw [rowFunctional,rowQuadratic_twoBlock hP a b ha hb hvb,
    profileL2Sq_blockProfile hP hm hvb]
  unfold scalarWell blockMean at *
  nlinarith

theorem blockMean_blockProfile {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) (u w : ℝ) :
    blockMean (blockProfile P u w) P=u ∧ blockMean (blockProfile P u w) Pᶜ=w := by
  classical
  have h1 : (∫ x in P,blockProfile P u w x ∂unitMeasure)=(1/2:ℝ)*u := by
    calc
      _ = ∫ _ in P,u ∂unitMeasure := setIntegral_congr_fun hP (fun x hx => by simp [blockProfile,hx])
      _ = _ := by simp [integral_const,half_mass_real hm,smul_eq_mul]
  have h2 : (∫ x in Pᶜ,blockProfile P u w x ∂unitMeasure)=(1/2:ℝ)*w := by
    calc
      _ = ∫ _ in Pᶜ,w ∂unitMeasure := setIntegral_congr_fun hP.compl (fun x hx => by
        have hx' : x∉P := hx
        simp [blockProfile,hx'])
      _ = _ := by simp [integral_const,half_mass_real (half_compl_mass hP hm),smul_eq_mul]
  constructor
  · unfold blockMean
    rw [h1]
    ring
  · unfold blockMean
    rw [h2]
    ring

theorem rowFunctional_blockProfile {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) (a b μ u w : ℝ)
    (ha : a∈Icc 0 1) (hb : b∈Icc 0 1) :
    rowFunctional (twoBlock P hP a b ha hb) μ (blockProfile P u w)=scalarWell a b μ u w := by
  classical
  have he : (fun x => entropy (blockProfile P u w x))=blockProfile P (entropy u) (entropy w) := by
    funext x
    simp only [blockProfile]
    split_ifs <;> rfl
  rw [rowFunctional,he,integral_blockProfile hP hm,
    rowQuadratic_twoBlock hP a b ha hb (blockProfile_boundedObservable hP u w),
    (blockMean_blockProfile hP hm u w).1,(blockMean_blockProfile hP hm u w).2]
  unfold scalarWell
  ring

/-- Orthogonal decomposition into within-block variance and distance of the block means. -/
theorem profileL2Sq_two_wells {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) {v : ℝ → ℝ} (hv : BoundedObservable unitMeasure v)
    (a b : ℝ) :
    min (profileL2Sq v (blockProfile P a b)) (profileL2Sq v (blockProfile P b a))=
      profileL2Sq v (blockProfile P (blockMean v P) (blockMean v Pᶜ))+
        wellDistanceSq a b (blockMean v P) (blockMean v Pᶜ)/2 := by
  have h1 : profileL2Sq v (blockProfile P a b)=
      profileL2Sq v (blockProfile P (blockMean v P) (blockMean v Pᶜ))+
      ((blockMean v P-a)^2+(blockMean v Pᶜ-b)^2)/2 := by
    rw [profileL2Sq_blockProfile hP hm hv,profileL2Sq_blockProfile hP hm hv]
    unfold blockMean
    ring
  have h2 : profileL2Sq v (blockProfile P b a)=
      profileL2Sq v (blockProfile P (blockMean v P) (blockMean v Pᶜ))+
      ((blockMean v P-b)^2+(blockMean v Pᶜ-a)^2)/2 := by
    rw [profileL2Sq_blockProfile hP hm hv,profileL2Sq_blockProfile hP hm hv]
    unfold blockMean
    ring
  rw [h1,h2]
  unfold wellDistanceSq
  simp only [min_def]
  split_ifs <;> linarith

/-- `thm:twowell` (c) for the actual integral functional, on any measurable balanced partition. -/
theorem rowFunctional_two_well_growth {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    ∃ c : ℝ,0<c ∧ ∀ v : ℝ → ℝ,AEMeasurable v unitMeasure →
      (∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) →
      c*min (profileL2Sq v (blockProfile P a b)) (profileL2Sq v (blockProfile P b a))≤
        rowFunctional (twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩) μ v-
          rowFunctional (twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩) μ (blockProfile P a b) := by
  obtain ⟨θ,hθ,hgrowth⟩ := scalarWell_quadratic_growth ha hab hb hμ hEL
  refine ⟨min 1 (2*θ),lt_min (by norm_num) (by positivity),?_⟩
  intro v hv hbound
  have hvb := profile_boundedObservable hv hbound
  have hu := blockMean_mem hv hbound hm
  have hw := blockMean_mem hv hbound (half_compl_mass hP hm)
  have hscalar := hgrowth _ hu _ hw
  have hj := rowFunctional_twoBlock_jensen hP hm a b μ
    ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩ hv hbound
  rw [rowFunctional_blockProfile hP hm,profileL2Sq_two_wells hP hm hvb]
  have hE := profileL2Sq_nonneg v (blockProfile P (blockMean v P) (blockMean v Pᶜ))
  have hd := wellDistanceSq_nonneg a b (blockMean v P) (blockMean v Pᶜ)
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (2*θ)) hE
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (2*θ)) hd
  nlinarith

theorem profileL2Sq_eq_zero_iff {v w : ℝ → ℝ} (hv : BoundedObservable unitMeasure v)
    (hw : BoundedObservable unitMeasure w) : profileL2Sq v w=0 ↔ v =ᵐ[unitMeasure] w := by
  have hdiff : BoundedObservable unitMeasure (fun x => v x-w x) := by
    simpa only [neg_one_mul,sub_eq_add_neg] using hv.add (hw.const_mul (-1))
  have hi : Integrable (fun x => (v x-w x)^2) unitMeasure := by
    simpa only [pow_two] using (hdiff.mul hdiff).integrable
  have he := integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg (v x-w x)) hi
  constructor
  · intro hz
    have h := he.mp hz
    filter_upwards [h] with x hx
    change (v x-w x)^2=0 at hx
    nlinarith
  · intro h
    apply he.mpr
    filter_upwards [h] with x hx
    simp only [hx,sub_self,zero_pow (by omega : 2≠0),Pi.zero_apply]

/-- `thm:twowell` (b): the actual row functional has exactly the two balanced rows as minima. -/
theorem rowFunctional_two_well_minima {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    let B := twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩
    rowFunctional B μ (blockProfile P a b)≤rowFunctional B μ v ∧
      (rowFunctional B μ v=rowFunctional B μ (blockProfile P a b) ↔
        v =ᵐ[unitMeasure] blockProfile P a b ∨ v =ᵐ[unitMeasure] blockProfile P b a) := by
  dsimp only
  obtain ⟨c,hc,hgrowth⟩ := rowFunctional_two_well_growth hP hm ha hab hb hμ hEL
  have h := hgrowth v hv hbound
  have h1 := profileL2Sq_nonneg v (blockProfile P a b)
  have h2 := profileL2Sq_nonneg v (blockProfile P b a)
  have hm0 := le_min h1 h2
  have hp := mul_nonneg hc.le hm0
  refine ⟨by linarith,?_⟩
  constructor
  · intro he
    rw [he,sub_self] at h
    have hz : min (profileL2Sq v (blockProfile P a b)) (profileL2Sq v (blockProfile P b a))=0 := by nlinarith
    have hvb := profile_boundedObservable hv hbound
    rcases le_total (profileL2Sq v (blockProfile P a b)) (profileL2Sq v (blockProfile P b a)) with hle | hle
    · rw [min_eq_left hle] at hz
      exact Or.inl ((profileL2Sq_eq_zero_iff hvb (blockProfile_boundedObservable hP a b)).mp hz)
    · rw [min_eq_right hle] at hz
      exact Or.inr ((profileL2Sq_eq_zero_iff hvb (blockProfile_boundedObservable hP b a)).mp hz)
  · rintro (he | he)
    · exact rowFunctional_congr_ae μ EventuallyEq.rfl he
    · rw [rowFunctional_congr_ae μ EventuallyEq.rfl he,
        rowFunctional_blockProfile hP hm,rowFunctional_blockProfile hP hm,scalarWell_swap a b μ b a]

end SparseLowerTail.Section06

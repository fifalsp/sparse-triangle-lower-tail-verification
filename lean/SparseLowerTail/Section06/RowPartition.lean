import SparseLowerTail.Section06.RowStability
import SparseLowerTail.Section02.TriangleL2

/-! Measurable selection of the two row classes and quantitative control of
codegrees by the two reference profiles. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section02 Section04

private theorem observable_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : BoundedObservable μ f) (hg : BoundedObservable μ g) :
    BoundedObservable μ (fun x => f x-g x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))

/-- Row squared distances are a.e. measurable even for a.e. graphon representatives. -/
theorem rowDistance_aemeasurable (U : Graphon) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    AEMeasurable (fun x => profileL2Sq (fun y => U (x,y)) f) unitMeasure := by
  have hdiff := observable_sub (graphon_boundedObservable U)
    (hf.comp Measure.quasiMeasurePreserving_snd)
  simpa only [profileL2Sq,pow_two] using (hdiff.mul hdiff).integral_left.measurable

/-- Assign each row to a nearest well by an actual measurable set; ties go to
well one. This does not require a pointwise measurable graphon representative. -/
theorem exists_row_partition (U : Graphon) {f g : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) (hg : BoundedObservable unitMeasure g)
    {ε : ℝ} (hclose : ∀ᵐ x ∂unitMeasure,
      min (profileL2Sq (fun y => U (x,y)) f) (profileL2Sq (fun y => U (x,y)) g)≤ε^2) :
    ∃ P : Set ℝ,MeasurableSet P ∧ ∀ᵐ x ∂unitMeasure,
      (x∈P → profileL2Sq (fun y => U (x,y)) f≤ε^2) ∧
      (x∉P → profileL2Sq (fun y => U (x,y)) g≤ε^2) := by
  let d1 := fun x => profileL2Sq (fun y => U (x,y)) f
  let d2 := fun x => profileL2Sq (fun y => U (x,y)) g
  have h1 := rowDistance_aemeasurable U hf
  have h2 := rowDistance_aemeasurable U hg
  let P := {x | h1.mk d1 x≤h2.mk d2 x}
  refine ⟨P,measurableSet_le h1.measurable_mk h2.measurable_mk,?_⟩
  filter_upwards [hclose,h1.ae_eq_mk,h2.ae_eq_mk] with x hx hx1 hx2
  change d1 x=h1.mk d1 x at hx1
  change d2 x=h2.mk d2 x at hx2
  change min (d1 x) (d2 x)≤ε^2 at hx
  have hP : x∈P ↔ d1 x≤d2 x := by simp only [P,mem_setOf_eq,← hx1,← hx2]
  constructor
  · intro hp
    simpa only [min_eq_left (hP.mp hp)] using hx
  · intro hp
    have hg : d2 x≤d1 x := (lt_of_not_ge (mt hP.mpr hp)).le
    simpa only [min_eq_right hg] using hx

/-- Squared Cauchy--Schwarz avoids introducing square roots in the quantitative
row comparison. -/
theorem profile_pair_error_le {v f g : ℝ → ℝ}
    (hv : BoundedObservable unitMeasure v) (hf : BoundedObservable unitMeasure f)
    (hg : BoundedObservable unitMeasure g) (hgb : ∀ᵐ x ∂unitMeasure,g x∈Icc (0:ℝ) 1)
    {ε : ℝ} (hε : 0≤ε) (hd : profileL2Sq v f≤ε^2) :
    |∫ x,(v x-f x)*g x ∂unitMeasure|≤ε := by
  have hcs := integral_mul_sq_le (observable_sub hv hf) hg
  have hg2 : (∫ x,(g x)^2 ∂unitMeasure)≤1 := by
    have hi : Integrable (fun x => (g x)^2) unitMeasure := by
      simpa only [pow_two] using (hg.mul hg).integrable
    have hh := integral_mono_ae hi (integrable_const (μ:=unitMeasure) (1:ℝ)) (by
      filter_upwards [hgb] with x hx
      change (g x)^2≤1
      nlinarith [hx.1,hx.2])
    simpa using hh
  have he0 := profileL2Sq_nonneg v f
  have hprod := mul_le_mul_of_nonneg_left hg2 he0
  change (∫ x,(v x-f x)*g x ∂unitMeasure)^2≤profileL2Sq v f*(∫ x,(g x)^2 ∂unitMeasure) at hcs
  apply (sq_le_sq₀ (abs_nonneg _) hε).mp
  rw [sq_abs]
  nlinarith

/-- Comparing two rows with their reference profiles controls their inner product. -/
theorem profile_inner_error_le {v w f g : ℝ → ℝ}
    (hv : BoundedObservable unitMeasure v) (hw : BoundedObservable unitMeasure w)
    (hf : BoundedObservable unitMeasure f) (hg : BoundedObservable unitMeasure g)
    (hwb : ∀ᵐ x ∂unitMeasure,w x∈Icc (0:ℝ) 1)
    (hfb : ∀ᵐ x ∂unitMeasure,f x∈Icc (0:ℝ) 1)
    {ε : ℝ} (hε : 0≤ε) (hvf : profileL2Sq v f≤ε^2) (hwg : profileL2Sq w g≤ε^2) :
    |(∫ x,v x*w x ∂unitMeasure)-(∫ x,f x*g x ∂unitMeasure)|≤2*ε := by
  have h1 := profile_pair_error_le hv hf hw hwb hε hvf
  have h2 := profile_pair_error_le hw hg hf hfb hε hwg
  have he : (∫ x,v x*w x ∂unitMeasure)-(∫ x,f x*g x ∂unitMeasure)=
      (∫ x,(v x-f x)*w x ∂unitMeasure)+(∫ x,(w x-g x)*f x ∂unitMeasure) := by
    rw [← integral_sub (hv.mul hw).integrable (hf.mul hg).integrable,
      ← integral_add ((observable_sub hv hf).mul hw).integrable ((observable_sub hw hg).mul hf).integrable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end SparseLowerTail.Section06

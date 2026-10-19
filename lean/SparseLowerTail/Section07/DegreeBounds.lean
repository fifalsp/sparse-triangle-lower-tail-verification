import SparseLowerTail.Section07.CenteredKernel
import SparseLowerTail.Section02.MeanGap

/-! The actual degree estimates in `eq:s7degree`. A positive-part quadratic
test proves d≥m/2 directly, so these estimates do not depend on an assumed
spectral diagonal bound. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

theorem rowDegree_mem_Icc_ae (U : Graphon) :
    ∀ᵐ x ∂unitMeasure, rowDegree U x∈Icc (0:ℝ) 1 := by
  filter_upwards [Measure.ae_ae_of_ae_prod U.bounded,
    (graphon_integrable U).prod_right_ae] with x hx hi
  refine ⟨integral_nonneg_of_ae (hx.mono fun y hy => hy.1),?_⟩
  have h := integral_mono_ae hi (integrable_const (1:ℝ)) (hx.mono fun y hy => hy.2)
  simpa [rowDegree] using h

theorem rowTriangle_nonneg_ae (U : Graphon) :
    ∀ᵐ x ∂unitMeasure, 0≤rowTriangle U x := by
  have h : ∀ᵐ p ∂squareMeasure, 0≤U p*codegree U p.1 p.2 := by
    filter_upwards [U.bounded,codegree_mem_Icc_ae U] with p hp hc
    exact mul_nonneg hp.1 hc.1
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  exact integral_nonneg_of_ae hx

/-- The lower degree bound in `lem:spectral` follows directly from positivity
of the centered kernel, with the test f=(m/2−d)₊. -/
theorem penalized_degree_lower (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W) :
    ∀ᵐ x ∂unitMeasure, edgeDensity U/2≤rowDegree U x := by
  let m := edgeDensity U
  let f := fun x => max (m/2-rowDegree U x) 0
  have hm := Section02.edgeDensity_mem_Icc U
  have hf0 (x : ℝ) : 0≤f x := le_max_right _ _
  have hf : BoundedObservable unitMeasure f := by
    refine ⟨(aemeasurable_const.sub (rowDegree_bounded U).measurable).max aemeasurable_const,
      1,by norm_num,?_⟩
    filter_upwards [rowDegree_mem_Icc_ae U] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]
    apply max_le
    · dsimp [m]
      linarith [hm.2,hx.1]
    · norm_num
  have hsq : Integrable (fun x => f x^2) unitMeasure := by
    simpa only [pow_two] using (hf.mul hf).integrable
  have hdf : (∫ x, rowDegree U x*f x ∂unitMeasure)=
      m/2*(∫ x, f x ∂unitMeasure)-(∫ x, f x^2 ∂unitMeasure) := by
    rw [← integral_const_mul,← integral_sub (hf.integrable.const_mul _) hsq]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [f]
      by_cases hx : m/2-rowDegree U x≤0
      · rw [max_eq_right hx]
        ring
      · rw [max_eq_left (le_of_not_ge hx)]
        ring
  have hq := penalized_centeredKernel_positive hSampling hr hγ hU hpen hf.integrable
  rw [centeredKernel_quadratic U hf.integrable,hdf] at hq
  have huq : 0≤∫ p, U p*(f p.1*f p.2) ∂squareMeasure := by
    apply integral_nonneg_of_ae
    filter_upwards [U.bounded] with p hp
    exact mul_nonneg hp.1 (mul_nonneg (hf0 p.1) (hf0 p.2))
  have hi0 : 0≤∫ x, f x ∂unitMeasure := integral_nonneg hf0
  have hi2 : 0≤∫ x, f x^2 ∂unitMeasure := integral_nonneg fun x => sq_nonneg _
  have hprod : (∫ x, f x ∂unitMeasure)*(∫ x, f x^2 ∂unitMeasure)=0 := by
    change 0≤2*(m/2*(∫ x, f x ∂unitMeasure)-(∫ x, f x^2 ∂unitMeasure))*
      (∫ x, f x ∂unitMeasure)-m*(∫ x, f x ∂unitMeasure)^2-_ at hq
    nlinarith [mul_nonneg hi0 hi2]
  have he : ∀ᵐ x ∂unitMeasure, f x=0 := by
    rcases mul_eq_zero.mp hprod with hzero|hzero
    · exact (integral_eq_zero_iff_of_nonneg hf0 hf.integrable).mp hzero
    · have hh := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hsq).mp hzero
      filter_upwards [hh] with x hx
      exact sq_eq_zero_iff.mp hx
  filter_upwards [he] with x hx
  have hh : m/2-rowDegree U x≤f x := le_max_left _ _
  change m/2≤rowDegree U x
  linarith

/-- The upper degree bound uses the actual vertex identity and rooted-triangle
nonnegativity; it holds for every constrained minimizer. -/
theorem minimizer_degree_upper (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, rowDegree U x≤edgeDensity U+graphonMultiplier U r*r^3/2 := by
  have hμ := minimizer_multiplier_pos hr hU
  filter_upwards [minimizer_vertex_degree hSampling hr hU,rowTriangle_nonneg_ae U] with x hx ht
  nlinarith [mul_nonneg hμ.le ht]

/-- All degree-deviation estimates of `eq:s7degree`, with η=μt/2. -/
theorem penalized_degree_estimates (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W) :
    (∀ᵐ x ∂unitMeasure, edgeDensity U/2≤rowDegree U x ∧
      rowDegree U x≤edgeDensity U+graphonMultiplier U r*r^3/2) ∧
    (∫ x, |degreeDeviation U x| ∂unitMeasure)≤graphonMultiplier U r*r^3 ∧
    (∫ x, degreeDeviation U x^2 ∂unitMeasure)≤
      (graphonMultiplier U r*r^3/2)*edgeDensity U/2 := by
  let m := edgeDensity U
  let η := graphonMultiplier U r*r^3/2
  have hη : 0≤η := by
    dsimp [η]
    exact (div_pos (mul_pos (minimizer_multiplier_pos hr hU) (pow_pos hr.1 3)) (by norm_num)).le
  have hlo := penalized_degree_lower hSampling hr hγ hU hpen
  have hhi := minimizer_degree_upper hSampling hr hU
  have hD := degreeDeviation_bounded U
  have hDb : ∀ᵐ x ∂unitMeasure, -m/2≤degreeDeviation U x ∧ degreeDeviation U x≤η := by
    filter_upwards [hlo,hhi] with x hx hy
    dsimp [degreeDeviation,m,η]
    constructor <;> linarith
  refine ⟨hlo.and hhi,?_,?_⟩
  · have hi : Integrable (fun x => 2*η-degreeDeviation U x) unitMeasure :=
      (integrable_const _).sub hD.integrable
    have hb : ∀ᵐ x ∂unitMeasure, |degreeDeviation U x|≤2*η-degreeDeviation U x := by
      filter_upwards [hDb] with x hx
      rcases le_total 0 (degreeDeviation U x) with hz|hz
      · rw [abs_of_nonneg hz]; linarith [hx.2]
      · rw [abs_of_nonpos hz]; linarith
    have hh := integral_mono_ae hD.integrable.norm hi hb
    rw [integral_sub (integrable_const _) hD.integrable,integral_degreeDeviation] at hh
    simp only [integral_const,measureReal_univ_eq_one,one_smul,sub_zero] at hh
    dsimp [η] at hh
    linarith
  · have hs : Integrable (fun x => degreeDeviation U x^2) unitMeasure := by
      simpa only [pow_two] using (hD.mul hD).integrable
    have hi : Integrable (fun x => (η-m/2)*degreeDeviation U x+η*m/2) unitMeasure :=
      (hD.integrable.const_mul _).add (integrable_const _)
    have hb : ∀ᵐ x ∂unitMeasure, degreeDeviation U x^2≤
        (η-m/2)*degreeDeviation U x+η*m/2 := by
      filter_upwards [hDb] with x hx
      nlinarith [mul_nonneg (by linarith [hx.1] : 0≤degreeDeviation U x+m/2)
        (by linarith [hx.2] : 0≤η-degreeDeviation U x)]
    have hh := integral_mono_ae hs hi hb
    rw [integral_add (hD.integrable.const_mul _) (integrable_const _),integral_const_mul,
      integral_degreeDeviation] at hh
    simpa [η,m] using hh

end SparseLowerTail.Section07

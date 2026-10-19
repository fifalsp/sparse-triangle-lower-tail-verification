import SparseLowerTail.Section07.PenalizedQuadratic
import SparseLowerTail.Section07.SmallData

/-! The actual centered graphon kernel used in `lem:spectral`.
Its zero mode and positive quadratic form are derived from the graphon integrals
and the proved penalized second variation. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- The centered kernel K(x,y)=d(x)+d(y)−m−U(x,y). -/
def centeredKernel (U : Graphon) (p : ℝ × ℝ) : ℝ :=
  rowDegree U p.1+rowDegree U p.2-edgeDensity U-U p

/-- The centered degree D=d−m. -/
def degreeDeviation (U : Graphon) (x : ℝ) : ℝ := rowDegree U x-edgeDensity U

theorem centeredKernel_bounded (U : Graphon) : BoundedObservable squareMeasure (centeredKernel U) := by
  convert ((((rowDegree_bounded U).comp Measure.quasiMeasurePreserving_fst).add
    ((rowDegree_bounded U).comp Measure.quasiMeasurePreserving_snd)).add
    (BoundedObservable.const (-edgeDensity U))).add ((graphon_boundedObservable U).const_mul (-1)) using 1
  funext p
  unfold centeredKernel
  ring

theorem degreeDeviation_bounded (U : Graphon) : BoundedObservable unitMeasure (degreeDeviation U) := by
  convert (rowDegree_bounded U).add (BoundedObservable.const (-edgeDensity U)) using 1

theorem centeredKernel_symmetric (U : Graphon) :
    ∀ᵐ p ∂squareMeasure, centeredKernel U p.swap=centeredKernel U p := by
  filter_upwards [U.symmetric] with p hp
  unfold centeredKernel
  simp only [Prod.fst_swap,Prod.snd_swap,hp]
  ring

theorem integral_degreeDeviation (U : Graphon) : ∫ x, degreeDeviation U x ∂unitMeasure=0 := by
  unfold degreeDeviation
  rw [integral_sub (rowDegree_bounded U).integrable (integrable_const _),integral_rowDegree]
  simp

/-- The constant function belongs to the null space of the actual kernel. -/
theorem centeredKernel_row_zero (U : Graphon) :
    ∀ᵐ x ∂unitMeasure, (∫ y, centeredKernel U (x,y) ∂unitMeasure)=0 := by
  filter_upwards [(graphon_integrable U).prod_right_ae] with x hx
  have hi : Integrable (fun y => rowDegree U x+rowDegree U y-edgeDensity U) unitMeasure :=
    ((integrable_const _).add (rowDegree_bounded U).integrable).sub (integrable_const _)
  have hi' : Integrable (fun y => rowDegree U x+rowDegree U y) unitMeasure :=
    (integrable_const _).add (rowDegree_bounded U).integrable
  change (∫ y, (rowDegree U x+rowDegree U y-edgeDensity U)-U (x,y) ∂unitMeasure)=0
  rw [integral_sub hi hx,integral_sub hi'
    (integrable_const _),integral_add (integrable_const _) (rowDegree_bounded U).integrable,
    integral_rowDegree]
  simp [rowDegree]

private theorem bounded_mul_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : BoundedObservable μ f) (hg : Integrable g μ) :
    Integrable (fun x => f x*g x) μ := by
  obtain ⟨K,_,hK⟩ := hf.bound
  exact hg.bdd_mul' hf.measurable.aestronglyMeasurable hK

/-- Fubini for a possibly unbounded integrable vertex test. -/
theorem integral_graphon_vertex_test (U : Graphon) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    (∫ p, U p*f p.1 ∂squareMeasure)=∫ x, rowDegree U x*f x ∂unitMeasure := by
  have hi : Integrable (fun p : ℝ × ℝ => f p.1) squareMeasure := by
    simpa only [mul_one] using hf.mul_prod (integrable_const (1:ℝ))
  rw [integral_prod _ (bounded_mul_integrable (graphon_boundedObservable U) hi)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [integral_mul_const]
    rfl

theorem integral_graphon_vertex_test_right (U : Graphon) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    (∫ p, U p*f p.2 ∂squareMeasure)=∫ x, rowDegree U x*f x ∂unitMeasure := by
  calc
    _ = ∫ p, U p.swap*f p.swap.1 ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [U.symmetric] with p hp
      simp only [Prod.fst_swap,hp]
    _ = ∫ p, U p*f p.1 ∂squareMeasure :=
      Measure.measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding (fun p => U p*f p.1)
    _ = _ := integral_graphon_vertex_test U hf

/-- Explicit expansion of the quadratic form of the centered kernel. -/
theorem centeredKernel_quadratic (U : Graphon) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    (∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure)=
      2*(∫ x, rowDegree U x*f x ∂unitMeasure)*(∫ x, f x ∂unitMeasure)-
      edgeDensity U*(∫ x, f x ∂unitMeasure)^2-
      (∫ p, U p*(f p.1*f p.2) ∂squareMeasure) := by
  have hd := bounded_mul_integrable (rowDegree_bounded U) hf
  have h₁ := hd.mul_prod hf
  have h₂ := hf.mul_prod hd
  have h₃ := (hf.mul_prod hf).const_mul (edgeDensity U)
  have h₄ := graphon_quadratic_integrable U hf
  have h₁₂ : Integrable (fun p : ℝ × ℝ => (rowDegree U p.1*f p.1)*f p.2+
      f p.1*(rowDegree U p.2*f p.2)) squareMeasure := h₁.add h₂
  have h₁₂₃ : Integrable (fun p : ℝ × ℝ => (rowDegree U p.1*f p.1)*f p.2+
      f p.1*(rowDegree U p.2*f p.2)-edgeDensity U*(f p.1*f p.2)) squareMeasure := h₁₂.sub h₃
  calc
    _ = ∫ p, ((rowDegree U p.1*f p.1)*f p.2+f p.1*(rowDegree U p.2*f p.2)-
        edgeDensity U*(f p.1*f p.2))-U p*(f p.1*f p.2) ∂squareMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by unfold centeredKernel; ring
    _ = _ := by
      rw [integral_sub h₁₂₃ h₄,integral_sub h₁₂ h₃,integral_add h₁ h₂,
        integral_const_mul,integral_prod_mul,
        integral_prod_mul (fun x => rowDegree U x*f x) f,
        integral_prod_mul f (fun x => rowDegree U x*f x)]
      ring

/-- Centering a vertex test transforms the U-form into the negative K-form. -/
theorem centeredKernel_quadratic_eq_neg_centered (U : Graphon) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    (∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure)=
      -(∫ p, U p*((f p.1-(∫ x, f x ∂unitMeasure))*(f p.2-(∫ x, f x ∂unitMeasure)))
        ∂squareMeasure) := by
  let m := ∫ x, f x ∂unitMeasure
  have hx : Integrable (fun p : ℝ × ℝ => U p*f p.1) squareMeasure := by
    apply bounded_mul_integrable (graphon_boundedObservable U)
    simpa only [mul_one] using hf.mul_prod (integrable_const (1:ℝ))
  have hy : Integrable (fun p : ℝ × ℝ => U p*f p.2) squareMeasure := by
    apply bounded_mul_integrable (graphon_boundedObservable U)
    simpa only [one_mul] using (integrable_const (1:ℝ)).mul_prod hf
  have hq := graphon_quadratic_integrable U hf
  have he : (∫ p, U p*((f p.1-m)*(f p.2-m)) ∂squareMeasure)=
      (∫ p, U p*(f p.1*f p.2) ∂squareMeasure)-
      m*(∫ p, U p*f p.1 ∂squareMeasure)-m*(∫ p, U p*f p.2 ∂squareMeasure)+
      m^2*edgeDensity U := by
    have h₁ : Integrable (fun p => U p*(f p.1*f p.2)-m*(U p*f p.1)) squareMeasure := hq.sub (hx.const_mul m)
    have h₂ : Integrable (fun p => U p*(f p.1*f p.2)-m*(U p*f p.1)-m*(U p*f p.2))
        squareMeasure := h₁.sub (hy.const_mul m)
    calc
      _ = ∫ p, ((U p*(f p.1*f p.2)-m*(U p*f p.1))-m*(U p*f p.2))+m^2*U p
          ∂squareMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by ring
      _ = _ := by
        rw [integral_add h₂ ((graphon_integrable U).const_mul _),integral_sub h₁ (hy.const_mul _),
          integral_sub hq (hx.const_mul _),integral_const_mul,integral_const_mul,integral_const_mul]
        rfl
  rw [he,integral_graphon_vertex_test U hf,integral_graphon_vertex_test_right U hf,
    centeredKernel_quadratic U hf]
  dsimp [m]
  ring

/-- Positivity of the actual centered kernel, the first assertion of `lem:spectral`. -/
theorem penalized_centeredKernel_positive (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W)
    {f : ℝ → ℝ} (hf : Integrable f unitMeasure) :
    0≤(∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure) := by
  rw [centeredKernel_quadratic_eq_neg_centered U hf]
  have hmean : (∫ x, f x-(∫ y, f y ∂unitMeasure) ∂unitMeasure)=0 := by
    rw [integral_sub hf (integrable_const _)]
    simp
  have h := penalized_quadratic_nonpos_integrable hSampling hr hγ hU hpen
    (hf.sub (integrable_const _)) hmean
  dsimp only [Pi.sub_apply] at h
  linarith

end SparseLowerTail.Section07

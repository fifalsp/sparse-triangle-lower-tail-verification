import SparseLowerTail.Section07.KernelActionCalculus

/-! Actual action and square-kernel estimates for the spectral remainder.
These provide the L² estimates used in the seven codegree error terms. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

theorem minimizer_eigenfunction_bounded (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U)) {i : ℕ} (hi : 0<S.eigenvalue i) :
    BoundedObservable unitMeasure (S.eigenfunction i) :=
  ⟨(S.eigenfunction_measurable i).aemeasurable,
    Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue i),
    Real.sqrt_nonneg _,minimizer_eigenfunction_bound hSampling hr hU S hi⟩

theorem spectralRemainder_bounded {U : Graphon}
    (S : KernelSpectralExpansion (centeredKernel U))
    (hψ : BoundedObservable unitMeasure (S.eigenfunction 0)) :
    BoundedObservable squareMeasure (spectralRemainder U S) := by
  convert (centeredKernel_bounded U).add
    (((hψ.comp Measure.quasiMeasurePreserving_fst).mul
      (hψ.comp Measure.quasiMeasurePreserving_snd)).const_mul (-S.eigenvalue 0)) using 1
  funext p
  dsimp [spectralRemainder]
  ring

theorem spectralRemainder_symmetric (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    ∀ᵐ p ∂squareMeasure, spectralRemainder U S p.swap=spectralRemainder U S p := by
  filter_upwards [centeredKernel_symmetric U] with p hp
  dsimp only [spectralRemainder,Prod.fst_swap,Prod.snd_swap]
  rw [hp]
  ring

/-- Bounded kernels have bounded measurable sections almost everywhere. -/
theorem boundedObservable_sections {K : ℝ × ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) :
    ∀ᵐ x ∂unitMeasure, BoundedObservable unitMeasure (fun y => K (x,y)) := by
  obtain ⟨C,hC,hbound⟩ := hK.bound
  filter_upwards [hK.integrable.prod_right_ae,Measure.ae_ae_of_ae_prod hbound] with x hx hbx
  exact ⟨hx.aestronglyMeasurable.aemeasurable,C,hC,hbx⟩

/-- The actual residual action has L² norm at most s times the input norm. -/
theorem spectralRemainder_action_sq_le (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U))
    (hψ : BoundedObservable unitMeasure (S.eigenfunction 0))
    {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    (∫ x, kernelAction (spectralRemainder U S) f x^2 ∂unitMeasure)≤
      (edgeDensity U-S.eigenvalue 0)^2*(∫ x, f x^2 ∂unitMeasure) := by
  apply kernelAction_sq_le (spectralRemainder_bounded S hψ) (spectralRemainder_symmetric U S)
    (sub_nonneg.mpr (centeredEigenvalue_le_mean U S 0)) _ _ hf
  · intro g hg
    obtain ⟨C,_,hC⟩ := hg.bound
    exact spectralRemainder_positive U S g
      (MemLp.of_bound hg.measurable.aestronglyMeasurable C hC)
  · intro g hg
    exact spectralRemainder_quadratic_upper U S hg

def residualSquare (U : Graphon) (S : KernelSpectralExpansion (centeredKernel U))
    (x y : ℝ) : ℝ := ∫ z, spectralRemainder U S (x,z)*spectralRemainder U S (y,z) ∂unitMeasure

/-- The square-kernel row is the actual residual action of the residual row. -/
theorem residualSquare_eq_action (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (x y : ℝ) :
    residualSquare U S x y=kernelAction (spectralRemainder U S)
      (fun z => spectralRemainder U S (x,z)) y := by
  apply integral_congr_ae
  exact Eventually.of_forall fun z => mul_comm _ _

/-- The square-kernel row norm bound used in the final codegree error term. -/
theorem minimizer_residualSquare_row_bound (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U)) (hev : 0<S.eigenvalue 0) :
    ∀ᵐ x ∂unitMeasure,
      (∫ y, residualSquare U S x y^2 ∂unitMeasure)≤
        (edgeDensity U-S.eigenvalue 0)^2*
          ((edgeDensity U-S.eigenvalue 0)*(edgeDensity U+graphonMultiplier U r*r^3)) := by
  have hψ := minimizer_eigenfunction_bounded hSampling hr hU S hev
  filter_upwards [boundedObservable_sections (spectralRemainder_bounded S hψ),
    minimizer_spectralRemainder_row_bound hSampling hr hU S] with x hx hrow
  simp_rw [residualSquare_eq_action]
  exact (spectralRemainder_action_sq_le U S hψ hx).trans
    (mul_le_mul_of_nonneg_left hrow.2.2.2 (sq_nonneg _))

/-- Pointwise Cauchy--Schwarz with the actual residual row estimate. -/
theorem minimizer_residualAction_bound (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U))
    {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure) :
    ∀ᵐ x ∂unitMeasure, |kernelAction (spectralRemainder U S) f x|≤
      Real.sqrt ((edgeDensity U-S.eigenvalue 0)*(edgeDensity U+graphonMultiplier U r*r^3))*
        Real.sqrt (∫ y, f y^2 ∂unitMeasure) := by
  filter_upwards [minimizer_spectralRemainder_row_bound hSampling hr hU S] with x hx
  exact (abs_integral_mul_le_L2 hx.2.2.1 hf).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx.2.2.2) (Real.sqrt_nonneg _))

end SparseLowerTail.Section07

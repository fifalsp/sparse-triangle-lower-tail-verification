import SparseLowerTail.Section07.SpectralDiagonal
import SparseLowerTail.Section07.CenteredCodegree

/-! Actual eigenfunction consequences of the graphon spectral diagonal bound. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section07
open Section04

/-- The centered kernel sends every integrable test to a function of mean zero. -/
theorem integral_centeredAction (U : Graphon) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) : (∫ x, centeredAction U f x ∂unitMeasure)=0 := by
  obtain ⟨C,_,hC⟩ := (centeredKernel_bounded U).bound
  have hfy : Integrable (fun p : ℝ × ℝ => f p.2) squareMeasure := by
    simpa only [one_mul] using (integrable_const (1:ℝ)).mul_prod hf
  have hfx : Integrable (fun p : ℝ × ℝ => f p.1) squareMeasure := by
    simpa only [mul_one] using hf.mul_prod (integrable_const (1:ℝ))
  have hi := hfy.bdd_mul' (centeredKernel_bounded U).measurable.aestronglyMeasurable hC
  have hi' := hfx.bdd_mul' (centeredKernel_bounded U).measurable.aestronglyMeasurable hC
  change (∫ x, ∫ y, centeredKernel U (x,y)*f y ∂unitMeasure ∂unitMeasure)=0
  rw [← integral_prod _ hi]
  calc
    _ = ∫ p, centeredKernel U p.swap*f p.swap.1 ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [centeredKernel_symmetric U] with p hp
      simp only [Prod.fst_swap,hp]
    _ = ∫ p, centeredKernel U p*f p.1 ∂squareMeasure :=
      Measure.measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
        (fun p => centeredKernel U p*f p.1)
    _ = 0 := by
      rw [integral_prod _ hi']
      apply integral_eq_zero_of_ae
      filter_upwards [centeredKernel_row_zero U] with x hx
      rw [integral_mul_const,hx,zero_mul]
      rfl

/-- Every eigenfunction with positive eigenvalue has mean zero. -/
theorem centeredEigenfunction_mean_zero (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) {i : ℕ} (hi : 0<S.eigenvalue i) :
    (∫ x, S.eigenfunction i x ∂unitMeasure)=0 := by
  have he := integral_congr_ae (S.eigen_equation i)
  change (∫ x, centeredAction U (S.eigenfunction i) x ∂unitMeasure)=_ at he
  rw [integral_centeredAction U (MemLp.integrable (by norm_num) (S.eigenfunction_memLp i)),
    integral_const_mul] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (ne_of_gt hi)

/-- Each rank-one diagonal is bounded by the actual degree diagonal. -/
theorem centeredEigenfunction_diagonal_bound (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (i : ℕ) :
    ∀ᵐ x ∂unitMeasure, S.eigenvalue i*(S.eigenfunction i x)^2≤2*rowDegree U x-edgeDensity U := by
  filter_upwards [centeredKernel_diagonal_bound U S] with x hx
  exact (Summable.le_tsum hx.1 i (fun j _ => mul_nonneg (S.eigenvalue_nonneg j) (sq_nonneg _))).trans hx.2.2

/-- The uniform eigenfunction bound used in `eq:s7Rrow`, with A=m+μt. -/
theorem minimizer_eigenfunction_bound (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U)) {i : ℕ} (hi : 0<S.eigenvalue i) :
    ∀ᵐ x ∂unitMeasure, |S.eigenfunction i x|≤
      Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue i) := by
  filter_upwards [centeredEigenfunction_diagonal_bound U S i,
    minimizer_degree_upper hSampling hr hU] with x hx hd
  have hs : (S.eigenfunction i x)^2≤
      (edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue i := by
    apply (le_div_iff₀ hi).mpr
    nlinarith
  have hnonneg : 0≤(edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue i :=
    (sq_nonneg _).trans hs
  exact (Real.le_sqrt (abs_nonneg _) hnonneg).mpr (by simpa only [sq_abs] using hs)

end SparseLowerTail.Section07

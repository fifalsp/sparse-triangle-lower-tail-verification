import SparseLowerTail.Section07.SpectralTail

/-! The operator norm estimate T_K≤mI, proved from the actual L² kernel
convergence and the internally proved trace bound. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SparseLowerTail.Section07
open Section04

/-- Cauchy--Schwarz for real L² functions, in square-root integral form. -/
theorem abs_integral_mul_le_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x*g x ∂μ|≤Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (∫ x, g x^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hg)
  have hn := norm_integral_le_integral_norm (fun x => f x*g x) (μ := μ)
  simp only [Real.norm_eq_abs,abs_mul] at hn
  have h' : (∫ x, |f x| *|g x| ∂μ)≤
      Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (∫ x, g x^2 ∂μ) := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] using h
  exact hn.trans h'

private theorem bounded_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : BoundedObservable μ f) : MemLp f 2 μ := by
  obtain ⟨C,_,hC⟩ := hf.bound
  exact MemLp.of_bound hf.measurable.aestronglyMeasurable C hC

/-- Spectral partial kernels genuinely belong to L² of the unit square. -/
theorem spectralPartial_memLp {K : ℝ × ℝ → ℝ} (S : KernelSpectralExpansion K) (N : ℕ) :
    MemLp (spectralPartial S.eigenvalue S.eigenfunction N) 2 squareMeasure := by
  apply memLp_finset_sum
  intro i hi
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => S.eigenfunction i p.1*S.eigenfunction i p.2) squareMeasure :=
    (((S.eigenfunction_measurable i).comp measurable_fst).mul
      ((S.eigenfunction_measurable i).comp measurable_snd)).aestronglyMeasurable
  have hsq : Integrable (fun p : ℝ × ℝ => (S.eigenfunction i p.1*S.eigenfunction i p.2)^2) squareMeasure := by
    convert (S.eigenfunction_memLp i).integrable_sq.mul_prod (S.eigenfunction_memLp i).integrable_sq using 1
    funext p
    ring
  convert ((memLp_two_iff_integrable_sq hmeas).mpr hsq).const_mul (S.eigenvalue i) using 1
  funext p
  ring

/-- Kernel L² convergence implies convergence of its genuine quadratic forms. -/
theorem spectralPartial_quadratic_tendsto (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    Tendsto (fun N => ∫ p, spectralPartial S.eigenvalue S.eigenfunction N p*(f p.1*f p.2)
      ∂squareMeasure) atTop (𝓝 (∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure)) := by
  have hp := (hf.comp Measure.quasiMeasurePreserving_fst).mul
    (hf.comp Measure.quasiMeasurePreserving_snd)
  have hK := bounded_memLp (centeredKernel_bounded U)
  have hg := bounded_memLp hp
  have hconv : Tendsto (fun N => Real.sqrt (∫ p,
      (centeredKernel U p-spectralPartial S.eigenvalue S.eigenfunction N p)^2 ∂squareMeasure)*
      Real.sqrt (∫ p, (f p.1*f p.2)^2 ∂squareMeasure)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,zero_mul] using
      (Real.continuous_sqrt.tendsto 0 |>.comp S.kernel_convergence).mul_const
        (Real.sqrt (∫ p, (f p.1*f p.2)^2 ∂squareMeasure))
  have hbound (N : ℕ) : |(∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure)-
      (∫ p, spectralPartial S.eigenvalue S.eigenfunction N p*(f p.1*f p.2) ∂squareMeasure)|≤
      Real.sqrt (∫ p, (centeredKernel U p-spectralPartial S.eigenvalue S.eigenfunction N p)^2
        ∂squareMeasure)*Real.sqrt (∫ p, (f p.1*f p.2)^2 ∂squareMeasure) := by
    have hiK : Integrable (fun p => centeredKernel U p*(f p.1*f p.2)) squareMeasure := hK.integrable_mul hg
    have hiN : Integrable (fun p => spectralPartial S.eigenvalue S.eigenfunction N p*(f p.1*f p.2)) squareMeasure :=
      (spectralPartial_memLp S N).integrable_mul hg
    rw [← integral_sub hiK hiN]
    have he : (fun p => centeredKernel U p*(f p.1*f p.2)-
        spectralPartial S.eigenvalue S.eigenfunction N p*(f p.1*f p.2))=
        (fun p => (centeredKernel U p-spectralPartial S.eigenvalue S.eigenfunction N p)*(f p.1*f p.2)) := by
      funext p; ring
    rw [he]
    exact abs_integral_mul_le_L2 (hK.sub (spectralPartial_memLp S N)) hg
  have habs := squeeze_zero (fun N => abs_nonneg _) hbound hconv
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  simpa only [Real.norm_eq_abs,abs_sub_comm] using habs

/-- Each squared spectral coefficient is bounded by the test's L² mass. -/
theorem spectral_coefficient_sq_le {K : ℝ × ℝ → ℝ} (S : KernelSpectralExpansion K)
    (i : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure) :
    (∫ x, S.eigenfunction i x*f x ∂unitMeasure)^2≤∫ x, f x^2 ∂unitMeasure := by
  have hn : (∫ x, S.eigenfunction i x^2 ∂unitMeasure)=1 := by
    simpa only [pow_two,if_pos rfl] using S.orthonormal_integral i i
  have h := abs_integral_mul_le_L2 (S.eigenfunction_memLp i) hf
  rw [hn,Real.sqrt_one,one_mul] at h
  have hnonneg : 0≤∫ x, f x^2 ∂unitMeasure := integral_nonneg fun x => sq_nonneg _
  have hsqrt := Real.sq_sqrt hnonneg
  have hh := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr h
  simpa only [sq_abs,hsqrt] using hh

/-- The graphon-specific norm bound T_K≤mI on bounded tests, enough for the
paper's degree deviation D. No operator-norm bound is assumed externally. -/
theorem centeredKernel_quadratic_upper (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    (∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure)≤
      edgeDensity U*(∫ x, f x^2 ∂unitMeasure) := by
  apply le_of_tendsto (spectralPartial_quadratic_tendsto U S hf)
  apply Eventually.of_forall
  intro N
  rw [spectralPartial_quadratic S N hf]
  calc
    _ ≤ ∑ i∈Finset.range N, S.eigenvalue i*(∫ x, f x^2 ∂unitMeasure) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (spectral_coefficient_sq_le S i (bounded_memLp hf))
        (S.eigenvalue_nonneg i)
    _ = (∑ i∈Finset.range N, S.eigenvalue i)*(∫ x, f x^2 ∂unitMeasure) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (spectral_partial_trace_bound U S N)
      (integral_nonneg fun x => sq_nonneg _)

end SparseLowerTail.Section07

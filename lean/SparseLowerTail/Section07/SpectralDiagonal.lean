import SparseLowerTail.Section07.ClassicalKernelSpectrum
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! The graphon-specific diagonal and trace bounds of `lem:spectral`.
Only the general classical spectrum is supplied as data. The finite-rank test,
Lebesgue differentiation, and graphon estimates are proved here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SparseLowerTail.Section07
open Section04

private theorem bounded_times_integrable {f g : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) (hg : Integrable g unitMeasure) :
    Integrable (fun x => g x*f x) unitMeasure := by
  obtain ⟨C,_,hC⟩ := hf.bound
  simpa only [mul_comm] using hg.bdd_mul' hf.measurable.aestronglyMeasurable hC

/-- The exact quadratic form of a finite spectral kernel. -/
theorem spectralPartial_quadratic {K : ℝ × ℝ → ℝ} (S : KernelSpectralExpansion K)
    (N : ℕ) {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    (∫ p, spectralPartial S.eigenvalue S.eigenfunction N p*(f p.1*f p.2) ∂squareMeasure)=
      ∑ i∈Finset.range N, S.eigenvalue i*(∫ x, S.eigenfunction i x*f x ∂unitMeasure)^2 := by
  have hi (i : ℕ) : Integrable (fun x => S.eigenfunction i x*f x) unitMeasure :=
    bounded_times_integrable hf (MemLp.integrable (by norm_num) (S.eigenfunction_memLp i))
  have hip (i : ℕ) : Integrable (fun p : ℝ × ℝ => S.eigenvalue i*
      ((S.eigenfunction i p.1*f p.1)*(S.eigenfunction i p.2*f p.2))) squareMeasure :=
    ((hi i).mul_prod (hi i)).const_mul _
  calc
    _ = ∫ p, ∑ i∈Finset.range N, S.eigenvalue i*
        ((S.eigenfunction i p.1*f p.1)*(S.eigenfunction i p.2*f p.2)) ∂squareMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only
        unfold spectralPartial
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => hip i)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul,integral_prod_mul (fun x => S.eigenfunction i x*f x)
        (fun x => S.eigenfunction i x*f x)]
      ring

private theorem spectralPartial_quadratic_integrable {K : ℝ × ℝ → ℝ}
    (S : KernelSpectralExpansion K) (N : ℕ) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    Integrable (fun p => spectralPartial S.eigenvalue S.eigenfunction N p*(f p.1*f p.2)) squareMeasure := by
  have hi (i : ℕ) : Integrable (fun x => S.eigenfunction i x*f x) unitMeasure :=
    bounded_times_integrable hf (MemLp.integrable (by norm_num) (S.eigenfunction_memLp i))
  have hh := integrable_finset_sum (Finset.range N) (fun i _ => ((hi i).mul_prod (hi i)).const_mul (S.eigenvalue i))
  convert hh using 1
  funext p
  unfold spectralPartial
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Domination of each finite spectral quadratic form by the centered form. -/
theorem spectralPartial_quadratic_le (U : Graphon) (S : KernelSpectralExpansion (centeredKernel U))
    (N : ℕ) {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    (∑ i∈Finset.range N, S.eigenvalue i*(∫ x, S.eigenfunction i x*f x ∂unitMeasure)^2)≤
      (∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure) := by
  obtain ⟨C,_,hC⟩ := hf.bound
  have hp := S.residual_positive N f (MemLp.of_bound hf.measurable.aestronglyMeasurable C hC)
  obtain ⟨B,_,hB⟩ := (centeredKernel_bounded U).bound
  have hk : Integrable (fun p => centeredKernel U p*(f p.1*f p.2)) squareMeasure :=
    (hf.integrable.mul_prod hf.integrable).bdd_mul'
      (centeredKernel_bounded U).measurable.aestronglyMeasurable hB
  have he : (∫ p, (centeredKernel U p-spectralPartial S.eigenvalue S.eigenfunction N p)*
      (f p.1*f p.2) ∂squareMeasure)=
      (∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure)-
      (∫ p, spectralPartial S.eigenvalue S.eigenfunction N p*(f p.1*f p.2) ∂squareMeasure) := by
    rw [← integral_sub hk (spectralPartial_quadratic_integrable S N hf)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by ring
  rw [he,spectralPartial_quadratic S N hf] at hp
  linarith

/-- The finite-rank cell inequality from `lem:spectral`, before normalization. -/
theorem spectral_cell_bound (U : Graphon) (S : KernelSpectralExpansion (centeredKernel U))
    (N : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∑ i∈Finset.range N, S.eigenvalue i*(∫ x in A, S.eigenfunction i x ∂unitMeasure)^2)≤
      2*(∫ x in A, rowDegree U x ∂unitMeasure)*unitMeasure.real A-
      edgeDensity U*(unitMeasure.real A)^2 := by
  let f := A.indicator (fun _ : ℝ => (1:ℝ))
  have hf : BoundedObservable unitMeasure f := by
    refine ⟨(measurable_const.indicator hA).aemeasurable,1,by norm_num,?_⟩
    exact Eventually.of_forall fun x => by
      by_cases hx : x∈A <;> simp [f,hx]
  have hi (g : ℝ → ℝ) : (∫ x, g x*f x ∂unitMeasure)=∫ x in A, g x ∂unitMeasure := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp [f]
      by_cases hx : x∈A <;> simp [hx]
  have hfint : (∫ x, f x ∂unitMeasure)=unitMeasure.real A := by
    rw [show f=A.indicator (fun _ : ℝ => (1:ℝ)) from rfl,integral_indicator hA]
    simp
  have hp := spectralPartial_quadratic_le U S N hf
  rw [centeredKernel_quadratic U hf.integrable,hfint,hi (rowDegree U)] at hp
  simp_rw [hi] at hp
  have hu : 0≤∫ p, U p*(f p.1*f p.2) ∂squareMeasure := by
    apply integral_nonneg_of_ae
    filter_upwards [U.bounded] with p hx
    apply mul_nonneg hx.1
    apply mul_nonneg <;> apply Set.indicator_nonneg <;> intro x hx <;> norm_num
  linarith

/-- The normalized finite-rank inequality holds on every positive-measure cell. -/
theorem spectral_average_bound (U : Graphon) (S : KernelSpectralExpansion (centeredKernel U))
    (N : ℕ) {A : Set ℝ} (hA : MeasurableSet A) (hm : 0<unitMeasure.real A) :
    (∑ i∈Finset.range N, S.eigenvalue i*(⨍ x in A, S.eigenfunction i x ∂unitMeasure)^2)≤
      2*(⨍ x in A, rowDegree U x ∂unitMeasure)-edgeDensity U := by
  have hh := (div_le_div_iff_of_pos_right (sq_pos_of_pos hm)).mpr (spectral_cell_bound U S N hA)
  have hav (f : ℝ → ℝ) : (⨍ x in A, f x ∂unitMeasure)=
      (∫ x in A, f x ∂unitMeasure)/unitMeasure.real A := by
    rw [setAverage_eq]
    simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
  simp_rw [hav]
  have he : (∑ i∈Finset.range N, S.eigenvalue i*(∫ x in A, S.eigenfunction i x ∂unitMeasure)^2)/
      (unitMeasure.real A)^2=
      ∑ i∈Finset.range N, S.eigenvalue i*((∫ x in A, S.eigenfunction i x ∂unitMeasure)/unitMeasure.real A)^2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hh
  convert hh using 1
  field_simp

/-- Lebesgue differentiation converts the finite-cell inequality to the
pointwise finite spectral diagonal bound. This uses mathlib's Vitali theorem. -/
theorem spectral_partial_diagonal_bound (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (N : ℕ) :
    ∀ᵐ x ∂unitMeasure, (∑ i∈Finset.range N, S.eigenvalue i*(S.eigenfunction i x)^2)≤
      2*rowDegree U x-edgeDensity U := by
  let v := Besicovitch.vitaliFamily unitMeasure
  have he : ∀ i : ℕ, ∀ᵐ x ∂unitMeasure,
      Tendsto (fun A => ⨍ y in A, S.eigenfunction i y ∂unitMeasure) (v.filterAt x)
        (𝓝 (S.eigenfunction i x)) := fun i =>
    v.ae_tendsto_average (MemLp.integrable (by norm_num) (S.eigenfunction_memLp i)).locallyIntegrable
  have hd := v.ae_tendsto_average (rowDegree_bounded U).integrable.locallyIntegrable
  filter_upwards [ae_all_iff.mpr he,hd,v.ae_eventually_measure_pos] with x hx hdx hpos
  have hl : Tendsto
      (fun A => ∑ i∈Finset.range N, S.eigenvalue i*(⨍ y in A, S.eigenfunction i y ∂unitMeasure)^2)
      (v.filterAt x) (𝓝 (∑ i∈Finset.range N, S.eigenvalue i*(S.eigenfunction i x)^2)) := by
    apply tendsto_finset_sum
    intro i hi
    exact ((hx i).pow 2).const_mul _
  have hr := (hdx.const_mul 2).sub_const (edgeDensity U)
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [hpos,v.eventually_filterAt_measurableSet x] with A hA hmeas
  exact spectral_average_bound U S N hmeas
    (ENNReal.toReal_pos hA.ne' (measure_ne_top unitMeasure A))

/-- Integration gives the finite-rank trace bound without assuming trace class. -/
theorem spectral_partial_trace_bound (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (N : ℕ) :
    (∑ i∈Finset.range N, S.eigenvalue i)≤edgeDensity U := by
  have hi (i : ℕ) : Integrable (fun x => S.eigenvalue i*(S.eigenfunction i x)^2) unitMeasure :=
    (S.eigenfunction_memLp i).integrable_sq.const_mul _
  have hh := integral_mono_ae (integrable_finset_sum _ (fun i _ => hi i))
    (((rowDegree_bounded U).integrable.const_mul 2).sub (integrable_const (edgeDensity U)))
    (spectral_partial_diagonal_bound U S N)
  rw [integral_finset_sum _ (fun i _ => hi i)] at hh
  have hnorm (i : ℕ) : (∫ x, (S.eigenfunction i x)^2 ∂unitMeasure)=1 := by
    simpa only [pow_two,if_pos rfl] using S.orthonormal_integral i i
  simp_rw [integral_const_mul,hnorm,mul_one] at hh
  dsimp only [Pi.sub_apply] at hh
  rw [integral_sub ((rowDegree_bounded U).integrable.const_mul 2) (integrable_const _),
    integral_const_mul,integral_rowDegree] at hh
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at hh
  linarith

/-- The graphon-specific trace-class conclusion and trace upper bound. -/
theorem centeredKernel_trace_bound (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    Summable S.eigenvalue ∧ (∑' i, S.eigenvalue i)≤edgeDensity U := by
  have hs := summable_of_sum_range_le S.eigenvalue_nonneg (spectral_partial_trace_bound U S)
  exact ⟨hs,hs.tsum_le_of_sum_range_le (spectral_partial_trace_bound U S)⟩

/-- The canonical diagonal reconstructed from the nonnegative spectral series. -/
def spectralDiagonal {K : ℝ × ℝ → ℝ} (S : KernelSpectralExpansion K) (x : ℝ) : ℝ :=
  ∑' i, S.eigenvalue i*(S.eigenfunction i x)^2

/-- The full diagonal bound `eq:s7diag`, including actual summability. -/
theorem centeredKernel_diagonal_bound (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    ∀ᵐ x ∂unitMeasure,
      Summable (fun i => S.eigenvalue i*(S.eigenfunction i x)^2) ∧
      0≤spectralDiagonal S x ∧ spectralDiagonal S x≤2*rowDegree U x-edgeDensity U := by
  filter_upwards [ae_all_iff.mpr (spectral_partial_diagonal_bound U S)] with x hx
  have hn (i : ℕ) : 0≤S.eigenvalue i*(S.eigenfunction i x)^2 :=
    mul_nonneg (S.eigenvalue_nonneg i) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hn hx,tsum_nonneg hn,Real.tsum_le_of_sum_range_le hn hx⟩

end SparseLowerTail.Section07

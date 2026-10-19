import SparseLowerTail.Section07.EigenfunctionBlocks

/-! The actual rank-one spectral remainder and the row bound `eq:s7Rrow`.
The generic rowwise Parseval theorem is used only through the explicit classical
spectral data; all trace, diagonal, and graphon-dependent bounds are proved here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace SparseLowerTail.Section07
open Section04

def spectralRemainder (U : Graphon) (S : KernelSpectralExpansion (centeredKernel U))
    (p : ℝ × ℝ) : ℝ :=
  centeredKernel U p-S.eigenvalue 0*S.eigenfunction 0 p.1*S.eigenfunction 0 p.2

def residualDiagonal {U : Graphon} (S : KernelSpectralExpansion (centeredKernel U))
    (x : ℝ) : ℝ := ∑' i, S.eigenvalue (i+1)*(S.eigenfunction (i+1) x)^2

theorem spectralRemainder_positive (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    PositiveKernelForm (spectralRemainder U S) := by
  simpa [spectralRemainder,spectralPartial] using S.residual_positive 1

theorem residualDiagonal_bound (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    ∀ᵐ x ∂unitMeasure,
      Summable (fun i => S.eigenvalue (i+1)*(S.eigenfunction (i+1) x)^2) ∧
      0≤residualDiagonal S x ∧ residualDiagonal S x≤2*rowDegree U x-edgeDensity U := by
  filter_upwards [centeredKernel_diagonal_bound U S] with x hx
  have ht : Summable (fun i => S.eigenvalue (i+1)*(S.eigenfunction (i+1) x)^2) :=
    (summable_nat_add_iff 1).mpr hx.1
  refine ⟨ht,tsum_nonneg fun i => mul_nonneg (S.eigenvalue_nonneg _) (sq_nonneg _),?_⟩
  have he := hx.1.tsum_eq_zero_add
  have hp : 0≤S.eigenvalue 0*(S.eigenfunction 0 x)^2 := mul_nonneg (S.eigenvalue_nonneg _) (sq_nonneg _)
  change (∑' i, S.eigenvalue (i+1)*(S.eigenfunction (i+1) x)^2)≤_
  dsimp [spectralDiagonal] at hx
  linarith [hx.2.2]

theorem residual_eigenvalue_le (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (i : ℕ) :
    S.eigenvalue (i+1)≤edgeDensity U-S.eigenvalue 0 := by
  have ht : Summable (fun i => S.eigenvalue (i+1)) :=
    (summable_nat_add_iff 1).mpr (centeredKernel_trace_bound U S).1
  exact (ht.le_tsum i (fun j _ => S.eigenvalue_nonneg _)).trans (centeredSpectrum_tail_bounds U S).1

/-- Exact rowwise Parseval followed by the graphon-dependent bound sR(x,x). -/
theorem spectralRemainder_row_square (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    ∀ᵐ x ∂unitMeasure,
      MemLp (fun y => spectralRemainder U S (x,y)) 2 unitMeasure ∧
      (∫ y, spectralRemainder U S (x,y)^2 ∂unitMeasure)=
        ∑' i, S.eigenvalue (i+1)^2*(S.eigenfunction (i+1) x)^2 ∧
      (∫ y, spectralRemainder U S (x,y)^2 ∂unitMeasure)≤
        (edgeDensity U-S.eigenvalue 0)*residualDiagonal S x := by
  filter_upwards [S.row_tail_parseval 1,S.row_memLp,residualDiagonal_bound U S] with x hx hr hd
  have hlp : MemLp (fun y => spectralRemainder U S (x,y)) 2 unitMeasure :=
    hr.sub ((S.eigenfunction_memLp 0).const_mul (S.eigenvalue 0*S.eigenfunction 0 x))
  have he : (∫ y, spectralRemainder U S (x,y)^2 ∂unitMeasure)=
      ∑' i, S.eigenvalue (i+1)^2*(S.eigenfunction (i+1) x)^2 := by
    simpa [spectralRemainder,spectralPartial] using hx.2
  refine ⟨hlp,he,?_⟩
  rw [he]
  change _≤(edgeDensity U-S.eigenvalue 0)*(∑' i, S.eigenvalue (i+1)*(S.eigenfunction (i+1) x)^2)
  rw [← tsum_mul_left]
  apply hx.1.tsum_le_tsum _ (hd.1.mul_left _)
  intro i
  have hh := mul_le_mul_of_nonneg_right (residual_eigenvalue_le U S i)
    (mul_nonneg (S.eigenvalue_nonneg (i+1)) (sq_nonneg (S.eigenfunction (i+1) x)))
  nlinarith

/-- The uniform spectral remainder row bound in `eq:s7Rrow`. -/
theorem minimizer_spectralRemainder_row_bound (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    ∀ᵐ x ∂unitMeasure,
      0≤residualDiagonal S x ∧ residualDiagonal S x≤edgeDensity U+graphonMultiplier U r*r^3 ∧
      MemLp (fun y => spectralRemainder U S (x,y)) 2 unitMeasure ∧
      (∫ y, spectralRemainder U S (x,y)^2 ∂unitMeasure)≤
        (edgeDensity U-S.eigenvalue 0)*(edgeDensity U+graphonMultiplier U r*r^3) := by
  filter_upwards [residualDiagonal_bound U S,spectralRemainder_row_square U S,
    minimizer_degree_upper hSampling hr hU] with x hd hrx hdx
  have hA : residualDiagonal S x≤edgeDensity U+graphonMultiplier U r*r^3 := by linarith [hd.2.2]
  refine ⟨hd.2.1,hA,hrx.1,hrx.2.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr (centeredEigenvalue_le_mean U S 0))

/-- The remainder annihilates the constant function. -/
theorem spectralRemainder_row_zero (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (hev : 0<S.eigenvalue 0) :
    ∀ᵐ x ∂unitMeasure, (∫ y, spectralRemainder U S (x,y) ∂unitMeasure)=0 := by
  have hi := MemLp.integrable (by norm_num : (1:ENNReal)≤2) (S.eigenfunction_memLp 0)
  filter_upwards [centeredKernel_row_zero U,S.row_memLp] with x hx hr
  dsimp only [spectralRemainder]
  rw [integral_sub (MemLp.integrable (by norm_num) hr) (hi.const_mul _),
    integral_const_mul,hx,centeredEigenfunction_mean_zero U S hev]
  ring

/-- The remainder annihilates the leading eigenfunction. -/
theorem spectralRemainder_eigenfunction_zero (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    ∀ᵐ x ∂unitMeasure,
      (∫ y, spectralRemainder U S (x,y)*S.eigenfunction 0 y ∂unitMeasure)=0 := by
  have he2 : Integrable (fun y => S.eigenfunction 0 y*S.eigenfunction 0 y) unitMeasure :=
    (S.eigenfunction_memLp 0).integrable_mul (S.eigenfunction_memLp 0)
  filter_upwards [S.eigen_equation 0,S.row_memLp] with x hx hr
  have hi : Integrable (fun y => centeredKernel U (x,y)*S.eigenfunction 0 y) unitMeasure :=
    hr.integrable_mul (S.eigenfunction_memLp 0)
  calc
    _ = (∫ y, centeredKernel U (x,y)*S.eigenfunction 0 y ∂unitMeasure)-
        S.eigenvalue 0*S.eigenfunction 0 x*(∫ y, S.eigenfunction 0 y*S.eigenfunction 0 y ∂unitMeasure) := by
      rw [← integral_const_mul,← integral_sub hi (he2.const_mul _)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by dsimp [spectralRemainder]; ring
    _ = 0 := by rw [hx,S.orthonormal_integral]; simp

/-- The actual residual quadratic form equals the full form minus its first mode. -/
theorem spectralRemainder_quadratic (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    (∫ p, spectralRemainder U S p*(f p.1*f p.2) ∂squareMeasure)=
      (∫ p, centeredKernel U p*(f p.1*f p.2) ∂squareMeasure)-
      S.eigenvalue 0*(∫ x, S.eigenfunction 0 x*f x ∂unitMeasure)^2 := by
  have hp := (hf.comp Measure.quasiMeasurePreserving_fst).mul
    (hf.comp Measure.quasiMeasurePreserving_snd)
  obtain ⟨C,_,hC⟩ := hp.bound
  have hplp : MemLp (fun p => f p.1*f p.2) 2 squareMeasure :=
    MemLp.of_bound hp.measurable.aestronglyMeasurable C hC
  have hiK := ((centeredKernel_bounded U).mul hp).integrable
  have hiN : Integrable (fun p => spectralPartial S.eigenvalue S.eigenfunction 1 p*(f p.1*f p.2))
      squareMeasure := (spectralPartial_memLp S 1).integrable_mul hplp
  have hN := spectralPartial_quadratic S 1 hf
  simp only [Finset.sum_range_one] at hN
  rw [← hN,← integral_sub hiK hiN]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by simp [spectralRemainder,spectralPartial]; ring

/-- The graphon-dependent residual norm bound in quadratic-form form. -/
theorem spectralRemainder_quadratic_upper (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    (∫ p, spectralRemainder U S p*(f p.1*f p.2) ∂squareMeasure)≤
      (edgeDensity U-S.eigenvalue 0)*(∫ x, f x^2 ∂unitMeasure) := by
  rw [spectralRemainder_quadratic U S hf]
  have ht := (spectralPartial_quadratic_tendsto U S hf).sub_const
    (S.eigenvalue 0*(∫ x, S.eigenfunction 0 x*f x ∂unitMeasure)^2)
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  rw [spectralPartial_quadratic S (n+1) hf,Finset.sum_range_succ']
  simp only [add_sub_cancel_right]
  obtain ⟨C,_,hC⟩ := hf.bound
  have hflp : MemLp f 2 unitMeasure := MemLp.of_bound hf.measurable.aestronglyMeasurable C hC
  have htail : Summable (fun i => S.eigenvalue (i+1)) :=
    (summable_nat_add_iff 1).mpr (centeredKernel_trace_bound U S).1
  calc
    _ ≤ ∑ i∈Finset.range n, S.eigenvalue (i+1)*(∫ x, f x^2 ∂unitMeasure) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (spectral_coefficient_sq_le S (i+1) hflp)
        (S.eigenvalue_nonneg _)
    _ = (∑ i∈Finset.range n, S.eigenvalue (i+1))*(∫ x, f x^2 ∂unitMeasure) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((Summable.sum_le_tsum (Finset.range n) (fun i _ => S.eigenvalue_nonneg _) htail).trans
        (centeredSpectrum_tail_bounds U S).1) (integral_nonneg fun x => sq_nonneg _)

end SparseLowerTail.Section07

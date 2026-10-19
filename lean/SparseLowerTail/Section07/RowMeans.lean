import SparseLowerTail.Section07.ResidualBlockMeans

/-! The actual row-average approximation `eq:s7rowmean`. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- The exact row-mean error decomposition on any positive-mass measurable set. -/
theorem rowMean_error_identity (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U))
    (hψ : BoundedObservable unitMeasure (S.eigenfunction 0))
    {P : Set ℝ} (hp : 0<unitMeasure.real P) :
    ∀ᵐ x ∂unitMeasure,
      setAverage P (fun y => U (x,y))-
        (rowDegree U x-S.eigenvalue 0*S.eigenfunction 0 x*setAverage P (signBlockFunction (S.eigenfunction 0)))=
      setAverage P (degreeDeviation U)-S.eigenvalue 0*S.eigenfunction 0 x*
        setAverage P (fun y => S.eigenfunction 0 y-signBlockFunction (S.eigenfunction 0) y)-
        setAverage P (fun y => spectralRemainder U S (x,y)) := by
  filter_upwards [boundedObservable_sections (spectralRemainder_bounded S hψ)] with x hx
  have hD := (degreeDeviation_bounded U).integrable
  have hσ := (signBlockFunction_bounded (S.eigenfunction_measurable 0)).integrable
  have hconst : Integrable (fun _ : ℝ => rowDegree U x) unitMeasure := integrable_const _
  have hsum : Integrable (fun y => rowDegree U x+degreeDeviation U y) unitMeasure := hconst.add hD
  have hscaled : Integrable (fun y => S.eigenvalue 0*S.eigenfunction 0 x*S.eigenfunction 0 y) unitMeasure :=
    hψ.integrable.const_mul _
  have hdif : Integrable (fun y => rowDegree U x+degreeDeviation U y-
      S.eigenvalue 0*S.eigenfunction 0 x*S.eigenfunction 0 y) unitMeasure := hsum.sub hscaled
  have he : (fun y => U (x,y))=(fun y => rowDegree U x+degreeDeviation U y-
      S.eigenvalue 0*S.eigenfunction 0 x*S.eigenfunction 0 y-spectralRemainder U S (x,y)) := by
    funext y
    dsimp [spectralRemainder,centeredKernel,degreeDeviation]
    ring
  rw [he,setAverage_sub P hdif hx.integrable,setAverage_sub P hsum hscaled,
    setAverage_add P hconst hD,setAverage_const P hp,setAverage_const_mul,
    setAverage_sub P hψ.integrable hσ]
  ring

/-- A sign function averages to its constant value on each of its sign blocks. -/
theorem signBlockFunction_average {f : ℝ → ℝ} (hf : Measurable f)
    {P : Set ℝ} (hp : 0<unitMeasure.real P) :
    (P=positiveSignBlock f → setAverage P (signBlockFunction f)=1) ∧
    (P=(positiveSignBlock f)ᶜ → setAverage P (signBlockFunction f)=-1) := by
  constructor
  · intro he; subst P
    have hh : (∫ x in positiveSignBlock f, signBlockFunction f x ∂unitMeasure)=
        ∫ x in positiveSignBlock f, (1:ℝ) ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (positiveSignBlock_measurable hf)] with x hx
      simp [signBlockFunction,show 0≤f x from hx]
    change (∫ x in positiveSignBlock f, signBlockFunction f x ∂unitMeasure)/unitMeasure.real (positiveSignBlock f)=1
    rw [hh]
    exact setAverage_const _ hp 1
  · intro he; subst P
    have hh : (∫ x in (positiveSignBlock f)ᶜ, signBlockFunction f x ∂unitMeasure)=
        ∫ x in (positiveSignBlock f)ᶜ, (-1:ℝ) ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (positiveSignBlock_measurable hf).compl] with x hx
      simp [signBlockFunction,show ¬0≤f x from hx]
    change (∫ x in (positiveSignBlock f)ᶜ, signBlockFunction f x ∂unitMeasure)/unitMeasure.real (positiveSignBlock f)ᶜ=-1
    rw [hh]
    exact setAverage_const _ hp (-1)

/-- Uniform row approximation on either actual eigenfunction sign block. -/
theorem smallTarget_rowMean_bound (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U))
    {P : Set ℝ} (hP : P=positiveSignBlock (S.eigenfunction 0) ∨ P=(positiveSignBlock (S.eigenfunction 0))ᶜ) :
    let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
    ∀ᵐ x ∂unitMeasure,
      |setAverage P (fun y => U (x,y))-
        (rowDegree U x-S.eigenvalue 0*S.eigenfunction 0 x*setAverage P (signBlockFunction (S.eigenfunction 0)))|≤
      rowMeanError (graphonMultiplier U r*r^3/2) (S.eigenvalue 0) M
        (edgeDensity U-S.eigenvalue 0) (edgeDensity U+graphonMultiplier U r*r^3) := by
  dsimp only
  let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hev := smallTarget_centeredEigenvalue_pos external hr hU S
  have hψ := minimizer_eigenfunction_bounded hSampling hr01 hU S hev
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hM : 1≤M := hblocks.1
  have hMpos : 0<M := by linarith
  have hmass : 1/(2*M^2)≤unitMeasure.real P := by
    rcases hP with rfl | rfl
    · exact hblocks.2.1
    · exact hblocks.2.2.2.1
  have hp : 0<unitMeasure.real P := (by positivity : (0:ℝ)<1/(2*M^2)).trans_le hmass
  have hψavg := (signBlock_average_estimates hMpos (S.eigenfunction_measurable 0)
    (minimizer_eigenfunction_bound hSampling hr01 hU S hev)
    (centeredEigenfunction_mean_zero U S hev)
    (show (∫ x, S.eigenfunction 0 x^2 ∂unitMeasure)=1 from by
      simpa only [pow_two,if_pos rfl] using S.orthonormal_integral 0 0) hP).1
  have hDavg := (smallTarget_degree_block_averages external hSampling hr hU S P hP).1
  filter_upwards [rowMean_error_identity U S hψ hp,
    smallTarget_residual_block_average external hSampling hr hU S hP,
    minimizer_eigenfunction_bound hSampling hr01 hU S hev] with x hx hR hfx
  rw [hx]
  have hterm : |S.eigenvalue 0*S.eigenfunction 0 x*
      setAverage P (fun y => S.eigenfunction 0 y-signBlockFunction (S.eigenfunction 0) y)|≤
      3*S.eigenvalue 0*M*(M-1) := by
    rw [abs_mul,abs_mul,abs_of_nonneg hev.le]
    have hfac := mul_le_mul_of_nonneg_left hfx hev.le
    have hh := mul_le_mul hfac hψavg (abs_nonneg _) (mul_nonneg hev.le hMpos.le)
    nlinarith
  have htri := abs_sub (setAverage P (degreeDeviation U)-S.eigenvalue 0*S.eigenfunction 0 x*
      setAverage P (fun y => S.eigenfunction 0 y-signBlockFunction (S.eigenfunction 0) y))
    (setAverage P (fun y => spectralRemainder U S (x,y)))
  have htri' := abs_sub (setAverage P (degreeDeviation U))
    (S.eigenvalue 0*S.eigenfunction 0 x*
      setAverage P (fun y => S.eigenfunction 0 y-signBlockFunction (S.eigenfunction 0) y))
  change _≤rowMeanError _ _ M _ _
  dsimp only [rowMeanError]
  linarith

/-- The two inequalities of `eq:s7rowmean` in their manuscript form. -/
theorem smallTarget_rowMeans (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
    let E := rowMeanError (graphonMultiplier U r*r^3/2) (S.eigenvalue 0) M
      (edgeDensity U-S.eigenvalue 0) (edgeDensity U+graphonMultiplier U r*r^3)
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ x ∂unitMeasure,
      |setAverage P (fun y => U (x,y))-(rowDegree U x-S.eigenvalue 0*S.eigenfunction 0 x)|≤E ∧
      |setAverage Pᶜ (fun y => U (x,y))-(rowDegree U x+S.eigenvalue 0*S.eigenfunction 0 x)|≤E := by
  dsimp only
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hMpos : 0<Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0) :=
    lt_of_lt_of_le zero_lt_one hblocks.1
  have hp : 0<unitMeasure.real (positiveSignBlock (S.eigenfunction 0)) :=
    (by positivity : (0:ℝ)<1/(2*(Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0))^2)).trans_le hblocks.2.1
  have hn : 0<unitMeasure.real (positiveSignBlock (S.eigenfunction 0))ᶜ :=
    (by positivity : (0:ℝ)<1/(2*(Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0))^2)).trans_le hblocks.2.2.2.1
  have hep := (signBlockFunction_average (S.eigenfunction_measurable 0) hp).1 rfl
  have hen := (signBlockFunction_average (S.eigenfunction_measurable 0) hn).2 rfl
  filter_upwards [smallTarget_rowMean_bound external hSampling hr hU S (Or.inl rfl),
    smallTarget_rowMean_bound external hSampling hr hU S (Or.inr rfl)] with x hx hy
  constructor
  · simpa only [hep,mul_one] using hx
  · simpa only [hen,mul_neg_one,sub_neg_eq_add] using hy

end SparseLowerTail.Section07

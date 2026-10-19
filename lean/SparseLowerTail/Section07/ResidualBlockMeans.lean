import SparseLowerTail.Section07.SignAverages
import SparseLowerTail.Section07.RowErrors

/-! Cancellation of the residual kernel on the sign blocks and the resulting
uniform bound on its block averages. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

private theorem signBlock_integral_cancellation {f ψ : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) (hψ : BoundedObservable unitMeasure ψ)
    (hmψ : Measurable ψ) (hfzero : (∫ x, f x ∂unitMeasure)=0)
    (horth : (∫ x, f x*ψ x ∂unitMeasure)=0)
    {P : Set ℝ} (hP : P=positiveSignBlock ψ ∨ P=(positiveSignBlock ψ)ᶜ) :
    |∫ x in P, f x ∂unitMeasure|=
      |∫ x, f x*(signBlockFunction ψ x-ψ x) ∂unitMeasure|/2 := by
  have hmeas := positiveSignBlock_measurable hmψ
  have hσ := signBlockFunction_bounded hmψ
  have hsplit := integral_add_compl hmeas (hf.mul hσ).integrable
  have hp : (∫ x in positiveSignBlock ψ, f x*signBlockFunction ψ x ∂unitMeasure)=
      ∫ x in positiveSignBlock ψ, f x ∂unitMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas] with x hx
    simp [signBlockFunction,show 0≤ψ x from hx]
  have hn : (∫ x in (positiveSignBlock ψ)ᶜ, f x*signBlockFunction ψ x ∂unitMeasure)=
      -(∫ x in (positiveSignBlock ψ)ᶜ, f x ∂unitMeasure) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas.compl] with x hx
    simp [signBlockFunction,show ¬0≤ψ x from hx]
  rw [hp,hn] at hsplit
  have hsum := integral_add_compl hmeas hf.integrable
  rw [hfzero] at hsum
  have he : (∫ x, f x*(signBlockFunction ψ x-ψ x) ∂unitMeasure)=
      ∫ x, f x*signBlockFunction ψ x ∂unitMeasure := by
    have heq : (fun x => f x*(signBlockFunction ψ x-ψ x))=
        (fun x => f x*signBlockFunction ψ x-f x*ψ x) := by funext x; ring
    rw [heq,integral_sub (hf.mul hσ).integrable (hf.mul hψ).integrable,horth,sub_zero]
  rw [he]
  rcases hP with rfl | rfl
  · have hh : (∫ x, f x*signBlockFunction ψ x ∂unitMeasure)=
        2*(∫ x in positiveSignBlock ψ, f x ∂unitMeasure) := by linarith
    rw [hh,abs_mul]
    norm_num
  · have hh : (∫ x, f x*signBlockFunction ψ x ∂unitMeasure)=
        -2*(∫ x in (positiveSignBlock ψ)ᶜ, f x ∂unitMeasure) := by linarith
    rw [hh,abs_mul]
    norm_num

/-- The exact half-factor cancellation holds for actual residual kernel rows. -/
theorem spectralRemainder_signBlock_integral (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (hev : 0<S.eigenvalue 0)
    (hψ : BoundedObservable unitMeasure (S.eigenfunction 0)) {P : Set ℝ}
    (hP : P=positiveSignBlock (S.eigenfunction 0) ∨ P=(positiveSignBlock (S.eigenfunction 0))ᶜ) :
    ∀ᵐ x ∂unitMeasure, |∫ y in P, spectralRemainder U S (x,y) ∂unitMeasure|=
      |kernelAction (spectralRemainder U S)
        (fun y => signBlockFunction (S.eigenfunction 0) y-S.eigenfunction 0 y) x|/2 := by
  filter_upwards [boundedObservable_sections (spectralRemainder_bounded S hψ),
    spectralRemainder_row_zero U S hev,spectralRemainder_eigenfunction_zero U S] with x hx hz he
  exact signBlock_integral_cancellation hx hψ (S.eigenfunction_measurable 0) hz he hP

/-- The residual block-average term in `eq:s7rowmean`, including the sharp
factor M² resulting from cancellation and the sign-block mass bound. -/
theorem smallTarget_residual_block_average (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U))
    {P : Set ℝ} (hP : P=positiveSignBlock (S.eigenfunction 0) ∨ P=(positiveSignBlock (S.eigenfunction 0))ᶜ) :
    let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
    ∀ᵐ x ∂unitMeasure, |setAverage P (fun y => spectralRemainder U S (x,y))|≤
      M^2*Real.sqrt ((edgeDensity U-S.eigenvalue 0)*(edgeDensity U+graphonMultiplier U r*r^3))*
        Real.sqrt (2-2/M) := by
  dsimp only
  let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hev := smallTarget_centeredEigenvalue_pos external hr hU S
  have hψ := minimizer_eigenfunction_bounded hSampling hr01 hU S hev
  have hσ := signBlockFunction_bounded (S.eigenfunction_measurable 0)
  have herr : BoundedObservable unitMeasure
      (fun y => signBlockFunction (S.eigenfunction 0) y-S.eigenfunction 0 y) := by
    convert hσ.add (hψ.const_mul (-1)) using 1
    funext y; ring
  obtain ⟨C,_,hC⟩ := herr.bound
  have herrlp := MemLp.of_bound (p := (2:ENNReal)) herr.measurable.aestronglyMeasurable C hC
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hM : 1≤M := hblocks.1
  have hMpos : 0<M := by linarith
  have hmass : 1/(2*M^2)≤unitMeasure.real P := by
    rcases hP with rfl | rfl
    · exact hblocks.2.1
    · exact hblocks.2.2.2.1
  have hp : 0<unitMeasure.real P := (by positivity : (0:ℝ)<1/(2*M^2)).trans_le hmass
  have hfac : 1≤2*M^2*unitMeasure.real P := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2*M^2)).mp hmass
    nlinarith
  filter_upwards [spectralRemainder_signBlock_integral U S hev hψ hP,
    minimizer_residualAction_bound hSampling hr01 hU S herrlp] with x hx hb
  have hsqrt := Real.sqrt_le_sqrt hblocks.2.2.2.2.2.2
  have hbound := hb.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))
  dsimp [setAverage]
  rw [abs_div,abs_of_nonneg hp.le,hx]
  apply (div_le_iff₀ hp).mpr
  have hh := mul_le_mul_of_nonneg_right hfac
    (mul_nonneg (Real.sqrt_nonneg ((edgeDensity U-S.eigenvalue 0)*
      (edgeDensity U+graphonMultiplier U r*r^3))) (Real.sqrt_nonneg (2-2/M)))
  change _≤M^2*_ * _ * unitMeasure.real P
  nlinarith

end SparseLowerTail.Section07

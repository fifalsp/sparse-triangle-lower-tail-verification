import SparseLowerTail.Section07.RowMeans

/-! Integral inequalities for normalized set averages used to propagate the
seven exact codegree terms into the explicit scalar error. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section07
open Section04

theorem setAverage_mono_ae {P : Set ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f unitMeasure) (hg : Integrable g unitMeasure)
    (hfg : ∀ᵐ x ∂unitMeasure.restrict P, f x≤g x) : setAverage P f≤setAverage P g := by
  exact div_le_div_of_nonneg_right (integral_mono_ae hf.integrableOn hg.integrableOn hfg) measureReal_nonneg

theorem setAverage_le_const {P : Set ℝ} (hp : 0<unitMeasure.real P) {f : ℝ → ℝ} {c : ℝ}
    (hf : Integrable f unitMeasure) (hb : ∀ᵐ x ∂unitMeasure.restrict P, f x≤c) :
    setAverage P f≤c := by
  rw [← setAverage_const P hp c]
  exact setAverage_mono_ae hf (integrable_const _) hb

theorem setAverage_abs_const_mul (P : Set ℝ) (f : ℝ → ℝ) (c : ℝ) :
    setAverage P (fun x => |c*f x|)=|c| *setAverage P (fun x => |f x|) := by
  simp_rw [abs_mul]
  exact setAverage_const_mul _ _ _

theorem setAverage_abs_neg (P : Set ℝ) (f : ℝ → ℝ) :
    setAverage P (fun x => |-f x|)=setAverage P (fun x => |f x|) := by simp only [abs_neg]

/-- L² controls the absolute integral on the probability space. -/
theorem integral_abs_le_sqrt_sq {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure) :
    (∫ x, |f x| ∂unitMeasure)≤Real.sqrt (∫ x, f x^2 ∂unitMeasure) := by
  have habs : MemLp (fun x => |f x|) 2 unitMeasure := hf.norm
  have hh := abs_integral_mul_le_L2 habs (memLp_const (1:ℝ))
  simp only [mul_one,sq_abs,one_pow,integral_const,measureReal_univ_eq_one,
    one_smul,Real.sqrt_one] at hh
  rwa [abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)] at hh

/-- L² controls a positive-mass set average, with its exact mass factor. -/
theorem setAverage_abs_le_L2 {f : ℝ → ℝ} {P : Set ℝ} (hf : MemLp f 2 unitMeasure) :
    setAverage P (fun x => |f x|)≤Real.sqrt (∫ x, f x^2 ∂unitMeasure)/unitMeasure.real P := by
  exact (setAverage_abs_le_global (MemLp.integrable (by norm_num) hf)).trans
    (div_le_div_of_nonneg_right (integral_abs_le_sqrt_sq hf) measureReal_nonneg)

/-- Converting a row L² bound and the block mass bound into an average bound. -/
theorem setAverage_abs_le_of_square {f : ℝ → ℝ} {P : Set ℝ} {M B : ℝ}
    (hf : MemLp f 2 unitMeasure) (hM : 0<M) (hB : 0≤B)
    (hmass : 1/(2*M^2)≤unitMeasure.real P)
    (hL2 : (∫ x, f x^2 ∂unitMeasure)≤B^2) :
    setAverage P (fun x => |f x|)≤2*M^2*B := by
  have hp : 0<unitMeasure.real P := (by positivity : (0:ℝ)<1/(2*M^2)).trans_le hmass
  have hs : Real.sqrt (∫ x, f x^2 ∂unitMeasure)≤B := by
    exact (Real.sqrt_le_iff).mpr ⟨hB,hL2⟩
  apply (setAverage_abs_le_L2 hf).trans
  apply (div_le_iff₀ hp).mpr
  have hm := (div_le_iff₀ (by positivity : (0:ℝ)<2*M^2)).mp hmass
  have hh := mul_le_mul_of_nonneg_left hm hB
  nlinarith

/-- Triangle inequality for averages of a finite sum. -/
theorem setAverage_abs_sum {ι : Type*} (F : Finset ι) (P : Set ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i∈F, Integrable (f i) unitMeasure) :
    setAverage P (fun x => |∑ i∈F, f i x|)≤∑ i∈F, setAverage P (fun x => |f i x|) := by
  have hisum : Integrable (fun x => ∑ i∈F, f i x) unitMeasure := integrable_finset_sum _ hf
  have hiabs : ∀ i∈F, Integrable (fun x => |f i x|) unitMeasure := fun i hi => (hf i hi).norm
  have habssum : Integrable (fun x => ∑ i∈F, |f i x|) unitMeasure := integrable_finset_sum _ hiabs
  calc
    _ ≤ setAverage P (fun x => ∑ i∈F, |f i x|) := by
      apply setAverage_mono_ae hisum.norm habssum
      exact Eventually.of_forall fun x => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      dsimp [setAverage]
      rw [integral_finset_sum F (fun i hi => (hiabs i hi).integrableOn),Finset.sum_div]

end SparseLowerTail.Section07

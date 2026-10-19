import SparseLowerTail.Section07.SetAverages

/-! The actual sign-block eigenfunction averages `eq:s7psiavg`. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- Either sign block contains half of the total absolute integral. -/
theorem signBlock_half_abs_integral {f : ℝ → ℝ} (hf : Measurable f)
    (hi : Integrable f unitMeasure) (hm : (∫ x, f x ∂unitMeasure)=0)
    {P : Set ℝ} (hP : P=positiveSignBlock f ∨ P=(positiveSignBlock f)ᶜ) :
    (∫ x, |f x| ∂unitMeasure)=2*(∫ x in P, |f x| ∂unitMeasure) := by
  have hmeas := positiveSignBlock_measurable hf
  have hplus : (∫ x in positiveSignBlock f, |f x| ∂unitMeasure)=
      ∫ x in positiveSignBlock f, f x ∂unitMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas] with x hx
    exact abs_of_nonneg hx
  have hminus : (∫ x in (positiveSignBlock f)ᶜ, |f x| ∂unitMeasure)=
      -(∫ x in (positiveSignBlock f)ᶜ, f x ∂unitMeasure) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas.compl] with x hx
    exact abs_of_nonpos (le_of_not_ge hx)
  have ha := integral_add_compl hmeas hi
  rw [hm] at ha
  have hb := integral_add_compl hmeas hi.norm
  simp only [Real.norm_eq_abs] at hb
  rw [hplus,hminus] at hb
  rcases hP with rfl | rfl
  · rw [hplus]; linarith
  · rw [hminus]; linarith

/-- The signed average error is the error in the absolute-value average. -/
theorem signBlock_average_error_abs {f : ℝ → ℝ} (hf : Measurable f)
    (hi : Integrable f unitMeasure) {P : Set ℝ}
    (hP : P=positiveSignBlock f ∨ P=(positiveSignBlock f)ᶜ)
    (hp : 0<unitMeasure.real P) :
    |setAverage P (fun x => f x-signBlockFunction f x)|=
      |setAverage P (fun x => |f x|)-1| := by
  have hmeas := positiveSignBlock_measurable hf
  have hiabs : Integrable (fun x => |f x|) unitMeasure := hi.norm
  have hav : ((∫ x in P, (|f x|-1) ∂unitMeasure)/unitMeasure.real P)=
      setAverage P (fun x => |f x|)-1 := by
    rw [integral_sub hiabs.integrableOn (integrable_const _),setIntegral_const]
    dsimp [setAverage]
    field_simp
  rcases hP with rfl | rfl
  · rw [← hav]
    congr 1
    apply congrArg (fun v : ℝ => v/unitMeasure.real (positiveSignBlock f))
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas] with x hx
    simp [signBlockFunction,show 0≤f x from hx,abs_of_nonneg (show 0≤f x from hx)]
  · rw [← hav]
    have he : (∫ x in (positiveSignBlock f)ᶜ, (f x-signBlockFunction f x) ∂unitMeasure)=
        -(∫ x in (positiveSignBlock f)ᶜ, (|f x|-1) ∂unitMeasure) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hmeas.compl] with x hx
      change f x-signBlockFunction f x=-(|f x|-1)
      have hfx : ¬0≤f x := hx
      rw [signBlockFunction,if_neg hfx,abs_of_nonpos (le_of_not_ge hfx)]
      ring
    dsimp [setAverage]
    rw [he,neg_div,abs_neg]

/-- The scalar estimate behind the constants 3 and 5 in the sign-block bounds. -/
private theorem average_abs_sub_one_bound {M c t : ℝ} (hM : 1≤M) (hc : 0<c)
    (hcup : c≤1-1/(2*M^2)) (ht : 1/(2*M)≤t) (htup : t≤M*c) :
    |t/c-1|≤3*(M-1) := by
  have hMp : 0<M := by linarith
  have hden : 0<2*M^2-1 := by nlinarith
  have hlo : M/(2*M^2-1)≤t/c := by
    apply (div_le_div_iff₀ hden hc).mpr
    have hh := mul_le_mul_of_nonneg_right hcup hMp.le
    have hh' := mul_le_mul_of_nonneg_right ht hden.le
    have he : M*(1-1/(2*M^2))=(2*M^2-1)/(2*M) := by field_simp
    rw [mul_comm c M,mul_comm (1-1/(2*M^2)) M,he] at hh
    have he' : 1/(2*M)*(2*M^2-1)=(2*M^2-1)/(2*M) := by ring
    rw [he'] at hh'
    exact hh.trans hh'
  have hlower : 1-3*(M-1)≤M/(2*M^2-1) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg (M-1)) (show 0≤3*M+2 by linarith)]
  have hu : t/c≤M := (div_le_iff₀ hc).mpr (by nlinarith [htup])
  rw [abs_le]
  constructor <;> linarith [hlower.trans hlo]

/-- Both estimates `eq:s7psiavg`, for either actual sign block. -/
theorem signBlock_average_estimates {f : ℝ → ℝ} {M : ℝ} (hM : 0<M)
    (hf : Measurable f) (hb : ∀ᵐ x ∂unitMeasure, |f x|≤M)
    (hm : (∫ x, f x ∂unitMeasure)=0) (hn : (∫ x, f x^2 ∂unitMeasure)=1)
    {P : Set ℝ} (hP : P=positiveSignBlock f ∨ P=(positiveSignBlock f)ᶜ) :
    |setAverage P (fun x => f x-signBlockFunction f x)|≤3*(M-1) ∧
      setAverage P (fun x => |f x-signBlockFunction f x|)≤5*(M-1) := by
  have hbo : BoundedObservable unitMeasure f := ⟨hf.aemeasurable,M,hM.le,hb⟩
  have hi := hbo.integrable
  have hiabs : Integrable (fun x => |f x|) unitMeasure := hi.norm
  have hblocks := sign_blocks_estimates hM hf hb hm hn
  have hM1 := hblocks.1
  have hmeas : MeasurableSet P := by
    rcases hP with rfl | rfl
    · exact positiveSignBlock_measurable hf
    · exact (positiveSignBlock_measurable hf).compl
  have hmass : 1/(2*M^2)≤unitMeasure.real P ∧ unitMeasure.real P≤1-1/(2*M^2) := by
    rcases hP with rfl | rfl
    · exact ⟨hblocks.2.1,hblocks.2.2.1⟩
    · exact ⟨hblocks.2.2.2.1,hblocks.2.2.2.2.1⟩
  have hp : 0<unitMeasure.real P := (by positivity : (0:ℝ)<1/(2*M^2)).trans_le hmass.1
  have hhalf := signBlock_half_abs_integral hf hi hm hP
  have hL1 : 1≤M*(∫ x, |f x| ∂unitMeasure) := by
    have hsq : Integrable (fun x => f x^2) unitMeasure := by simpa only [pow_two] using (hbo.mul hbo).integrable
    have hh := integral_mono_ae hsq (hiabs.const_mul M) (show ∀ᵐ x ∂unitMeasure, f x^2≤M*|f x| from by
      filter_upwards [hb] with x hx
      nlinarith [mul_le_mul_of_nonneg_right hx (abs_nonneg (f x)),sq_abs (f x)])
    rwa [hn,integral_const_mul] at hh
  have ht : 1/(2*M)≤∫ x in P, |f x| ∂unitMeasure := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [hhalf] at hL1
    nlinarith
  have htup : (∫ x in P, |f x| ∂unitMeasure)≤M*unitMeasure.real P := by
    have hh := integral_mono_ae (μ := unitMeasure.restrict P) hiabs.integrableOn
      (integrable_const M) (ae_restrict_of_ae hb)
    simpa [mul_comm] using hh
  have hav := average_abs_sub_one_bound hM1 hp hmass.2 ht htup
  constructor
  · rw [signBlock_average_error_abs hf hi hP hp]
    exact hav
  · have herror : ∀ᵐ x ∂unitMeasure,
        |f x-signBlockFunction f x|≤1-|f x|+2*(M-1) := by
      filter_upwards [hb] with x hx
      have he : |f x-signBlockFunction f x|=|(|f x|-1)| := by
        dsimp [signBlockFunction]
        split_ifs with hfx
        · rw [abs_of_nonneg hfx]
        · rw [abs_of_nonpos (le_of_not_ge hfx)]
          rw [show f x-(-1)=-(-f x-1) by ring,abs_neg]
      rw [he,abs_le]
      constructor <;> linarith [abs_nonneg (f x)]
    have herrorI : Integrable (fun x => |f x-signBlockFunction f x|) unitMeasure := by
      exact (hi.sub (signBlockFunction_bounded hf).integrable).norm
    have hupI : Integrable (fun x => 1-|f x|+2*(M-1)) unitMeasure :=
      ((integrable_const _).sub hiabs).add (integrable_const _)
    have hh := integral_mono_ae (μ := unitMeasure.restrict P) herrorI.integrableOn hupI.integrableOn
      (ae_restrict_of_ae herror)
    have hcalc : (∫ x in P, (1-|f x|+2*(M-1)) ∂unitMeasure)=
        unitMeasure.real P*(1+2*(M-1))-(∫ x in P, |f x| ∂unitMeasure) := by
      have hisub : Integrable (fun x => 1-|f x|) (unitMeasure.restrict P) :=
        (integrable_const _).sub hiabs.integrableOn
      rw [integral_add hisub (integrable_const _),integral_sub (integrable_const _) hiabs.integrableOn]
      simp only [setIntegral_const,smul_eq_mul]
      ring
    rw [hcalc] at hh
    apply (div_le_iff₀ hp).mpr
    have hlo := (abs_le.mp hav).1
    have hhlo := (le_div_iff₀ hp).mp (show 1-3*(M-1)≤
        (∫ x in P, |f x| ∂unitMeasure)/unitMeasure.real P by linarith)
    nlinarith

end SparseLowerTail.Section07

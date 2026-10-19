import SparseLowerTail.Section07.CenteredCubic

/-! The sign-block construction and mass/error estimates `eq:s7mass`.
All quantities are actual measurable sets and integrals of the eigenfunction. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

def positiveSignBlock (f : ℝ → ℝ) : Set ℝ := {x | 0≤f x}

def signBlockFunction (f : ℝ → ℝ) (x : ℝ) : ℝ := if 0≤f x then 1 else -1

theorem positiveSignBlock_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    MeasurableSet (positiveSignBlock f) := measurableSet_le measurable_const hf

theorem signBlockFunction_bounded {f : ℝ → ℝ} (hf : Measurable f) :
    BoundedObservable unitMeasure (signBlockFunction f) := by
  refine ⟨?_,1,by norm_num,?_⟩
  · exact (Measurable.ite (positiveSignBlock_measurable hf) measurable_const measurable_const).aemeasurable
  · exact Eventually.of_forall fun x => by dsimp [signBlockFunction]; split_ifs <;> norm_num

/-- A normalized mean-zero bounded function has substantial mass in each sign
block, and its sign function is close in L². -/
theorem sign_blocks_estimates {f : ℝ → ℝ} {M : ℝ} (hM : 0<M)
    (hf : Measurable f) (hb : ∀ᵐ x ∂unitMeasure, |f x|≤M)
    (hm : ∫ x, f x ∂unitMeasure=0) (hn : ∫ x, f x^2 ∂unitMeasure=1) :
    1≤M ∧
    1/(2*M^2)≤unitMeasure.real (positiveSignBlock f) ∧
    unitMeasure.real (positiveSignBlock f)≤1-1/(2*M^2) ∧
    1/(2*M^2)≤unitMeasure.real (positiveSignBlock f)ᶜ ∧
    unitMeasure.real (positiveSignBlock f)ᶜ≤1-1/(2*M^2) ∧
    (∫ x, (signBlockFunction f x-f x)^2 ∂unitMeasure)=2-2*(∫ x, |f x| ∂unitMeasure) ∧
    (∫ x, (signBlockFunction f x-f x)^2 ∂unitMeasure)≤2-2/M := by
  have hbo : BoundedObservable unitMeasure f := ⟨hf.aemeasurable,M,hM.le,hb⟩
  have hi := hbo.integrable
  have hsq : Integrable (fun x => f x^2) unitMeasure := by
    simpa only [pow_two] using (hbo.mul hbo).integrable
  have hsqle : ∀ᵐ x ∂unitMeasure, f x^2≤M^2 := by
    filter_upwards [hb] with x hx
    have hh := (sq_le_sq₀ (abs_nonneg _) hM.le).mpr hx
    simpa only [sq_abs] using hh
  have hM1 : 1≤M := by
    have hh := integral_mono_ae hsq (integrable_const (M^2)) hsqle
    rw [hn] at hh
    simp only [integral_const,measureReal_univ_eq_one,one_smul] at hh
    nlinarith
  have hL1 : 1≤M*(∫ x, |f x| ∂unitMeasure) := by
    have he : ∀ᵐ x ∂unitMeasure, f x^2≤M*|f x| := by
      filter_upwards [hb] with x hx
      have hh := mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))
      nlinarith [sq_abs (f x)]
    have hh := integral_mono_ae hsq (hi.norm.const_mul M) he
    rwa [hn,integral_const_mul] at hh
  let P := positiveSignBlock f
  have hP : MeasurableSet P := positiveSignBlock_measurable hf
  have hmP := integral_add_compl hP hi
  rw [hm] at hmP
  have hL := integral_add_compl hP hi.norm
  have hpabs : (∫ x in P, |f x| ∂unitMeasure)=∫ x in P, f x ∂unitMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hP] with x hx
    exact abs_of_nonneg hx
  have hnabs : (∫ x in Pᶜ, |f x| ∂unitMeasure)=-(∫ x in Pᶜ, f x ∂unitMeasure) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hP.compl] with x hx
    exact abs_of_nonpos (le_of_not_ge hx)
  simp only [Real.norm_eq_abs] at hL
  rw [hpabs,hnabs] at hL
  have hiP : (∫ x, |f x| ∂unitMeasure)=2*(∫ x in P, f x ∂unitMeasure) := by linarith
  have hiN : (∫ x, |f x| ∂unitMeasure)=-2*(∫ x in Pᶜ, f x ∂unitMeasure) := by linarith
  have hPupper : (∫ x in P, f x ∂unitMeasure)≤M*unitMeasure.real P := by
    have hh := integral_mono_ae (μ := unitMeasure.restrict P) hi.integrableOn (integrable_const M)
      ((ae_restrict_of_ae hb).mono fun x hx => (le_abs_self _).trans hx)
    simpa [mul_comm] using hh
  have hNupper : -(∫ x in Pᶜ, f x ∂unitMeasure)≤M*unitMeasure.real Pᶜ := by
    have hh := integral_mono_ae (μ := unitMeasure.restrict Pᶜ) hi.neg.integrableOn (integrable_const M)
      ((ae_restrict_of_ae hb).mono fun x hx => (neg_le_abs _).trans hx)
    simpa [integral_neg,mul_comm] using hh
  have hloP : 1/(2*M^2)≤unitMeasure.real P := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*M^2)).mpr
    rw [hiP] at hL1
    nlinarith [mul_le_mul_of_nonneg_left hPupper hM.le]
  have hloN : 1/(2*M^2)≤unitMeasure.real Pᶜ := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*M^2)).mpr
    rw [hiN] at hL1
    nlinarith [mul_le_mul_of_nonneg_left hNupper hM.le]
  have hmass : unitMeasure.real P+unitMeasure.real Pᶜ=1 := by
    simpa using measureReal_add_measureReal_compl (μ := unitMeasure) hP
  have herr : (∫ x, (signBlockFunction f x-f x)^2 ∂unitMeasure)=
      2-2*(∫ x, |f x| ∂unitMeasure) := by
    have hiabs : Integrable (fun x => |f x|) unitMeasure := hi.norm
    have hi' : Integrable (fun x => 1+f x^2) unitMeasure := (integrable_const _).add hsq
    calc
      _ = ∫ x, (1+f x^2)-2*|f x| ∂unitMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [signBlockFunction]
          split_ifs with hx
          · rw [abs_of_nonneg hx]; ring
          · rw [abs_of_nonpos (le_of_not_ge hx)]; ring
      _ = _ := by
        rw [integral_sub hi' (hiabs.const_mul 2),integral_add (integrable_const _) hsq,
          integral_const_mul,hn]
        norm_num
  refine ⟨hM1,hloP,by linarith,hloN,by linarith,herr,?_⟩
  rw [herr]
  have hl : 1/M≤∫ x, |f x| ∂unitMeasure := (div_le_iff₀ hM).mpr (by nlinarith [hL1])
  have he : (2:ℝ)/M=2*(1/M) := by ring
  rw [he]
  linarith

/-- `eq:s7mass` for the actual leading eigenfunction of a small-target minimizer. -/
theorem smallTarget_eigenfunction_blocks (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
    1≤M ∧
    1/(2*M^2)≤unitMeasure.real (positiveSignBlock (S.eigenfunction 0)) ∧
    unitMeasure.real (positiveSignBlock (S.eigenfunction 0))≤1-1/(2*M^2) ∧
    1/(2*M^2)≤unitMeasure.real (positiveSignBlock (S.eigenfunction 0))ᶜ ∧
    unitMeasure.real (positiveSignBlock (S.eigenfunction 0))ᶜ≤1-1/(2*M^2) ∧
    (∫ x, (signBlockFunction (S.eigenfunction 0) x-S.eigenfunction 0 x)^2 ∂unitMeasure)=
      2-2*(∫ x, |S.eigenfunction 0 x| ∂unitMeasure) ∧
    (∫ x, (signBlockFunction (S.eigenfunction 0) x-S.eigenfunction 0 x)^2 ∂unitMeasure)≤2-2/M := by
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hev := smallTarget_centeredEigenvalue_pos external hr hU S
  have hμ := minimizer_multiplier_pos hr01 hU
  have hm := Section02.edgeDensity_mem_Icc U
  have hA : 0<edgeDensity U+graphonMultiplier U r*r^3 := by
    have hp := mul_pos hμ (pow_pos hr.1 3)
    linarith [hm.1]
  have hn : (∫ x, (S.eigenfunction 0 x)^2 ∂unitMeasure)=1 := by
    simpa only [pow_two,if_pos rfl] using S.orthonormal_integral 0 0
  exact sign_blocks_estimates (Real.sqrt_pos.mpr (div_pos hA hev)) (S.eigenfunction_measurable 0)
    (minimizer_eigenfunction_bound hSampling hr01 hU S hev)
    (centeredEigenfunction_mean_zero U S hev) hn

end SparseLowerTail.Section07

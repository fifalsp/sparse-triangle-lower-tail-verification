import SparseLowerTail.Section07.ResidualCodegree

/-! Normalized set averages and the degree estimates in `eq:s7Davg`.
All averages are actual restricted integrals. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

def setAverage (P : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in P, f x ∂unitMeasure)/unitMeasure.real P

theorem setAverage_const (P : Set ℝ) (hp : 0<unitMeasure.real P) (c : ℝ) :
    setAverage P (fun _ => c)=c := by
  dsimp [setAverage]
  rw [setIntegral_const,smul_eq_mul]
  exact mul_div_cancel_left₀ c (ne_of_gt hp)

theorem setAverage_const_mul (P : Set ℝ) (f : ℝ → ℝ) (c : ℝ) :
    setAverage P (fun x => c*f x)=c*setAverage P f := by
  dsimp [setAverage]
  rw [integral_const_mul]
  ring

theorem setAverage_add (P : Set ℝ) {f g : ℝ → ℝ}
    (hf : Integrable f unitMeasure) (hg : Integrable g unitMeasure) :
    setAverage P (fun x => f x+g x)=setAverage P f+setAverage P g := by
  dsimp [setAverage]
  rw [integral_add hf.integrableOn hg.integrableOn]
  ring

theorem setAverage_sub (P : Set ℝ) {f g : ℝ → ℝ}
    (hf : Integrable f unitMeasure) (hg : Integrable g unitMeasure) :
    setAverage P (fun x => f x-g x)=setAverage P f-setAverage P g := by
  dsimp [setAverage]
  rw [integral_sub hf.integrableOn hg.integrableOn]
  ring

theorem abs_setAverage_le (P : Set ℝ) (f : ℝ → ℝ) :
    |setAverage P f|≤setAverage P (fun x => |f x|) := by
  dsimp [setAverage]
  rw [abs_div,abs_of_nonneg (measureReal_nonneg)]
  exact div_le_div_of_nonneg_right abs_integral_le_integral_abs (measureReal_nonneg)

theorem setAverage_abs_le_global {P : Set ℝ} {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    setAverage P (fun x => |f x|)≤(∫ x, |f x| ∂unitMeasure)/unitMeasure.real P := by
  apply div_le_div_of_nonneg_right _ measureReal_nonneg
  exact setIntegral_le_integral hf.norm (Eventually.of_forall fun x => abs_nonneg _)

/-- A mean-zero function bounded above has a two-sided average bound on every
set of prescribed positive mass. -/
theorem setAverage_mean_zero_bounds {D : ℝ → ℝ} {η M : ℝ} {P : Set ℝ}
    (hD : Integrable D unitMeasure) (hzero : (∫ x, D x ∂unitMeasure)=0)
    (hη : 0≤η) (hupper : ∀ᵐ x ∂unitMeasure, D x≤η)
    (hM : 1≤M) (hP : MeasurableSet P)
    (hmass : 1/(2*M^2)≤unitMeasure.real P)
    (hL1 : (∫ x, |D x| ∂unitMeasure)≤2*η) :
    |setAverage P D|≤η*(2*M^2-1) ∧
      setAverage P (fun x => |D x|)≤4*M^2*η := by
  have hMpos : 0<M := by linarith
  have hp : 0<unitMeasure.real P := (by positivity : (0:ℝ)<1/(2*M^2)).trans_le hmass
  have hmul : 1≤unitMeasure.real P*(2*M^2) := (div_le_iff₀ (by positivity)).mp hmass
  have hsum := integral_add_compl hP hD
  rw [hzero] at hsum
  have hPupper : (∫ x in P, D x ∂unitMeasure)≤unitMeasure.real P*η := by
    have hh := integral_mono_ae (μ := unitMeasure.restrict P) hD.integrableOn
      (integrable_const η) (ae_restrict_of_ae hupper)
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hNupper : (∫ x in Pᶜ, D x ∂unitMeasure)≤(1-unitMeasure.real P)*η := by
    have hh := integral_mono_ae (μ := unitMeasure.restrict Pᶜ) hD.integrableOn
      (integrable_const η) (ae_restrict_of_ae hupper)
    simpa only [setIntegral_const,smul_eq_mul,measureReal_compl hP,measureReal_univ_eq_one] using hh
  have hratio : 1-unitMeasure.real P≤unitMeasure.real P*(2*M^2-1) := by nlinarith
  have hfac : 1≤2*M^2-1 := by nlinarith
  constructor
  · rw [abs_le]
    constructor
    · apply (le_div_iff₀ hp).mpr
      have hh := mul_le_mul_of_nonneg_right hratio hη
      nlinarith
    · apply (div_le_iff₀ hp).mpr
      have hh := mul_le_mul_of_nonneg_left hfac hη
      have hh' := mul_le_mul_of_nonneg_right hh hp.le
      nlinarith
  · apply (setAverage_abs_le_global hD).trans
    apply (div_le_iff₀ hp).mpr
    have hh := mul_le_mul_of_nonneg_left hmul (show 0≤2*η by positivity)
    nlinarith

/-- Mean-zero cancellation yields the sharper bound |⟨D,ψ⟩|≤Mη. -/
theorem mean_zero_pair_bound {D f : ℝ → ℝ} {M η : ℝ}
    (hD : BoundedObservable unitMeasure D) (hf : BoundedObservable unitMeasure f)
    (hfzero : (∫ x, f x ∂unitMeasure)=0) (hDzero : (∫ x, D x ∂unitMeasure)=0)
    (hupper : ∀ᵐ x ∂unitMeasure, D x≤η)
    (hbound : ∀ᵐ x ∂unitMeasure, |f x|≤M) :
    |∫ x, D x*f x ∂unitMeasure|≤M*η := by
  have hi : Integrable (fun x => (D x-η)*f x) unitMeasure := by
    convert (hD.mul hf).integrable.sub (hf.integrable.const_mul η) using 1
    funext x; dsimp; ring
  have hshift : (∫ x, D x*f x ∂unitMeasure)=∫ x, (D x-η)*f x ∂unitMeasure := by
    have he : (fun x => (D x-η)*f x)=(fun x => D x*f x-η*f x) := by funext x; ring
    rw [he,integral_sub (hD.mul hf).integrable (hf.integrable.const_mul η),integral_const_mul,hfzero]
    ring
  rw [hshift]
  have hu : Integrable (fun x => M*(η-D x)) unitMeasure :=
    ((integrable_const η).sub hD.integrable).const_mul M
  calc
    _ ≤ ∫ x, |(D x-η)*f x| ∂unitMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ x, M*(η-D x) ∂unitMeasure := by
      apply integral_mono_ae hi.norm hu
      filter_upwards [hupper,hbound] with x hx hfx
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonpos (sub_nonpos.mpr hx)]
      nlinarith [mul_le_mul_of_nonneg_left hfx (sub_nonneg.mpr hx)]
    _ = M*η := by
      rw [integral_const_mul,integral_sub (integrable_const _) hD.integrable,hDzero]
      simp

/-- The actual degree-sign covariance estimate used in the codegree bound. -/
theorem minimizer_degreeEigenfunctionPair_bound (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U)) (hev : 0<S.eigenvalue 0) :
    |degreeEigenfunctionPair U S|≤
      Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)*
        (graphonMultiplier U r*r^3/2) := by
  apply mean_zero_pair_bound (degreeDeviation_bounded U)
    (minimizer_eigenfunction_bounded hSampling hr hU S hev)
    (centeredEigenfunction_mean_zero U S hev) (integral_degreeDeviation U) _
    (minimizer_eigenfunction_bound hSampling hr hU S hev)
  filter_upwards [minimizer_degree_upper hSampling hr hU] with x hx
  dsimp [degreeDeviation]
  linarith

/-- `eq:s7Davg` for either of the actual eigenfunction sign blocks. -/
theorem smallTarget_degree_block_averages (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
    let η := graphonMultiplier U r*r^3/2
    ∀ P, P=positiveSignBlock (S.eigenfunction 0) ∨ P=(positiveSignBlock (S.eigenfunction 0))ᶜ →
      |setAverage P (degreeDeviation U)|≤η*(2*M^2-1) ∧
      setAverage P (fun x => |degreeDeviation U x|)≤4*M^2*η := by
  dsimp only
  intro P hP
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hμ := minimizer_multiplier_pos hr01 hU
  have hrpos := hr.1
  have hη : 0≤graphonMultiplier U r*r^3/2 := by positivity
  have hμeq := (smallTarget_optimizer_data external hr hU).2.2.1
  have hγ : 0≤branchMu (leftBranch r)/3 := by rw [← hμeq]; positivity
  have hdeg := penalized_degree_estimates hSampling hr01 hγ hU
    ((smallTarget_data external hr).2 U hU).2.2
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hmeas : MeasurableSet P := by
    rcases hP with rfl | rfl
    · exact positiveSignBlock_measurable (S.eigenfunction_measurable 0)
    · exact (positiveSignBlock_measurable (S.eigenfunction_measurable 0)).compl
  have hmass : 1/(2*(Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0))^2)
      ≤unitMeasure.real P := by
    rcases hP with rfl | rfl
    · exact hblocks.2.1
    · exact hblocks.2.2.2.1
  refine setAverage_mean_zero_bounds (degreeDeviation_bounded U).integrable
    (integral_degreeDeviation U) hη ?_ hblocks.1 hmeas hmass ?_
  · filter_upwards [hdeg.1] with x hx
    dsimp [degreeDeviation]
    linarith [hx.2]
  · linarith [hdeg.2.1]

end SparseLowerTail.Section07

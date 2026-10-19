import SparseLowerTail.Section07.SmallErrorSums
import SparseLowerTail.Section07.SmallParameterBounds

/-! Complete smallparams(b) scalar bounds and their actual graphon inputs. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section07
open Section04 Numerics

namespace SmallErrorData

theorem error_bounds (d : SmallErrorData) :
    rowEulerError d.mu d.eta d.m d.ev d.bound d.tail d.diagonal<114/1000 ∧
    rowMeanError d.eta d.ev d.bound d.tail d.diagonal<3/1000 ∧
    (2-2*d.m-d.mu*d.t)+1-(d.bound^2)⁻¹<1005/1000 ∧
    4987/10000<1/(2*d.bound^2) ∧ d.m+d.eta≤5006/10000 := by
  have hEc := d.weighted_codegree_upper
  have hEm := d.weighted_mean_upper
  have hE0 := d.weighted_base_upper
  have hmut := mul_nonneg d.mu_pos.le d.triangle_nonneg
  have hsqpos : 0<d.bound^2 := by nlinarith [d.bound_one_le]
  have hinv : (1002575/1000000:ℝ)⁻¹≤(d.bound^2)⁻¹ :=
    inv_anti₀ hsqpos d.bound_sq_upper.le
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp only [rowEulerError]
    nlinarith
  · by_contra hn
    have hh : 3/1000≤rowMeanError d.eta d.ev d.bound d.tail d.diagonal := le_of_not_gt hn
    have hm := mul_le_mul d.mu_lower hh (by norm_num : (0:ℝ)≤3/1000) d.mu_pos.le
    nlinarith
  · norm_num at hinv
    nlinarith [d.mean_lower]
  · apply (lt_div_iff₀ (by positivity : 0<2*d.bound^2)).mpr
    nlinarith [d.bound_sq_upper]
  · linarith [d.mean_upper,d.eta_upper]

end SmallErrorData

/-- Every actual small-target minimizer supplies the explicit scalar hypotheses.
This definition adds no assumed graphon or numerical statement. -/
def smallTargetErrorData (external : KP26PenalizedReduction) {r : ℝ}
    (hr : r∈Ioc (0:ℝ) smallTarget) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U)) : SmallErrorData := by
  have hd := smallTarget_optimizer_data external hr hU
  have hs := smallTarget_support hr
  have hp := small_parameter_bounds hs.1.1
    (hs.1.2.trans penalizedCrossing_lt_smallUpper.le)
  rw [hs.2.2.2,←hd.2.2.1,←hd.2.2.2] at hp
  have ht := centeredSpectrum_tail_inequalities U S
  rw [hd.1] at ht
  exact {
    m := edgeDensity U
    mu := graphonMultiplier U r
    t := r^3
    ev := S.eigenvalue 0
    mean_lower := by linarith [hp.1.1]
    mean_upper := hp.1.2
    mu_lower := by linarith [hp.2.1]
    triangle_nonneg := pow_nonneg hr.1.le 3
    triangle_upper := hp.2.2.1
    mut_upper := by linarith [hp.2.2.2.1]
    mu2t_upper := hp.2.2.2.2.1
    mean_defect := by linarith [hp.2.2.2.2.2]
    eigenvalue_pos := smallTarget_centeredEigenvalue_pos external hr hU S
    eigenvalue_upper := centeredEigenvalue_le_mean U S 0
    spectral_first := ht.1
    spectral_second := ht.2 }

/-- An exact multiplier identity puts the vertex mean in the form used by the error table. -/
theorem vertexMean_penalty_form {r : ℝ} (hr : r≠0) (U : Graphon) :
    vertexMean U r=2-2*edgeDensity U-graphonMultiplier U r*r^3 := by
  have hmu : graphonMultiplier U r*r^3=1-cost U-edgeDensity U := by
    unfold graphonMultiplier
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hr)
  rw [vertexMean_eq hr]
  linarith

/-- Actual small-target error bounds; the first four are scalar, the last is
an almost-everywhere bound on the actual graphon degree. -/
theorem smallTarget_error_bounds (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let μ := graphonMultiplier U r
    let m := edgeDensity U
    let ev := S.eigenvalue 0
    let η := μ*r^3/2
    let A := m+μ*r^3
    let M := Real.sqrt (A/ev)
    rowEulerError μ η m ev M (m-ev) A<114/1000 ∧
    rowMeanError η ev M (m-ev) A<3/1000 ∧
    vertexMean U r+1-(M^2)⁻¹<1005/1000 ∧
    4987/10000<1/(2*M^2) ∧
    (∀ᵐ x ∂unitMeasure,rowDegree U x≤5006/10000) := by
  let d := smallTargetErrorData external hr hU S
  have hb := d.error_bounds
  refine ⟨hb.1,hb.2.1,?_,hb.2.2.2.1,?_⟩
  · rw [vertexMean_penalty_form hr.1.ne' U]
    exact hb.2.2.1
  · have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
    filter_upwards [minimizer_degree_upper hSampling hr01 hU] with x hx
    exact hx.trans hb.2.2.2.2

end SparseLowerTail.Section07

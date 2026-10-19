import SparseLowerTail.Section02.BlockAveraging

/-! The entropy continuity estimate used to pass from L¹ block approximation to cost. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

def l1Distance (U W : Graphon) : ℝ := ∫ p, |U p-W p| ∂squareMeasure

theorem l1Distance_nonneg (U W : Graphon) : 0 ≤ l1Distance U W :=
  integral_nonneg fun _ => abs_nonneg _

/-- Uniform continuity and 0≤h≤1 give a global affine error bound. -/
theorem entropy_uniform_error {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      |entropy u-entropy v| ≤ ε+|u-v|/δ := by
  have hu : UniformContinuousOn entropy (Icc (0:ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous continuous_entropy.continuousOn
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro u hu v hv
  by_cases hclose : |u-v| < δ
  · have h := hd u hu v hv (by simpa only [Real.dist_eq] using hclose)
    rw [Real.dist_eq] at h
    exact h.le.trans (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hδ.le))
  · have hmax : |entropy u-entropy v| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [entropy_nonneg hu.1, entropy_nonneg hv.1, entropy_le_one hu, entropy_le_one hv]
    have hlarge : 1 ≤ |u-v|/δ := (le_div_iff₀ hδ).mpr (by simpa using le_of_not_gt hclose)
    linarith

/-- Integral form of the preceding modulus, for genuine graphons. -/
theorem cost_error_bound {ε δ : ℝ} (_hδ : 0 < δ)
    (herr : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, |entropy u-entropy v| ≤ ε+|u-v|/δ)
    (U W : Graphon) : |cost U-cost W| ≤ ε+l1Distance U W/δ := by
  have hnorm := ((cost_integrable U).sub (cost_integrable W)).norm
  have hdist := ((graphon_integrable U).sub (graphon_integrable W)).norm
  have hmono := integral_mono_ae hnorm ((integrable_const ε).add (hdist.div_const δ))
    (show (fun p => |entropy (U p)-entropy (W p)|) ≤ᵐ[squareMeasure]
      (fun p => ε+|U p-W p|/δ) from by
        filter_upwards [U.bounded,W.bounded] with p hp hq
        exact herr (U p) hp (W p) hq)
  have hnormint := norm_integral_le_integral_norm
    (f := fun p => entropy (U p)-entropy (W p)) (μ := squareMeasure)
  rw [integral_sub (cost_integrable U) (cost_integrable W)] at hnormint
  simp only [Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply] at hmono hdist
  rw [integral_add (f := fun _ => ε) (g := fun p => |U p-W p|/δ)
    (integrable_const ε) (hdist.div_const δ), integral_div] at hmono
  simp only [Real.norm_eq_abs, integral_const, measureReal_univ_eq_one,
    smul_eq_mul, one_mul] at hnormint hmono
  exact hnormint.trans hmono

/-- Entropy cost is continuous under L¹ convergence of graphons. -/
theorem cost_tendsto_of_l1 {U : ℕ → Graphon} {W : Graphon}
    (h : Tendsto (fun n => l1Distance (U n) W) atTop (𝓝 0)) :
    Tendsto (fun n => cost (U n)) atTop (𝓝 (cost W)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,herr⟩ := entropy_uniform_error (show 0 < ε/2 by linarith)
  have hp : 0 < ε*δ/2 := by positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp h (ε*δ/2) hp
  refine ⟨N,?_⟩
  intro n hn
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (l1Distance_nonneg _ _)] at hsmall
  have hb := cost_error_bound hδ herr (U n) W
  have hd : l1Distance (U n) W/δ < ε/2 := (div_lt_iff₀ hδ).mpr (by nlinarith [hsmall])
  rw [Real.dist_eq]
  linarith

/-- Own-paper entropy convergence, derived from the authorized classical L¹ approximation. -/
theorem cost_dyadic_tendsto (hclass : ClassicalDyadicL1Approximation) (U : Graphon) :
    Tendsto (fun k => cost (averagedGraphon (dyadicPartition k) U)) atTop (𝓝 (cost U)) :=
  cost_tendsto_of_l1 (hclass U.toFun (graphon_integrable U))

end SparseLowerTail.Section02

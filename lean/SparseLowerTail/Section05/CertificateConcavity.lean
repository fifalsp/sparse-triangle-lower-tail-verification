import SparseLowerTail.Section05.CoverDefinitions
import Mathlib.Analysis.Convex.Jensen

/-! Actual certificate concavity and finite-vertex interpolation (`lem:concave`).
The exact quadratic remainder is proved, so the claim concerns the certificate
defined from all twelve features, not an abstract concavity assumption. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05

theorem certificateFeature_affine (i : Fin 12) (u : EdgeTriple)
    (π ρ : ℝ × ℝ) (s : ℝ) :
    certificateFeature i u (s • π+(1-s) • ρ) =
      s*certificateFeature i u π+(1-s)*certificateFeature i u ρ := by
  fin_cases i <;>
    simp [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,
      relaxationMultiplier,relaxationVertexMean,coverCycle] <;> ring

theorem certificateHoeffding_mix (u : EdgeTriple) (π ρ : ℝ × ℝ) (s : ℝ) :
    certificateHoeffding u (s • π+(1-s) • ρ) =
      s*certificateHoeffding u π+(1-s)*certificateHoeffding u ρ-
        s*(1-s)*((π.1+criticalOmega*π.2)-(ρ.1+criticalOmega*ρ.2))^2 := by
  simp [certificateHoeffding,cyclicAverage,coverCycle]
  ring

/-- The only nonlinear parameter dependence is the negative square in H*. -/
theorem coverCertificate_mix (θ : Fin 12 → ℝ) (lam : ℝ) (u : EdgeTriple)
    (π ρ : ℝ × ℝ) (s : ℝ) :
    coverCertificate θ lam u (s • π+(1-s) • ρ) =
      s*coverCertificate θ lam u π+(1-s)*coverCertificate θ lam u ρ+
        lam*s*(1-s)*((π.1+criticalOmega*π.2)-(ρ.1+criticalOmega*ρ.2))^2 := by
  have hlin : (∑ i, θ i*certificateFeature i u (s • π+(1-s) • ρ)) =
      s*(∑ i, θ i*certificateFeature i u π)+(1-s)*(∑ i, θ i*certificateFeature i u ρ) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [certificateFeature_affine]
    ring
  unfold coverCertificate
  rw [hlin,certificateHoeffding_mix]
  ring

/-- `lem:concave`: concavity holds on the whole parameter plane. -/
theorem coverCertificate_concave (θ : Fin 12 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (u : EdgeTriple) : ConcaveOn ℝ univ (coverCertificate θ lam u) := by
  refine ⟨convex_univ,?_⟩
  intro π _ ρ _ a b ha hb hab
  have hb' : b=1-a := by linarith
  subst b
  rw [coverCertificate_mix]
  simp only [smul_eq_mul]
  have hp := mul_nonneg (mul_nonneg (mul_nonneg hlam ha) hb)
    (sq_nonneg ((π.1+criticalOmega*π.2)-(ρ.1+criticalOmega*ρ.2)))
  linarith

/-- The finite polygon-vertex inequality in `lem:concave`. -/
theorem coverCertificate_le_map_sum {ι : Type*} (t : Finset ι)
    (θ : Fin 12 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (u : EdgeTriple)
    (w : ι → ℝ) (v : ι → ℝ × ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hsum : ∑ i ∈ t, w i = 1) :
    (∑ i ∈ t, w i*coverCertificate θ lam u (v i)) ≤
      coverCertificate θ lam u (∑ i ∈ t, w i • v i) := by
  simpa only [smul_eq_mul] using
    (coverCertificate_concave θ hlam u).le_map_sum hw hsum (fun _ _ => mem_univ _)

end SparseLowerTail.Section05

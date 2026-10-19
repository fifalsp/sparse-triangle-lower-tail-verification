import SparseLowerTail.Section05.CoverCertificate

/-! Coordinate-permutation symmetry of the actual certificate functions.
This justifies reducing interval verification to ordered coordinate boxes. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section04

/-- Each actual feature is invariant under the first generating transposition. -/
theorem certificateFeature_swap12 (i : Fin 12) (u : EdgeTriple) (π : ℝ × ℝ) :
    certificateFeature i (edgeSwap12 u) π = certificateFeature i u π := by
  fin_cases i <;> simp only [certificateFeature,Matrix.cons_val_zero',Matrix.cons_val_succ',
    cyclicAverage,coverEdgeResidual,coverVertexResidual,coverCycle,edgeSwap12_apply]
  all_goals ring

/-- Each actual feature is invariant under the second generating transposition. -/
theorem certificateFeature_swap23 (i : Fin 12) (u : EdgeTriple) (π : ℝ × ℝ) :
    certificateFeature i (edgeSwap23 u) π = certificateFeature i u π := by
  fin_cases i <;> simp only [certificateFeature,Matrix.cons_val_zero',Matrix.cons_val_succ',
    cyclicAverage,coverEdgeResidual,coverVertexResidual,coverCycle,edgeSwap23_apply]
  all_goals ring

theorem certificateHoeffding_swap12 (u : EdgeTriple) (π : ℝ × ℝ) :
    certificateHoeffding (edgeSwap12 u) π = certificateHoeffding u π := by
  simp only [certificateHoeffding,cyclicAverage,coverCycle,edgeSwap12_apply]
  ring

theorem certificateHoeffding_swap23 (u : EdgeTriple) (π : ℝ × ℝ) :
    certificateHoeffding (edgeSwap23 u) π = certificateHoeffding u π := by
  simp only [certificateHoeffding,cyclicAverage,coverCycle,edgeSwap23_apply]
  ring

/-- Certificates can be checked on one coordinate ordering because Ψ is symmetric. -/
theorem coverCertificate_swap12 (θ : Fin 12 → ℝ) (lam : ℝ) (u : EdgeTriple) (π : ℝ × ℝ) :
    coverCertificate θ lam (edgeSwap12 u) π = coverCertificate θ lam u π := by
  simp only [coverCertificate,certificateFeature_swap12,certificateHoeffding_swap12]

theorem coverCertificate_swap23 (θ : Fin 12 → ℝ) (lam : ℝ) (u : EdgeTriple) (π : ℝ × ℝ) :
    coverCertificate θ lam (edgeSwap23 u) π = coverCertificate θ lam u π := by
  simp only [coverCertificate,certificateFeature_swap23,certificateHoeffding_swap23]

theorem coverCertificate_permutationWord (θ : Fin 12 → ℝ) (lam : ℝ)
    (w : List Bool) (u : EdgeTriple) (π : ℝ × ℝ) :
    coverCertificate θ lam (edgePermutationWord w u) π = coverCertificate θ lam u π := by
  induction w generalizing u with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => exact (ih (edgeSwap12 u)).trans (coverCertificate_swap12 θ lam u π)
    | true => exact (ih (edgeSwap23 u)).trans (coverCertificate_swap23 θ lam u π)

end SparseLowerTail.Section05

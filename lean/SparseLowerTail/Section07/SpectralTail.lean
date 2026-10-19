import SparseLowerTail.Section07.SpectralEigenfunctions

/-! The spectral-moment upper bounds in `eq:s7tail`, proved from the actual
trace bound. The remaining lower moment bound comes from the cubic block identity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section07
open Section04

/-- A nonnegative summable sequence has cubic sum at most the cube of its sum. -/
theorem tsum_cube_le_cube_tsum {a : ℕ → ℝ} (ha : ∀ i, 0≤a i)
    (hs : Summable a) (hc : Summable (fun i => a i^3)) :
    (∑' i, a i^3)≤(∑' i, a i)^3 := by
  let t := ∑' i, a i
  have ht : 0≤t := tsum_nonneg ha
  have hi (i : ℕ) : a i≤t := hs.le_tsum i (fun j _ => ha j)
  have hp (i : ℕ) : a i^3≤t^2*a i := by
    have hsq : (a i)^2≤t^2 := by nlinarith [ha i,hi i]
    nlinarith [mul_le_mul_of_nonneg_right hsq (ha i)]
  have hh := hc.tsum_le_tsum hp (hs.mul_left (t^2))
  rw [tsum_mul_left] at hh
  change (∑' i, a i^3)≤t^3
  nlinarith

/-- Every centered eigenvalue is at most the graphon edge density. -/
theorem centeredEigenvalue_le_mean (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (i : ℕ) : S.eigenvalue i≤edgeDensity U :=
  ((centeredKernel_trace_bound U S).1.le_tsum i (fun j _ => S.eigenvalue_nonneg j)).trans
    (centeredKernel_trace_bound U S).2

/-- Cubic spectral mass is at most mλ², where λ is the largest eigenvalue. -/
theorem centeredSpectrum_cube_le_top (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    (∑' i, S.eigenvalue i^3)≤edgeDensity U*(S.eigenvalue 0)^2 := by
  have hs := (centeredKernel_trace_bound U S).1
  have hbound (i : ℕ) : S.eigenvalue i^3≤(S.eigenvalue 0)^2*S.eigenvalue i := by
    have hi := S.eigenvalue_antitone (Nat.zero_le i)
    have hi0 := S.eigenvalue_nonneg i
    have h0 := S.eigenvalue_nonneg 0
    have hsq : S.eigenvalue i^2≤S.eigenvalue 0^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hi0]
  have hh := S.cube_summable.tsum_le_tsum hbound (hs.mul_left _)
  rw [tsum_mul_left] at hh
  have htrace := (centeredKernel_trace_bound U S).2
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left htrace (sq_nonneg (S.eigenvalue 0))])

/-- The tail has mass at most m−λ and cubic mass at most (m−λ)³. -/
theorem centeredSpectrum_tail_bounds (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    (∑' i, S.eigenvalue (i+1))≤edgeDensity U-S.eigenvalue 0 ∧
    (∑' i, S.eigenvalue (i+1)^3)≤(edgeDensity U-S.eigenvalue 0)^3 := by
  have hs := (centeredKernel_trace_bound U S).1
  have htail : Summable (fun i => S.eigenvalue (i+1)) := (summable_nat_add_iff 1).mpr hs
  have htailcube : Summable (fun i => S.eigenvalue (i+1)^3) :=
    (summable_nat_add_iff 1).mpr S.cube_summable
  have ht : (∑' i, S.eigenvalue (i+1))≤edgeDensity U-S.eigenvalue 0 := by
    have hh := (centeredKernel_trace_bound U S).2
    rw [hs.tsum_eq_zero_add] at hh
    linarith
  refine ⟨ht,?_⟩
  have hh := tsum_cube_le_cube_tsum (fun i => S.eigenvalue_nonneg (i+1)) htail htailcube
  exact hh.trans (pow_le_pow_left₀ (tsum_nonneg fun i => S.eigenvalue_nonneg (i+1)) ht 3)

/-- The second moment upper bound used to obtain 3mλ(m−λ)≤t. -/
theorem centeredSpectrum_cube_le_tail (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    (∑' i, S.eigenvalue i^3)≤edgeDensity U^3-
      3*edgeDensity U*S.eigenvalue 0*(edgeDensity U-S.eigenvalue 0) := by
  have hh := (centeredSpectrum_tail_bounds U S).2
  rw [S.cube_summable.tsum_eq_zero_add]
  nlinarith

end SparseLowerTail.Section07

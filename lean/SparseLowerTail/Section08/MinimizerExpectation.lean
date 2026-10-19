import SparseLowerTail.Section08.CertificateExpectation
import SparseLowerTail.Section04.EulerLagrange

/-!
# Certificate expectations for actual minimizers

Discharges the Euler equation, positive lower bound, and active constraint in
`s8:expect` using `prop:euler` and `lem:active`. The last theorem isolates the
remaining certificate-positivity input explicitly; it does not prove that input.
-/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Certificate
open Section04 TriangleIntegration

theorem minimizer_psi_integrable {r : ℝ} (hr : r ∈ Ioo 0 1)
    {U : Graphon} (hU : IsMinimizer r U) (z : ℝ) :
    Integrable (fun p => psi z (X U p) (Y U p) (Z U p)) tripleMeasure :=
  psi_integrable z U (Real.exp_pos _) (minimizer_lower_bound hr hU)

/-- The certificate expectation identity with no additional regularity or
stationarity hypotheses on the minimizer. -/
theorem minimizer_expectation_identity {r z : ℝ} (hr : r ∈ Ioo 0 1)
    {U : Graphon} (hU : IsMinimizer r U)
    (ht : balancedTriangle (branchA z) (branchB z) = r ^ 3) :
    expectation z U = 3*c1 z*(edgeDensity U-(branchA z+branchB z)/2) +
      3*(branchMu z-graphonMultiplier U r)*
        (c2 z*balancedTriangle (branchA z) (branchB z) +
          c3 z*(∫ p, codegree U p.1 p.2 ∂squareMeasure) +
          c4 z*(∫ p, U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure)) :=
  expectation_identity z U (Real.exp_pos _) (minimizer_lower_bound hr hU)
    ((minimizer_triangle_eq hr hU).trans ht.symm) (minimizer_log_equation hr hU)

/-- Matching the branch cost and edge density fixes the explicit multiplier. -/
theorem multiplier_eq_branch_of_matching_data {r z : ℝ} (hr : 0 < r)
    (hz : z ∈ Ioo 0 1) {U : Graphon}
    (ht : balancedTriangle (branchA z) (branchB z) = r ^ 3)
    (hF : cost U = balancedCost (branchA z) (branchB z))
    (he : edgeDensity U = (branchA z+branchB z)/2) :
    graphonMultiplier U r = branchMu z := by
  have hb := balancedEL_multiplier_cost (branch_balancedEL hz.1 hz.2)
  rw [ht] at hb
  unfold graphonMultiplier
  rw [hF, he, ← hb]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ (ne_of_gt hr))

/-- This is the zero-expectation step used after the small-target data have
been established. Matching data are internal hypotheses, not assumed theorems. -/
theorem minimizer_expectation_zero_of_matching_data {r z : ℝ}
    (hr : r ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U)
    (ht : balancedTriangle (branchA z) (branchB z) = r ^ 3)
    (hF : cost U = balancedCost (branchA z) (branchB z))
    (he : edgeDensity U = (branchA z+branchB z)/2) :
    expectation z U = 0 := by
  rw [minimizer_expectation_identity hr hU ht,
    multiplier_eq_branch_of_matching_data hr.1 hz ht hF he, he]
  ring

/-- Nonnegative certificates with zero expectation vanish almost everywhere.
Certificate positivity remains an explicit, still-to-be-proved input. -/
theorem minimizer_certificate_zero_ae {r z : ℝ} (hr : r ∈ Ioo 0 1)
    {U : Graphon} (hU : IsMinimizer r U)
    (hzero : expectation z U = 0)
    (hpos : ∀ᵐ p ∂tripleMeasure, 0 ≤ psi z (X U p) (Y U p) (Z U p)) :
    ∀ᵐ p ∂tripleMeasure, psi z (X U p) (Y U p) (Z U p) = 0 := by
  exact (integral_eq_zero_iff_of_nonneg_ae hpos
    (minimizer_psi_integrable hr hU z)).mp hzero

end SparseLowerTail.Certificate

import SparseLowerTail.Section07.ExternalReduction
import SparseLowerTail.Section04.EulerLagrange

/-! The multiplier part of `lem:penalized`. Truncation extends penalized
optimality to bounded nonnegative kernels, so multiplicative variations are
admissible on both sides without any unproved Euler assumption. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

/-- Nonnegative penalties decrease under truncation to a graphon. -/
theorem penalized_le_nonnegativeKernel {γ : ℝ} (hγ : 0 ≤ γ) {U : Graphon}
    (hpen : ∀ W : Graphon, cost U+γ*triangle U ≤ cost W+γ*triangle W)
    (W : NonnegativeKernel) : cost U+γ*triangle U ≤ W.cost+γ*W.triangle :=
  (hpen W.truncate).trans (add_le_add W.cost_truncate_le
    (mul_le_mul_of_nonneg_left W.triangle_truncate_le hγ))

/-- A global penalized minimum has vanishing multiplicative first variation. -/
theorem penalized_firstVariation {γ : ℝ} (hγ : 0 ≤ γ) {U : Graphon}
    (hpen : ∀ W : Graphon, cost U+γ*triangle U ≤ cost W+γ*triangle W)
    (D : ℝ × ℝ → ℝ) (hD : BoundedObservable squareMeasure D)
    (hDs : ∀ᵐ p ∂squareMeasure, D p.swap=D p) :
    (∫ p, U p*Real.log (U p)*D p ∂squareMeasure)+
      γ*(3*∫ p, (U p*D p)*codegree U p.1 p.2 ∂squareMeasure)=0 := by
  let W := expTilt U D hD hDs
  have hc0 : (W 0).cost=cost U := by simp [W,NonnegativeKernel.cost,expTilt,cost]
  have ht0 : (W 0).triangle=triangle U := by
    simp [W,NonnegativeKernel.triangle,expTilt,triangle]
  have hmin : IsLocalMin (fun s => (W s).cost+γ*(W s).triangle) 0 := by
    apply Eventually.of_forall
    intro s
    change (W 0).cost+γ*(W 0).triangle ≤ (W s).cost+γ*(W s).triangle
    rw [hc0,ht0]
    exact penalized_le_nonnegativeKernel hγ hpen (W s)
  exact hmin.hasDerivAt_eq_zero ((hasDerivAt_expTilt_cost U D hD hDs).add
    ((hasDerivAt_expTilt_triangle U D hD hDs).const_mul γ))

/-- The integral stationary identity for a global penalized minimizer. -/
theorem penalized_integral_identity {γ : ℝ} (hγ : 0 ≤ γ) {U : Graphon}
    (hpen : ∀ W : Graphon, cost U+γ*triangle U ≤ cost W+γ*triangle W) :
    (∫ p, U p*Real.log (U p) ∂squareMeasure)+3*γ*triangle U=0 := by
  have h := penalized_firstVariation hγ hpen (fun _ => 1)
    (BoundedObservable.const 1) (Eventually.of_forall fun _ => rfl)
  simp only [mul_one] at h
  rw [← triangle_eq_integral_codegree] at h
  nlinarith

/-- The constrained multiplier equals three times any supporting global penalty. -/
theorem minimizer_multiplier_eq_three_penalty {r γ : ℝ} (hr : r ∈ Ioo (0:ℝ) 1)
    (hγ : 0 ≤ γ) {U : Graphon} (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U ≤ cost W+γ*triangle W) :
    graphonMultiplier U r=3*γ := by
  have h := penalized_integral_identity hγ hpen
  rw [minimizer_triangle_eq hr hU] at h
  have hm := graphonMultiplier_integral_identity (U := U) (ne_of_gt hr.1)
  have hp : 0<r^3 := pow_pos hr.1 3
  nlinarith

end SparseLowerTail.Section07

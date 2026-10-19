import SparseLowerTail.Section04.Unimodal
import SparseLowerTail.Section04.BalancedStationary
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Derivative of the balanced stationary cost

Stable manuscript anchor: `lem:Bderivative`(b). We prove the envelope cancellation
on the stationary branch, then change from the branch parameter to the triangle
target along a continuous local inverse of `branchRho`. The local inverse and
nonvanishing derivative assumptions are explicit; no global inverse branch or
crossing statement is assumed implicitly.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section04

/-- The entropy cost `F(B_z)` along the stationary branch. -/
def branchCost (z : ℝ) : ℝ := balancedCost (branchA z) (branchB z)

theorem contDiffAt_branchA {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ContDiffAt ℝ 1 branchA z :=
  contDiffAt_id.mul (contDiffAt_branchB hz hz1)

theorem contDiffAt_branchMu {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ContDiffAt ℝ 1 branchMu z := by
  have hL : ContDiffAt ℝ 1 branchLog z := by
    have he : branchLog = fun x => -Real.log x := funext branchLog_eq_neg_log
    rw [he]
    exact (Real.contDiffAt_log.mpr (ne_of_gt hz)).neg
  exact (contDiffAt_const.mul hL).div
    (((contDiffAt_const.sub contDiffAt_id).pow 2).mul
      ((contDiffAt_branchB hz hz1).pow 2))
    (mul_ne_zero (pow_ne_zero _ (ne_of_gt (sub_pos.mpr hz1)))
      (pow_ne_zero _ (ne_of_gt (branchB_pos z))))

theorem contDiffAt_branchCost {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ContDiffAt ℝ 1 branchCost z := by
  have ha := contDiffAt_branchA hz hz1
  have hb := contDiffAt_branchB hz hz1
  have hea : ContDiffAt ℝ 1 (fun x => entropy (branchA x)) z :=
    ((ha.mul (ha.log (ne_of_gt (branchA_pos hz)))).sub ha).add contDiffAt_const
  have heb : ContDiffAt ℝ 1 (fun x => entropy (branchB x)) z :=
    ((hb.mul (hb.log (ne_of_gt (branchB_pos z)))).sub hb).add contDiffAt_const
  exact (hea.add heb).div_const 2

/-- The scalar target `ρ` is the actual cube root of the branch density. -/
theorem branch_triangle_eq_rho_cube {z : ℝ} (hz : 0 < z) :
    balancedTriangle (branchA z) (branchB z) = branchRho z ^ 3 := by
  obtain ⟨ha, hb⟩ := branch_eq_scaled_ray hz
  rw [ha, hb, scaled_ray_triangle hz]

/-- Cost differentiation along any positive differentiable pair. -/
theorem hasDerivAt_balancedCost_path {a b : ℝ → ℝ} {a' b' x : ℝ}
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x)
    (hap : 0 < a x) (hbp : 0 < b x) :
    HasDerivAt (fun y => balancedCost (a y) (b y))
      ((Real.log (a x) * a' + Real.log (b x) * b') / 2) x :=
  (((hasDerivAt_entropy (ne_of_gt hap)).comp x ha).add
    ((hasDerivAt_entropy (ne_of_gt hbp)).comp x hb)).div_const 2

/-- Triangle differentiation along any differentiable pair. -/
theorem hasDerivAt_balancedTriangle_path {a b : ℝ → ℝ} {a' b' x : ℝ}
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) :
    HasDerivAt (fun y => balancedTriangle (a y) (b y))
      ((3 * (a x ^ 2 + b x ^ 2) * a' + 6 * a x * b x * b') / 4) x := by
  convert ((ha.pow 3).add ((ha.const_mul 3).mul (hb.pow 2))).div_const 4 using 1
  norm_num
  ring

/-- The EL equations give the envelope cancellation `C' = -(μ/3)t'`. -/
theorem balancedEL_derivative_identity {a b μ a' b' : ℝ} (hel : BalancedEL a b μ) :
    (Real.log a * a' + Real.log b * b') / 2 =
      -(μ / 3) * ((3 * (a ^ 2 + b ^ 2) * a' + 6 * a * b * b') / 4) := by
  rw [hel.1, hel.2]
  ring

/-- Derivative of `F(B_z)` before changing from `z` to the target `ρ(z)`. -/
theorem hasDerivAt_branchCost {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasDerivAt branchCost
      (-branchMu z * branchRho z ^ 2 * deriv branchRho z) z := by
  have ha := ((contDiffAt_branchA hz hz1).differentiableAt (by norm_num)).hasDerivAt
  have hb := ((contDiffAt_branchB hz hz1).differentiableAt (by norm_num)).hasDerivAt
  have hr := ((contDiffAt_branchRho hz hz1).differentiableAt (by norm_num)).hasDerivAt
  have ht := hasDerivAt_balancedTriangle_path ha hb
  have hcost := hasDerivAt_balancedCost_path ha hb (branchA_pos hz) (branchB_pos z)
  have heq : (fun x => balancedTriangle (branchA x) (branchB x)) =ᶠ[𝓝 z]
      (fun x => branchRho x ^ 3) := by
    filter_upwards [eventually_gt_nhds hz] with x hx
    exact branch_triangle_eq_rho_cube hx
  have hder := ht.unique ((hr.pow 3).congr_of_eventuallyEq heq)
  simp only [Nat.cast_ofNat, Nat.reduceSub] at hder
  have hel := balancedEL_derivative_identity (a' := deriv branchA z)
    (b' := deriv branchB z) (branch_balancedEL hz hz1)
  rw [hder] at hel
  convert hcost using 1
  nlinarith [hel]

/-- The cost of the actual stationary graphon is the scalar branch cost. -/
theorem branchGraphon_cost {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    cost (branchGraphon z hz hz1) = branchCost z := by
  have h := branchGraphon_isBalanced hz hz1
  obtain ⟨ha, hb⟩ := h.values_mem_Icc
  exact h.cost_eq ha hb

/-- `lem:Bderivative`(b), pointwise, for any differentiable local inverse.
Differentiability of the inverse is an explicit calculus input here. -/
theorem hasDerivAt_branchCost_of_differentiable_inverse {σ : ℝ → ℝ} {r σ' : ℝ}
    (hz : σ r ∈ Ioo (0 : ℝ) 1) (hσ : HasDerivAt σ σ' r)
    (hinv : ∀ᶠ t in 𝓝 r, branchRho (σ t) = t) :
    HasDerivAt (fun t => branchCost (σ t)) (-branchMu (σ r) * r ^ 2) r := by
  have he : branchRho (σ r) = r := hinv.self_of_nhds
  have hrho := ((contDiffAt_branchRho hz.1 hz.2).differentiableAt (by norm_num)).hasDerivAt
  have hder := (hrho.comp r hσ).unique ((hasDerivAt_id r).congr_of_eventuallyEq hinv)
  have hcost := (hasDerivAt_branchCost hz.1 hz.2).comp r hσ
  rw [he] at hcost
  convert hcost using 1
  nlinarith [congrArg (fun x : ℝ => -branchMu (σ r) * r ^ 2 * x) hder]

/-- A continuous local inverse is differentiable wherever `ρ'` is nonzero.
Thus inverse differentiability is discharged by the classical inverse rule,
not taken as an assumption in the main derivative interface. -/
theorem hasDerivAt_branchCost_of_local_inverse {σ : ℝ → ℝ} {r : ℝ}
    (hz : σ r ∈ Ioo (0 : ℝ) 1) (hσ : ContinuousAt σ r)
    (hn : deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ᶠ t in 𝓝 r, branchRho (σ t) = t) :
    HasDerivAt (fun t => branchCost (σ t)) (-branchMu (σ r) * r ^ 2) r := by
  have hrho := ((contDiffAt_branchRho hz.1 hz.2).differentiableAt (by norm_num)).hasDerivAt
  exact hasDerivAt_branchCost_of_differentiable_inverse hz
    (hrho.of_local_left_inverse hσ hn hinv) hinv

/-- Interval version of the pointwise inverse interface. -/
theorem hasDerivAt_branchCost_on_inverse {J : Set ℝ} (hJ : IsOpen J)
    {σ : ℝ → ℝ} (hσ : ContinuousOn σ J) (hz : MapsTo σ J (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ J, deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ r ∈ J, branchRho (σ r) = r) {r : ℝ} (hr : r ∈ J) :
    HasDerivAt (fun t => branchCost (σ t)) (-branchMu (σ r) * r ^ 2) r := by
  apply hasDerivAt_branchCost_of_local_inverse (hz hr)
    (hσ.continuousAt (hJ.mem_nhds hr)) (hn r hr)
  filter_upwards [hJ.mem_nhds hr] with t ht
  exact hinv t ht

/-- Continuous differentiability in `lem:Bderivative`(b), conditional only on
identifying a continuous inverse branch with nonzero `ρ'`. The cost derivative
and its continuity are proved, rather than included among the hypotheses. -/
theorem contDiffOn_branchCost_inverse {J : Set ℝ} (hJ : IsOpen J)
    {σ : ℝ → ℝ} (hσ : ContinuousOn σ J) (hz : MapsTo σ J (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ J, deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ r ∈ J, branchRho (σ r) = r) :
    ContDiffOn ℝ 1 (fun t => branchCost (σ t)) J := by
  have hder := fun r hr => hasDerivAt_branchCost_on_inverse hJ hσ hz hn hinv (r := r) hr
  have hμ : ContinuousOn branchMu (Ioo (0 : ℝ) 1) := by
    intro z hz
    exact (contDiffAt_branchMu hz.1 hz.2).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun r => -branchMu (σ r) * r ^ 2) J :=
    (hμ.comp hσ hz).neg.mul (continuousOn_id.pow 2)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen hJ]
  refine ⟨fun r hr => (hder r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · rw [contDiffOn_zero]
    apply hc.congr
    intro r hr
    exact (hder r hr).deriv

/-- Literal derivative formula from `lem:Bderivative`(b) on an inverse branch. -/
theorem deriv_branchCost_inverse {J : Set ℝ} (hJ : IsOpen J)
    {σ : ℝ → ℝ} (hσ : ContinuousOn σ J) (hz : MapsTo σ J (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ J, deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ r ∈ J, branchRho (σ r) = r) {r : ℝ} (hr : r ∈ J) :
    deriv (fun t => branchCost (σ t)) r = -branchMu (σ r) * r ^ 2 :=
  (hasDerivAt_branchCost_on_inverse hJ hσ hz hn hinv hr).deriv

end SparseLowerTail.Section04

import SparseLowerTail.Section07.Fold
import Mathlib.Analysis.Calculus.DerivativeTest

/-! Second-order necessity for the actual scalar penalized minimizer. The
Hessian restriction is derived from line variations, rather than assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

private theorem second_derivative_nonneg_of_localMin {f : ℝ → ℝ} {x d : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) (hd : HasDerivAt (deriv f) d x) :
    0 ≤ d := by
  by_contra hn
  have hneg : deriv (deriv f) x < 0 := by rw [hd.deriv]; exact lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin,hmax] with y hy hz
    exact le_antisymm hz hy
  have hh := he.deriv.deriv_eq
  have he' : deriv (fun _ : ℝ => f x) = fun _ => (0:ℝ) := funext (fun y => deriv_const y (f x))
  rw [he',deriv_const] at hh
  rw [hd.deriv] at hh
  linarith

private def penaltyLineFirst (γ a b v w t : ℝ) : ℝ :=
  (Real.log (a+t*v)*v+Real.log (b+t*w)*w)/2+
    γ*(3*((a+t*v)^2+(b+t*w)^2)*v+6*(a+t*v)*(b+t*w)*w)/4

private theorem hasDerivAt_penalty_line (γ a b v w t : ℝ)
    (ha : 0<a+t*v) (hb : 0<b+t*w) :
    HasDerivAt (fun s => balancedPenalty γ (a+s*v) (b+s*w))
      (penaltyLineFirst γ a b v w t) t := by
  have hdA : HasDerivAt (fun s => a+s*v) v t := by
    simpa using ((hasDerivAt_id t).mul_const v).const_add a
  have hdB : HasDerivAt (fun s => b+s*w) w t := by
    simpa using ((hasDerivAt_id t).mul_const w).const_add b
  convert (hasDerivAt_balancedCost_path hdA hdB ha hb).add
    ((hasDerivAt_balancedTriangle_path hdA hdB).const_mul γ) using 1
  unfold penaltyLineFirst
  ring

private theorem hasDerivAt_penaltyLineFirst (γ a b v w : ℝ) (ha : 0<a) (hb : 0<b) :
    HasDerivAt (penaltyLineFirst γ a b v w)
      (((1/a+3*γ*a)/2)*v^2+3*γ*b*v*w+((1/b+3*γ*a)/2)*w^2) 0 := by
  have hdA : HasDerivAt (fun s : ℝ => a+s*v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v).const_add a
  have hdB : HasDerivAt (fun s : ℝ => b+s*w) w 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const w).const_add b
  have hlogA := hdA.log (by simpa using ne_of_gt ha)
  have hlogB := hdB.log (by simpa using ne_of_gt hb)
  have hh := (((hlogA.mul_const v).add (hlogB.mul_const w)).div_const 2).add
    (((((((hdA.pow 2).add (hdB.pow 2)).const_mul 3).mul_const v).add
      (((hdA.const_mul 6).mul hdB).mul_const w)).const_mul γ).div_const 4)
  convert hh using 1
  dsimp
  ring

/-- Every line direction has nonnegative second variation at an interior scalar
minimum. This is the actual positive-semidefinite Hessian condition. -/
theorem penalizedMinimizer_secondVariation {γ a b : ℝ} (hγ : 0<γ)
    (h : IsBalancedPenalizedMinimizer γ a b) (v w : ℝ) :
    0 ≤ ((1/a+3*γ*a)/2)*v^2+3*γ*b*v*w+((1/b+3*γ*a)/2)*w^2 := by
  have hi := penalizedMinimizer_interior hγ h
  let f : ℝ → ℝ := fun s => balancedPenalty γ (a+s*v) (b+s*w)
  have hA : ∀ᶠ s in 𝓝 (0:ℝ), a+s*v ∈ Ioo (0:ℝ) 1 := by
    have hc : ContinuousAt (fun s : ℝ => a+s*v) 0 := by fun_prop
    apply hc.tendsto.eventually
    simpa only [zero_mul,add_zero] using
      (show ∀ᶠ x in 𝓝 a, x ∈ Ioo (0:ℝ) 1 from isOpen_Ioo.mem_nhds hi.1)
  have hB : ∀ᶠ s in 𝓝 (0:ℝ), b+s*w ∈ Ioo (0:ℝ) 1 := by
    have hc : ContinuousAt (fun s : ℝ => b+s*w) 0 := by fun_prop
    apply hc.tendsto.eventually
    simpa only [zero_mul,add_zero] using
      (show ∀ᶠ x in 𝓝 b, x ∈ Ioo (0:ℝ) 1 from isOpen_Ioo.mem_nhds hi.2)
  have hmin : IsLocalMin f 0 := by
    filter_upwards [hA,hB] with s hs ht
    simpa [f] using h.2.2 (a+s*v) (b+s*w) ⟨hs.1.le,hs.2.le⟩ ⟨ht.1.le,ht.2.le⟩
  have he : deriv f =ᶠ[𝓝 (0:ℝ)] penaltyLineFirst γ a b v w := by
    filter_upwards [hA,hB] with s hs ht
    exact (hasDerivAt_penalty_line γ a b v w s hs.1 ht.1).deriv
  have hd := (hasDerivAt_penaltyLineFirst γ a b v w hi.1.1 hi.2.1).congr_of_eventuallyEq he
  have hc : ContinuousAt f 0 :=
    (hasDerivAt_penalty_line γ a b v w 0 (by simpa using hi.1.1) (by simpa using hi.2.1)).continuousAt
  exact second_derivative_nonneg_of_localMin hmin hc hd

/-- The determinant inequality follows from the proved positive quadratic form. -/
theorem penalizedMinimizer_hessianDet_nonneg {γ a b : ℝ} (hγ : 0<γ)
    (h : IsBalancedPenalizedMinimizer γ a b) : 0 ≤ penalizedHessianDet γ a b := by
  let A := (1/a+3*γ*a)/2
  let B := (1/b+3*γ*a)/2
  let C := 3*γ*b/2
  have ha := (penalizedMinimizer_interior hγ h).1.1
  have hA : 0<A := by dsimp [A]; positivity
  have hh := penalizedMinimizer_secondVariation hγ h (-C) A
  have hid : ((1/a+3*γ*a)/2)*(-C)^2+3*γ*b*(-C)*A+((1/b+3*γ*a)/2)*A^2 =
      A*penalizedHessianDet γ a b := by unfold A C penalizedHessianDet; ring
  rw [hid] at hh
  exact nonneg_of_mul_nonneg_right hh hA

/-- The unstable branch beyond the fold cannot be a penalized minimizer. -/
theorem penalizedMinimizer_branch_le_fold {γ a b : ℝ} (hγ : 0<γ)
    (h : IsBalancedPenalizedMinimizer γ a b) (hne : a≠b) : a/b ≤ foldPoint := by
  obtain ⟨_,hz,ha,hb,hm⟩ := penalizedMinimizer_branch hγ h hne
  have hd := penalizedMinimizer_hessianDet_nonneg hγ h
  have hγeq : γ=branchMu (a/b)/3 := by rw [hm]; ring
  rw [hγeq,ha,hb] at hd
  have hd' : 0 ≤ penalizedHessianDet (branchMu (a/b)/3) (branchA (a/b)) (branchB (a/b)) := by
    simpa only [← ha,← hb] using hd
  rw [penalizedHessianDet_branch hz] at hd'
  have hq : foldQ (a/b) ≤ 1 := by
    have hden : 0<4*(a/b)*(branchB (a/b))^2 := by
      have hp := hz.1
      have hbpos := branchB_pos (a/b)
      positivity
    have hh := (le_div_iff₀ hden).mp hd'
    simpa only [zero_mul,sub_nonneg] using hh
  exact (strictMonoOn_foldQ.le_iff_le hz foldPoint_spec.1).mp (by rwa [foldPoint_spec.2])

end SparseLowerTail.Section07

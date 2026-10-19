import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! Taylor lower bounds for future interval-certificate leaves.
These are proved classical analysis lemmas. Instantiating them for a certificate
still requires checking its derivatives and derivative enclosures on the leaf. -/
noncomputable section
namespace SparseLowerTail.Numerics
open Set

/-- A second-derivative lower bound on a whole segment gives a Taylor lower
bound at its endpoint. Intended for x ↦ Ψ(center+x*displacement). -/
theorem segment_taylor_lower {f f₁ f₂ : ℝ → ℝ} {M : ℝ}
    (h₁ : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ x) x)
    (hbound : ∀ x ∈ Icc (0:ℝ) 1, -M ≤ f₂ x) :
    f 0+f₁ 0-M/2 ≤ f 1 := by
  let g : ℝ → ℝ := fun x => f x+(M/2)*x^2
  let g₁ : ℝ → ℝ := fun x => f₁ x+M*x
  have hg₁ : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt g (g₁ x) x := by
    intro x hx
    convert (h₁ x hx).add (((hasDerivAt_id x).pow 2).const_mul (M/2)) using 1
    dsimp [g,g₁]
    ring
  have hg₂ : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt g₁ (f₂ x+M) x := by
    intro x hx
    simpa only [g₁,mul_one] using (h₂ x hx).add ((hasDerivAt_id x).const_mul M)
  have hc : ConvexOn ℝ (Icc (0:ℝ) 1) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun x hx => (hg₁ x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg₁ x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (hg₂ x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    linarith [hbound x (interior_subset hx)]
  have hs := hc.le_slope_of_hasDerivAt (by norm_num) (by norm_num) zero_lt_one
    (hg₁ 0 (by norm_num))
  norm_num [slope,g,g₁] at hs
  linarith

/-- A certified affine-plus-quadratic lower bound can be weakened to a positive
leaf margin using only real arithmetic. -/
theorem segment_taylor_positive {f f₁ f₂ : ℝ → ℝ} {M L : ℝ}
    (h₁ : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ x) x)
    (hbound : ∀ x ∈ Icc (0:ℝ) 1, -M ≤ f₂ x)
    (hmargin : L < f 0+f₁ 0-M/2) : L < f 1 :=
  hmargin.trans_le (segment_taylor_lower h₁ h₂ hbound)

end SparseLowerTail.Numerics

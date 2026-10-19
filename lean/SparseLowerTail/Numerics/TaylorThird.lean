import SparseLowerTail.Numerics.TaylorBounds

/-! Third-order segment bounds for checked Taylor certificates. -/
noncomputable section
namespace SparseLowerTail.Numerics
open Set

private theorem unitSegment_monotone {f f' : ℝ→ℝ}
    (hd : ∀ x∈Icc (0:ℝ) 1,HasDerivAt f (f' x) x)
    (hp : ∀ x∈Icc (0:ℝ) 1,0≤f' x) : MonotoneOn f (Icc (0:ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  exact fun x hx => hp x (interior_subset hx)

/-- A uniform lower bound on the third derivative gives the signed Taylor
remainder bound. The lower bound need not be negative. -/
theorem segment_taylor3_lower {f f₁ f₂ f₃ : ℝ→ℝ} {L : ℝ}
    (h₁ : ∀ x∈Icc (0:ℝ) 1,HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x∈Icc (0:ℝ) 1,HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x∈Icc (0:ℝ) 1,HasDerivAt f₂ (f₃ x) x)
    (hL : ∀ x∈Icc (0:ℝ) 1,L≤f₃ x) :
    f 0+f₁ 0+f₂ 0/2+L/6≤f 1 := by
  have hm₂ : MonotoneOn (fun x => f₂ x-L*x) (Icc (0:ℝ) 1) := by
    apply unitSegment_monotone (f' := fun x => f₃ x-L)
    · intro x hx
      simpa using (h₃ x hx).sub ((hasDerivAt_id x).const_mul L)
    · intro x hx
      linarith [hL x hx]
  have hb₂ : ∀ x∈Icc (0:ℝ) 1,f₂ 0+L*x≤f₂ x := by
    intro x hx
    have hh := hm₂ (by norm_num) hx hx.1
    simp only [mul_zero,sub_zero] at hh
    linarith
  have hm₁ : MonotoneOn (fun x => f₁ x-f₂ 0*x-(L/2)*x^2) (Icc (0:ℝ) 1) := by
    apply unitSegment_monotone (f' := fun x => f₂ x-f₂ 0-L*x)
    · intro x hx
      convert ((h₂ x hx).sub ((hasDerivAt_id x).const_mul (f₂ 0))).sub
        (((hasDerivAt_id x).pow 2).const_mul (L/2)) using 1 <;> simp only [id_eq] <;> ring
    · intro x hx
      linarith [hb₂ x hx]
  have hb₁ : ∀ x∈Icc (0:ℝ) 1,f₁ 0+f₂ 0*x+(L/2)*x^2≤f₁ x := by
    intro x hx
    have hh := hm₁ (by norm_num) hx hx.1
    norm_num at hh
    linarith
  have hm : MonotoneOn (fun x => f x-f₁ 0*x-(f₂ 0/2)*x^2-(L/6)*x^3)
      (Icc (0:ℝ) 1) := by
    apply unitSegment_monotone (f' := fun x => f₁ x-f₁ 0-f₂ 0*x-(L/2)*x^2)
    · intro x hx
      convert (((h₁ x hx).sub ((hasDerivAt_id x).const_mul (f₁ 0))).sub
        (((hasDerivAt_id x).pow 2).const_mul (f₂ 0/2))).sub
        (((hasDerivAt_id x).pow 3).const_mul (L/6)) using 1 <;> simp only [id_eq] <;> ring
    · intro x hx
      linarith [hb₁ x hx]
  have hh := hm (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤1)
  norm_num at hh
  linarith

end SparseLowerTail.Numerics

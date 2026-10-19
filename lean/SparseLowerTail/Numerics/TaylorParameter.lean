import SparseLowerTail.Numerics.TaylorThird

/-! Taylor bounds on a parameter segment in either direction. The hypotheses
are actual derivatives on the segment, not numerical derivative estimates. -/
noncomputable section
namespace SparseLowerTail.Numerics
open Set

/-- Second-order Taylor expansion with an absolute third-order remainder.
The endpoint may lie on either side of the center. -/
theorem parameter_taylor3_abs {f f₁ f₂ f₃ : ℝ → ℝ} {c d M : ℝ}
    (h₁ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ (c+s*d)) (c+s*d))
    (h₂ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ (c+s*d)) (c+s*d))
    (h₃ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f₂ (f₃ (c+s*d)) (c+s*d))
    (hM : ∀ s ∈ Icc (0:ℝ) 1, |f₃ (c+s*d)| ≤ M) :
    |f (c+d)-(f c+d*f₁ c+d^2*f₂ c/2)| ≤ M*|d|^3/6 := by
  have hp (s : ℝ) : HasDerivAt (fun u : ℝ => c+u*d) d s := by
    simpa using ((hasDerivAt_id s).mul_const d).const_add c
  have hd₁ : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun u => f (c+u*d)) (d*f₁ (c+s*d)) s := by
    intro s hs
    simpa [mul_comm] using (h₁ s hs).comp s (hp s)
  have hd₂ : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun u => d*f₁ (c+u*d)) (d^2*f₂ (c+s*d)) s := by
    intro s hs
    convert ((h₂ s hs).comp s (hp s)).const_mul d using 1 <;> ring
  have hd₃ : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun u => d^2*f₂ (c+u*d)) (d^3*f₃ (c+s*d)) s := by
    intro s hs
    convert ((h₃ s hs).comp s (hp s)).const_mul (d^2) using 1 <;> ring
  have hb : ∀ s ∈ Icc (0:ℝ) 1, |d^3*f₃ (c+s*d)| ≤ M*|d|^3 := by
    intro s hs
    rw [abs_mul,abs_pow,mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM s hs) (pow_nonneg (abs_nonneg _) _)
  have hlo := segment_taylor3_lower hd₁ hd₂ hd₃
    (fun s hs => (neg_le_neg (hb s hs)).trans (neg_abs_le _))
  have hhi := segment_taylor3_lower (fun s hs => (hd₁ s hs).neg)
    (fun s hs => (hd₂ s hs).neg) (fun s hs => (hd₃ s hs).neg)
    (fun s hs => neg_le_neg ((le_abs_self _).trans (hb s hs)))
  simp only [Pi.neg_apply,zero_mul,add_zero,one_mul] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The lower bound used by the parameter part of the family certificate.
The quadratic term retains its sign; only the odd-order errors are absolute. -/
theorem parameter_taylor3_lower {f f₁ f₂ f₃ : ℝ → ℝ} {c d w M : ℝ}
    (h₁ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ (c+s*d)) (c+s*d))
    (h₂ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ (c+s*d)) (c+s*d))
    (h₃ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f₂ (f₃ (c+s*d)) (c+s*d))
    (hM : ∀ s ∈ Icc (0:ℝ) 1, |f₃ (c+s*d)| ≤ M)
    (hd : |d| ≤ w) :
    f c-|f₁ c| *w+min 0 (f₂ c)*w^2/2-M*w^3/6 ≤ f (c+d) := by
  have hw : 0≤w := (abs_nonneg d).trans hd
  have hM0 : 0≤M := (abs_nonneg _).trans (hM 0 (by norm_num))
  have hlin : -(|f₁ c| *w)≤d*f₁ c := by
    have h := mul_le_mul_of_nonneg_right hd (abs_nonneg (f₁ c))
    rw [←abs_mul] at h
    nlinarith [neg_abs_le (d*f₁ c)]
  have hd2 : d^2≤w^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hquad : min 0 (f₂ c)*w^2≤d^2*f₂ c := by
    calc
      min 0 (f₂ c)*w^2 ≤ min 0 (f₂ c)*d^2 :=
        mul_le_mul_of_nonpos_left hd2 (min_le_left _ _)
      _ ≤ f₂ c*d^2 := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hcube : |d|^3 ≤ w^3 := pow_le_pow_left₀ (abs_nonneg _) hd 3
  have herr := mul_le_mul_of_nonneg_left hcube hM0
  have ht := (abs_le.mp (parameter_taylor3_abs h₁ h₂ h₃ hM)).1
  linarith

end SparseLowerTail.Numerics

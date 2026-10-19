import SparseLowerTail.Numerics.DyadicTaylorAxes

/-! Diagonal-aware Taylor bounds with semantically verified, potentially
factored gradient and Hessian expressions. -/
namespace SparseLowerTail.Numerics
open Set PolynomialExpr
namespace DyadicInterval

/-- For displacement intervals containing zero this is the sharp square
interval up to outward rounding. It remains sound for every interval. -/
def square (I : DyadicInterval) : DyadicInterval :=
  ⟨0,ceilDiv (max (I.lower^2) (I.upper^2)) scale⟩

theorem square_contains {I : DyadicInterval} {x : ℝ} (hx : I.contains x) :
    I.square.contains (x*x) := by
  have hs := scale_real_pos
  have hbound : x^2≤max (((I.lower:ℝ)/scale)^2) (((I.upper:ℝ)/scale)^2) := by
    rcases le_total x 0 with h | h
    · have hp := mul_nonneg (sub_nonneg.mpr hx.1)
        (show 0≤-x-(I.lower:ℝ)/scale by linarith [hx.1])
      exact (by nlinarith : x^2≤((I.lower:ℝ)/scale)^2).trans (le_max_left _ _)
    · have hp := mul_nonneg (sub_nonneg.mpr hx.2)
        (show 0≤(I.upper:ℝ)/scale+x by linarith [hx.2])
      exact (by nlinarith : x^2≤((I.upper:ℝ)/scale)^2).trans (le_max_right _ _)
  have htop := (rounded_div_bounds (max (I.lower^2) (I.upper^2)) scale scale_pos).2
  have he : (max (I.lower^2) (I.upper^2):ℤ)/(scale:ℝ)/scale=
      max (((I.lower:ℝ)/scale)^2) (((I.upper:ℝ)/scale)^2) := by
    push_cast
    rw [←max_div_div_right hs.le, ←max_div_div_right hs.le]
    simp only [div_pow]
    ring_nf
  refine ⟨?_,?_⟩
  · simpa [square] using mul_self_nonneg x
  · change x*x≤(ceilDiv (max (I.lower^2) (I.upper^2)) scale:ℝ)/scale
    rw [he] at htop
    nlinarith

end DyadicInterval

def dyadicVelocityProduct (velocity : Fin 3→DyadicInterval) (i j : Fin 3) : DyadicInterval :=
  if i=j then (velocity i).square else (velocity i).mul (velocity j)

theorem dyadicVelocityProduct_contains {velocity : Fin 3→DyadicInterval} {v : Fin 3→ℝ}
    (hv : ∀ i,(velocity i).contains (v i)) (i j : Fin 3) :
    (dyadicVelocityProduct velocity i j).contains (v i*v j) := by
  by_cases he : i=j
  · subst j
    simpa [dyadicVelocityProduct] using DyadicInterval.square_contains (hv i)
  · simpa [dyadicVelocityProduct,he] using DyadicInterval.mul_contains (hv i) (hv j)

def dyadicFactoredGradient {n : ℕ} (g : Fin 3→PolynomialExpr n)
    (start : Fin n→DyadicInterval) (velocity : Fin 3→DyadicInterval) : DyadicInterval :=
  DyadicInterval.sumThree (fun i => (velocity i).mul ((g i).dyadicEval start))

def dyadicFactoredHessian {n : ℕ} (h : Fin 3→Fin 3→PolynomialExpr n)
    (whole : Fin n→DyadicInterval) (velocity : Fin 3→DyadicInterval) : DyadicInterval :=
  DyadicInterval.sumThree (fun i => DyadicInterval.sumThree (fun j =>
    (dyadicVelocityProduct velocity i j).mul ((h i j).dyadicEval whole)))

theorem dyadic_factored_taylor_lower {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n)
    (g : Fin 3→PolynomialExpr n) (h : Fin 3→Fin 3→PolynomialExpr n)
    (hg : ∀ i y,(g i).realEval y=(e.derivative (d i)).realEval y)
    (hh : ∀ i j y,(h i j).realEval y=((e.derivative (d i)).derivative (d j)).realEval y)
    (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval)
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i)) :
    ((e.dyadicEval start).lower : ℝ)/DyadicInterval.scale+
      ((dyadicFactoredGradient g start velocity).lower:ℝ)/DyadicInterval.scale+
      ((dyadicFactoredHessian h whole velocity).lower:ℝ)/DyadicInterval.scale/2 ≤ e.realEval (x 1) := by
  let f₁ := fun s => sumThree (fun i => v i*(e.derivative (d i)).realEval (x s))
  let f₂ := fun s => sumThree (fun i => sumThree (fun j =>
    v i*v j*((e.derivative (d i)).derivative (d j)).realEval (x s)))
  have h₁ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt (fun t => e.realEval (x t)) (f₁ s) s :=
    fun s hs => e.hasDerivAt_three d v (hx s hs)
  have h₂ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ s) s := by
    intro s hs
    have h0 := ((e.derivative (d 0)).hasDerivAt_three d v (hx s hs)).const_mul (v 0)
    have h1 := ((e.derivative (d 1)).hasDerivAt_three d v (hx s hs)).const_mul (v 1)
    have h2 := ((e.derivative (d 2)).hasDerivAt_three d v (hx s hs)).const_mul (v 2)
    convert (h0.add h1).add h2 using 1 <;> dsimp [f₁,f₂,sumThree] <;> ring
  have hb : ∀ s ∈ Icc (0:ℝ) 1,
      -(-((dyadicFactoredHessian h whole velocity).lower : ℝ)/DyadicInterval.scale) ≤ f₂ s := by
    intro s hs
    have H : (dyadicFactoredHessian h whole velocity).contains (f₂ s) := by
      apply DyadicInterval.sumThree_contains
      intro i
      apply DyadicInterval.sumThree_contains
      intro j
      have H := DyadicInterval.mul_contains (dyadicVelocityProduct_contains hv i j)
        ((h i j).dyadicEval_contains (hwhole s hs))
      simpa only [hh] using H
    simpa only [neg_div,neg_neg] using H.1
  have H0 := (e.dyadicEval_contains hstart).1
  have H1 : (dyadicFactoredGradient g start velocity).contains (f₁ 0) := by
    apply DyadicInterval.sumThree_contains
    intro i
    have H := DyadicInterval.mul_contains (hv i) ((g i).dyadicEval_contains hstart)
    simpa only [hg] using H
  have H := segment_taylor_lower h₁ h₂ hb
  simp only [neg_div,sub_neg_eq_add] at H
  linarith [H1.1]

def dyadicFactoredTaylorMargin {n : ℕ} (e : PolynomialExpr n)
    (g : Fin 3→PolynomialExpr n) (h : Fin 3→Fin 3→PolynomialExpr n) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) : ℤ :=
  2*(e.dyadicEval start).lower+2*(dyadicFactoredGradient g start velocity).lower+
    (dyadicFactoredHessian h whole velocity).lower

theorem dyadic_factored_taylor_margin_lower {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n)
    (g : Fin 3→PolynomialExpr n) (h : Fin 3→Fin 3→PolynomialExpr n)
    (hg : ∀ i y,(g i).realEval y=(e.derivative (d i)).realEval y)
    (hh : ∀ i j y,(h i j).realEval y=((e.derivative (d i)).derivative (d j)).realEval y)
    (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval)
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i)) :
    (dyadicFactoredTaylorMargin e g h start whole velocity:ℝ)/(2*DyadicInterval.scale)≤
      e.realEval (x 1) := by
  convert dyadic_factored_taylor_lower e d g h hg hh v x start whole velocity hv hx hstart hwhole using 1
  unfold dyadicFactoredTaylorMargin
  push_cast
  ring

theorem dyadic_factored_taylor_positive {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n)
    (g : Fin 3→PolynomialExpr n) (h : Fin 3→Fin 3→PolynomialExpr n)
    (hg : ∀ i y,(g i).realEval y=(e.derivative (d i)).realEval y)
    (hh : ∀ i j y,(h i j).realEval y=((e.derivative (d i)).derivative (d j)).realEval y)
    (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval)
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i))
    (hmargin : 0<dyadicFactoredTaylorMargin e g h start whole velocity) :
    0<e.realEval (x 1) := by
  apply lt_of_lt_of_le _ (dyadic_factored_taylor_margin_lower e d g h hg hh v x start whole velocity hv hx hstart hwhole)
  apply div_pos (by exact_mod_cast hmargin)
  exact mul_pos (by norm_num) DyadicInterval.scale_real_pos

end SparseLowerTail.Numerics

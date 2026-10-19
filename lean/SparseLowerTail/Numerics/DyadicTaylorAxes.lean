import SparseLowerTail.Numerics.DyadicInterval
import SparseLowerTail.Numerics.IntervalTaylorAxes

/-! Fixed-precision Taylor bounds with an integer-only final margin check. -/
namespace SparseLowerTail.Numerics
open Set PolynomialExpr
set_option linter.unnecessarySeqFocus false

def DyadicInterval.sumThree (f : Fin 3 → DyadicInterval) : DyadicInterval :=
  ((f 0).add (f 1)).add (f 2)

theorem DyadicInterval.sumThree_contains {I : Fin 3 → DyadicInterval}
    {x : Fin 3 → ℝ} (hx : ∀ i, (I i).contains (x i)) :
    (DyadicInterval.sumThree I).contains (SparseLowerTail.Numerics.sumThree x) :=
  DyadicInterval.add_contains (DyadicInterval.add_contains (hx 0) (hx 1)) (hx 2)

def dyadicGradientInterval {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (start : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) : DyadicInterval :=
  DyadicInterval.sumThree (fun i => (velocity i).mul ((e.derivative (d i)).dyadicEval start))

def dyadicHessianInterval {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) : DyadicInterval :=
  DyadicInterval.sumThree (fun i => DyadicInterval.sumThree (fun j =>
    ((velocity i).mul (velocity j)).mul
      (((e.derivative (d i)).derivative (d j)).dyadicEval whole)))

theorem dyadic_taylor_axes_lower {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval)
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i)) :
    ((e.dyadicEval start).lower : ℝ)/DyadicInterval.scale+
      ((dyadicGradientInterval e d start velocity).lower:ℝ)/DyadicInterval.scale+
      ((dyadicHessianInterval e d whole velocity).lower:ℝ)/DyadicInterval.scale/2 ≤ e.realEval (x 1) := by
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
      -(-((dyadicHessianInterval e d whole velocity).lower : ℝ)/DyadicInterval.scale) ≤ f₂ s := by
    intro s hs
    have H : (dyadicHessianInterval e d whole velocity).contains (f₂ s) := by
      apply DyadicInterval.sumThree_contains
      intro i
      apply DyadicInterval.sumThree_contains
      intro j
      exact DyadicInterval.mul_contains (DyadicInterval.mul_contains (hv i) (hv j))
        (((e.derivative (d i)).derivative (d j)).dyadicEval_contains (hwhole s hs))
    simpa only [neg_div,neg_neg] using H.1
  have H0 := (e.dyadicEval_contains hstart).1
  have H1 : (dyadicGradientInterval e d start velocity).contains (f₁ 0) := by
    apply DyadicInterval.sumThree_contains
    intro i
    exact DyadicInterval.mul_contains (hv i) ((e.derivative (d i)).dyadicEval_contains hstart)
  have H := segment_taylor_lower h₁ h₂ hb
  simp only [neg_div,sub_neg_eq_add] at H
  linarith [H1.1]

def dyadicTaylorMargin {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) : ℤ :=
  2*(e.dyadicEval start).lower+2*(dyadicGradientInterval e d start velocity).lower+
    (dyadicHessianInterval e d whole velocity).lower

theorem dyadic_taylor_axes_margin_lower {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval)
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i)) :
    (dyadicTaylorMargin e d start whole velocity:ℝ)/(2*DyadicInterval.scale)≤
      e.realEval (x 1) := by
  convert dyadic_taylor_axes_lower e d v x start whole velocity hv hx hstart hwhole using 1
  unfold dyadicTaylorMargin
  push_cast
  ring

theorem dyadic_taylor_axes_positive {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval)
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i))
    (hmargin : 0<dyadicTaylorMargin e d start whole velocity) :
    0<e.realEval (x 1) := by
  apply lt_of_lt_of_le _ (dyadic_taylor_axes_margin_lower e d v x start whole velocity hv hx hstart hwhole)
  apply div_pos (by exact_mod_cast hmargin)
  exact mul_pos (by norm_num) DyadicInterval.scale_real_pos

end SparseLowerTail.Numerics

import SparseLowerTail.Numerics.PolynomialSimplify
import SparseLowerTail.Numerics.TaylorBounds

/-! A checked Taylor leaf for any reified expression and differentiable path.
All numerical input is rational interval data; no analytic derivative conclusion
or external numerical success flag is assumed. -/
namespace SparseLowerTail.Numerics
open Set PolynomialExpr

/-- The lower value, directional gradient and directional Hessian enclosures
combine to give a lower bound throughout any path parametrized by [0,1]. -/
theorem interval_taylor2_lower {n : ℕ} (e : PolynomialExpr n)
    (d : Fin n → PolynomialExpr n) (x : ℝ → Fin n → ℝ)
    (start whole : Fin n → RationalInterval)
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i,
      HasDerivAt (fun t => x t i) ((d i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i)) :
    ((e.intervalEval start).lower : ℝ)+((e.derivative d).intervalEval start).lower+
      (((e.derivative d).derivative d).intervalEval whole).lower/2 ≤ e.realEval (x 1) := by
  have h₁ : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun t => e.realEval (x t)) ((e.derivative d).realEval (x s)) s :=
    fun s hs => e.hasDerivAt_derivative d (hx s hs)
  have h₂ : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun t => (e.derivative d).realEval (x t))
        (((e.derivative d).derivative d).realEval (x s)) s :=
    fun s hs => (e.derivative d).hasDerivAt_derivative d (hx s hs)
  have hbound : ∀ s ∈ Icc (0:ℝ) 1,
      -(-((((e.derivative d).derivative d).intervalEval whole).lower : ℝ)) ≤
        ((e.derivative d).derivative d).realEval (x s) := by
    intro s hs
    simpa only [neg_neg] using (((e.derivative d).derivative d).intervalEval_contains (hwhole s hs)).1
  have h := segment_taylor_lower h₁ h₂ hbound
  have h0 := (e.intervalEval_contains hstart).1
  have h1 := ((e.derivative d).intervalEval_contains hstart).1
  linarith

/-- A closed rational comparison is the final numerical obligation. -/
theorem interval_taylor2_positive {n : ℕ} (e : PolynomialExpr n)
    (d : Fin n → PolynomialExpr n) (x : ℝ → Fin n → ℝ)
    (start whole : Fin n → RationalInterval) {L : ℚ}
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i,
      HasDerivAt (fun t => x t i) ((d i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i))
    (hL : L < (e.intervalEval start).lower+((e.derivative d).intervalEval start).lower+
      (((e.derivative d).derivative d).intervalEval whole).lower/2) :
    (L : ℝ) < e.realEval (x 1) := by
  have h : (L : ℝ) < ((e.intervalEval start).lower : ℝ)+
      ((e.derivative d).intervalEval start).lower+
      (((e.derivative d).derivative d).intervalEval whole).lower/2 := by exact_mod_cast hL
  exact h.trans_le (interval_taylor2_lower e d x start whole hx hstart hwhole)

end SparseLowerTail.Numerics

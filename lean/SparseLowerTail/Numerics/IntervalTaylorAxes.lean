import SparseLowerTail.Numerics.IntervalTaylor

/-! Taylor bounds that evaluate each partial derivative before combining it
with the displacement, avoiding interval dependency from repeated displacements. -/
namespace SparseLowerTail.Numerics
open Set PolynomialExpr
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- Chain rule with three scalar coordinate velocities. -/
theorem PolynomialExpr.hasDerivAt_three {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (v : Fin 3 → ℝ)
    {x : ℝ → Fin n → ℝ} {s : ℝ}
    (hx : ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s) :
    HasDerivAt (fun t => e.realEval (x t))
      (v 0*(e.derivative (d 0)).realEval (x s)+
       v 1*(e.derivative (d 1)).realEval (x s)+
       v 2*(e.derivative (d 2)).realEval (x s)) s := by
  simp only [derivative,realEval_simplify]
  induction e with
  | rational r =>
    simpa only [along,realEval,Rat.cast_zero,mul_zero,add_zero] using hasDerivAt_const s (r:ℝ)
  | var i => exact hx i
  | add a b ha hb =>
    convert ha.add hb using 1 <;> simp only [along,realEval] <;> ring
  | neg a ha =>
    convert ha.neg using 1 <;> simp only [along,realEval] <;> ring
  | mul a b ha hb =>
    convert ha.mul hb using 1 <;> simp only [along,realEval] <;> ring

def sumThree (f : Fin 3 → ℝ) : ℝ := f 0+f 1+f 2

def RationalInterval.sumThree (f : Fin 3 → RationalInterval) : RationalInterval :=
  ((f 0).add (f 1)).add (f 2)

theorem RationalInterval.sumThree_contains {I : Fin 3 → RationalInterval}
    {x : Fin 3 → ℝ} (hx : ∀ i, (I i).contains (x i)) :
    (RationalInterval.sumThree I).contains (SparseLowerTail.Numerics.sumThree x) :=
  RationalInterval.add_contains (RationalInterval.add_contains (hx 0) (hx 1)) (hx 2)

def gradientInterval {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (start : Fin n → RationalInterval)
    (velocity : Fin 3 → RationalInterval) : RationalInterval :=
  RationalInterval.sumThree (fun i => (velocity i).mul ((e.derivative (d i)).intervalEval start))

def hessianInterval {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (whole : Fin n → RationalInterval)
    (velocity : Fin 3 → RationalInterval) : RationalInterval :=
  RationalInterval.sumThree (fun i => RationalInterval.sumThree (fun j =>
    ((velocity i).mul (velocity j)).mul
      (((e.derivative (d i)).derivative (d j)).intervalEval whole)))

theorem interval_taylor_axes_lower {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → RationalInterval)
    (velocity : Fin 3 → RationalInterval)
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i)) :
    ((e.intervalEval start).lower : ℝ)+(gradientInterval e d start velocity).lower+
      (hessianInterval e d whole velocity).lower/2 ≤ e.realEval (x 1) := by
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
      -(-((hessianInterval e d whole velocity).lower : ℝ)) ≤ f₂ s := by
    intro s hs
    have H : (hessianInterval e d whole velocity).contains (f₂ s) := by
      apply RationalInterval.sumThree_contains
      intro i
      apply RationalInterval.sumThree_contains
      intro j
      exact RationalInterval.mul_contains (RationalInterval.mul_contains (hv i) (hv j))
        (((e.derivative (d i)).derivative (d j)).intervalEval_contains (hwhole s hs))
    simpa only [neg_neg] using H.1
  have H0 := (e.intervalEval_contains hstart).1
  have H1 : (gradientInterval e d start velocity).contains (f₁ 0) := by
    apply RationalInterval.sumThree_contains
    intro i
    exact RationalInterval.mul_contains (hv i) ((e.derivative (d i)).intervalEval_contains hstart)
  have H := segment_taylor_lower h₁ h₂ hb
  linarith [H1.1]

theorem interval_taylor_axes_positive {n : ℕ} (e : PolynomialExpr n)
    (d : Fin 3 → Fin n → PolynomialExpr n) (v : Fin 3 → ℝ)
    (x : ℝ → Fin n → ℝ) (start whole : Fin n → RationalInterval)
    (velocity : Fin 3 → RationalInterval) {L : ℚ}
    (hv : ∀ i, (velocity i).contains (v i))
    (hx : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, HasDerivAt (fun t => x t i)
      (v 0*(d 0 i).realEval (x s)+v 1*(d 1 i).realEval (x s)+
        v 2*(d 2 i).realEval (x s)) s)
    (hstart : ∀ i, (start i).contains (x 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (x s i))
    (hL : L < (e.intervalEval start).lower+(gradientInterval e d start velocity).lower+
      (hessianInterval e d whole velocity).lower/2) :
    (L : ℝ) < e.realEval (x 1) := by
  have h : (L : ℝ) < ((e.intervalEval start).lower : ℝ)+
      (gradientInterval e d start velocity).lower+
      (hessianInterval e d whole velocity).lower/2 := by exact_mod_cast hL
  exact h.trans_le (interval_taylor_axes_lower e d v x start whole velocity hv hx hstart hwhole)

end SparseLowerTail.Numerics

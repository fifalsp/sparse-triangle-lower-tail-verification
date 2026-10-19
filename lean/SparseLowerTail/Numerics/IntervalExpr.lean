import SparseLowerTail.Numerics.IntervalArithmetic

/-! A proof-producing rational interval evaluator for polynomial expressions.
The expression and rational computations are data. One inductive correctness
proof connects them to real arithmetic; closed checks may use `decide +kernel`,
never native evaluation or an imported external success flag. -/
namespace SparseLowerTail.Numerics

structure RationalInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

namespace RationalInterval

def contains (I : RationalInterval) (x : ℝ) : Prop := Bounds x I.lower I.upper

def point (r : ℚ) : RationalInterval := ⟨r,r⟩
def add (I J : RationalInterval) : RationalInterval := ⟨I.lower+J.lower,I.upper+J.upper⟩
def neg (I : RationalInterval) : RationalInterval := ⟨-I.upper,-I.lower⟩
def mul (I J : RationalInterval) : RationalInterval :=
  ⟨min (min (I.lower*J.lower) (I.lower*J.upper))
      (min (I.upper*J.lower) (I.upper*J.upper)),
    max (max (I.lower*J.lower) (I.lower*J.upper))
      (max (I.upper*J.lower) (I.upper*J.upper))⟩

theorem point_contains (r : ℚ) : (point r).contains (r : ℝ) := ⟨le_rfl,le_rfl⟩

theorem add_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (I.add J).contains (x+y) := by
  simpa only [contains,add,Rat.cast_add] using hx.add hy

theorem neg_contains {I : RationalInterval} {x : ℝ}
    (hx : I.contains x) : I.neg.contains (-x) := by
  simpa only [contains,neg,Rat.cast_neg] using hx.neg

theorem mul_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (I.mul J).contains (x*y) := by
  simp only [contains,mul,Rat.cast_min,Rat.cast_max,Rat.cast_mul]
  apply hx.mul_corners hy <;>
    simp only [min_le_iff,le_max_iff] <;> aesop

end RationalInterval

/-- Small expression language with only operations whose interval rules are proved. -/
inductive PolynomialExpr (n : ℕ)
  | rational : ℚ → PolynomialExpr n
  | var : Fin n → PolynomialExpr n
  | add : PolynomialExpr n → PolynomialExpr n → PolynomialExpr n
  | neg : PolynomialExpr n → PolynomialExpr n
  | mul : PolynomialExpr n → PolynomialExpr n → PolynomialExpr n
  deriving DecidableEq, Repr

namespace PolynomialExpr

instance {n : ℕ} : Add (PolynomialExpr n) := ⟨.add⟩
instance {n : ℕ} : Neg (PolynomialExpr n) := ⟨.neg⟩
instance {n : ℕ} : Sub (PolynomialExpr n) := ⟨fun e f => .add e (.neg f)⟩
instance {n : ℕ} : Mul (PolynomialExpr n) := ⟨.mul⟩
instance {n : ℕ} (k : ℕ) : OfNat (PolynomialExpr n) k := ⟨.rational k⟩
def natPow {n : ℕ} (e : PolynomialExpr n) : ℕ → PolynomialExpr n
  | 0 => .rational 1
  | k+1 => .mul (natPow e k) e
instance {n : ℕ} : Pow (PolynomialExpr n) ℕ := ⟨natPow⟩

def realEval {n : ℕ} : PolynomialExpr n → (Fin n → ℝ) → ℝ
  | .rational r, _ => r
  | .var i, x => x i
  | .add e f, x => e.realEval x+f.realEval x
  | .neg e, x => -e.realEval x
  | .mul e f, x => e.realEval x*f.realEval x

@[simp] theorem realEval_rational {n : ℕ} (r : ℚ) (x : Fin n → ℝ) :
    (rational r : PolynomialExpr n).realEval x = (r : ℝ) := rfl
@[simp] theorem realEval_var {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    (var i : PolynomialExpr n).realEval x = x i := rfl

@[simp] theorem realEval_add {n : ℕ} (e f : PolynomialExpr n) (x : Fin n → ℝ) :
    (e+f).realEval x = e.realEval x+f.realEval x := rfl
@[simp] theorem realEval_neg {n : ℕ} (e : PolynomialExpr n) (x : Fin n → ℝ) :
    (-e).realEval x = -e.realEval x := rfl
@[simp] theorem realEval_sub {n : ℕ} (e f : PolynomialExpr n) (x : Fin n → ℝ) :
    (e-f).realEval x = e.realEval x-f.realEval x := by rfl
@[simp] theorem realEval_mul {n : ℕ} (e f : PolynomialExpr n) (x : Fin n → ℝ) :
    (e*f).realEval x = e.realEval x*f.realEval x := rfl
@[simp] theorem realEval_ofNat {n : ℕ} (k : ℕ) (x : Fin n → ℝ) :
    (OfNat.ofNat k : PolynomialExpr n).realEval x = k := by
  change ((k : ℚ) : ℝ) = k
  exact_mod_cast rfl
@[simp] theorem realEval_zero {n : ℕ} (x : Fin n → ℝ) :
    (0 : PolynomialExpr n).realEval x = 0 := by
  change ((0 : ℚ) : ℝ) = 0
  norm_num
@[simp] theorem realEval_one {n : ℕ} (x : Fin n → ℝ) :
    (1 : PolynomialExpr n).realEval x = 1 := by
  change ((1 : ℚ) : ℝ) = 1
  norm_num
@[simp] theorem realEval_two {n : ℕ} (x : Fin n → ℝ) :
    (2 : PolynomialExpr n).realEval x = 2 := by
  change ((2 : ℚ) : ℝ) = 2
  norm_num

@[simp] theorem realEval_pow {n : ℕ} (e : PolynomialExpr n) (k : ℕ) (x : Fin n → ℝ) :
    (e^k).realEval x = e.realEval x^k := by
  induction k with
  | zero => change ((1 : ℚ) : ℝ) = _; simp
  | succ k hk => change (e^k).realEval x*e.realEval x = _
                 rw [hk,pow_succ]

def intervalEval {n : ℕ} : PolynomialExpr n → (Fin n → RationalInterval) → RationalInterval
  | .rational r, _ => .point r
  | .var i, box => box i
  | .add e f, box => (e.intervalEval box).add (f.intervalEval box)
  | .neg e, box => (e.intervalEval box).neg
  | .mul e f, box => (e.intervalEval box).mul (f.intervalEval box)

/-- The only analytic trust bridge: a single structural induction, checked once. -/
theorem intervalEval_contains {n : ℕ} (e : PolynomialExpr n)
    {x : Fin n → ℝ} {box : Fin n → RationalInterval}
    (hx : ∀ i, (box i).contains (x i)) :
    (e.intervalEval box).contains (e.realEval x) := by
  induction e with
  | rational r => exact RationalInterval.point_contains r
  | var i => exact hx i
  | add e f he hf => exact RationalInterval.add_contains he hf
  | neg e he => exact RationalInterval.neg_contains he
  | mul e f he hf => exact RationalInterval.mul_contains he hf

/-- A rational lower-bound comparison proves a real lower bound for every point. -/
theorem le_realEval {n : ℕ} (e : PolynomialExpr n)
    {x : Fin n → ℝ} {box : Fin n → RationalInterval} {L : ℚ}
    (hx : ∀ i, (box i).contains (x i)) (hL : L ≤ (e.intervalEval box).lower) :
    (L : ℝ) ≤ e.realEval x := by
  have h : (L : ℝ) ≤ ((e.intervalEval box).lower : ℝ) := by exact_mod_cast hL
  exact h.trans (e.intervalEval_contains hx).1

theorem lt_realEval {n : ℕ} (e : PolynomialExpr n)
    {x : Fin n → ℝ} {box : Fin n → RationalInterval} {L : ℚ}
    (hx : ∀ i, (box i).contains (x i)) (hL : L < (e.intervalEval box).lower) :
    (L : ℝ) < e.realEval x := by
  have h : (L : ℝ) < ((e.intervalEval box).lower : ℝ) := by exact_mod_cast hL
  exact h.trans_le (e.intervalEval_contains hx).1

/-- Symbolic chain rule, with derivatives supplied for the primitive variables. -/
def along {n : ℕ} (d : Fin n → PolynomialExpr n) : PolynomialExpr n → PolynomialExpr n
  | .rational _ => .rational 0
  | .var i => d i
  | .add e f => .add (along d e) (along d f)
  | .neg e => .neg (along d e)
  | .mul e f => .add (.mul (along d e) f) (.mul e (along d f))

theorem hasDerivAt_realEval {n : ℕ} (e : PolynomialExpr n)
    (d : Fin n → PolynomialExpr n) {x : ℝ → Fin n → ℝ} {s : ℝ}
    (hx : ∀ i, HasDerivAt (fun t => x t i) ((d i).realEval (x s)) s) :
    HasDerivAt (fun t => e.realEval (x t)) ((e.along d).realEval (x s)) s := by
  induction e with
  | rational r => simpa only [along, realEval, Rat.cast_zero] using hasDerivAt_const s (r : ℝ)
  | var i => exact hx i
  | add e f he hf => exact he.add hf
  | neg e he => exact he.neg
  | mul e f he hf => exact he.mul hf

end PolynomialExpr
end SparseLowerTail.Numerics

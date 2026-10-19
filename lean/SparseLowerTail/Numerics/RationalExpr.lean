import SparseLowerTail.Numerics.DyadicReciprocal

/-! A fail-closed checked interval evaluator for rational expressions. Division
is permitted only when the computed denominator interval excludes zero. -/
namespace SparseLowerTail.Numerics

inductive RationalExpr (n : ℕ) where
  | rational (q : ℚ)
  | var (i : Fin n)
  | add (e f : RationalExpr n)
  | neg (e : RationalExpr n)
  | mul (e f : RationalExpr n)
  | inv (e : RationalExpr n)
  deriving Repr

namespace RationalExpr
instance {n : ℕ} : Add (RationalExpr n) := ⟨.add⟩
instance {n : ℕ} : Neg (RationalExpr n) := ⟨.neg⟩
instance {n : ℕ} : Sub (RationalExpr n) := ⟨fun e f => .add e (.neg f)⟩
instance {n : ℕ} : Mul (RationalExpr n) := ⟨.mul⟩
instance {n : ℕ} (k : ℕ) : OfNat (RationalExpr n) k := ⟨.rational k⟩
def natPow {n : ℕ} (e : RationalExpr n) : ℕ → RationalExpr n
  | 0 => .rational 1
  | k+1 => .mul (natPow e k) e
instance {n : ℕ} : Pow (RationalExpr n) ℕ := ⟨natPow⟩

instance {n : ℕ} : Inv (RationalExpr n) := ⟨.inv⟩
instance {n : ℕ} : Div (RationalExpr n) := ⟨fun e f => .mul e (.inv f)⟩
noncomputable def realEval {n : ℕ} : RationalExpr n→(Fin n→ℝ)→ℝ
  | .rational q,_ => q
  | .var i,x => x i
  | .add e f,x => e.realEval x+f.realEval x
  | .neg e,x => -e.realEval x
  | .mul e f,x => e.realEval x*f.realEval x
  | .inv e,x => (e.realEval x)⁻¹

@[simp] theorem realEval_rational {n : ℕ} (r : ℚ) (x : Fin n → ℝ) :
    (rational r : RationalExpr n).realEval x = (r : ℝ) := rfl
@[simp] theorem realEval_var {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    (var i : RationalExpr n).realEval x = x i := rfl

@[simp] theorem realEval_add {n : ℕ} (e f : RationalExpr n) (x : Fin n → ℝ) :
    (e+f).realEval x = e.realEval x+f.realEval x := rfl
@[simp] theorem realEval_neg {n : ℕ} (e : RationalExpr n) (x : Fin n → ℝ) :
    (-e).realEval x = -e.realEval x := rfl
@[simp] theorem realEval_sub {n : ℕ} (e f : RationalExpr n) (x : Fin n → ℝ) :
    (e-f).realEval x = e.realEval x-f.realEval x := by rfl
@[simp] theorem realEval_mul {n : ℕ} (e f : RationalExpr n) (x : Fin n → ℝ) :
    (e*f).realEval x = e.realEval x*f.realEval x := rfl
@[simp] theorem realEval_ofNat {n : ℕ} (k : ℕ) (x : Fin n → ℝ) :
    (OfNat.ofNat k : RationalExpr n).realEval x = k := by
  change ((k : ℚ) : ℝ) = k
  exact_mod_cast rfl
@[simp] theorem realEval_zero {n : ℕ} (x : Fin n → ℝ) :
    (0 : RationalExpr n).realEval x = 0 := by
  change ((0 : ℚ) : ℝ) = 0
  norm_num
@[simp] theorem realEval_one {n : ℕ} (x : Fin n → ℝ) :
    (1 : RationalExpr n).realEval x = 1 := by
  change ((1 : ℚ) : ℝ) = 1
  norm_num
@[simp] theorem realEval_two {n : ℕ} (x : Fin n → ℝ) :
    (2 : RationalExpr n).realEval x = 2 := by
  change ((2 : ℚ) : ℝ) = 2
  norm_num

@[simp] theorem realEval_pow {n : ℕ} (e : RationalExpr n) (k : ℕ) (x : Fin n → ℝ) :
    (e^k).realEval x = e.realEval x^k := by
  induction k with
  | zero => change ((1 : ℚ) : ℝ) = _; simp
  | succ k hk => change (e^k).realEval x*e.realEval x = _
                 rw [hk,pow_succ]

@[simp] theorem realEval_inv {n : ℕ} (e : RationalExpr n) (x : Fin n→ℝ) :
    (e⁻¹).realEval x=(e.realEval x)⁻¹ := rfl
@[simp] theorem realEval_div {n : ℕ} (e f : RationalExpr n) (x : Fin n→ℝ) :
    (e/f).realEval x=e.realEval x/f.realEval x := by simp only [div_eq_mul_inv]; rfl

def dyadicEval {n : ℕ} : RationalExpr n→(Fin n→DyadicInterval)→Option DyadicInterval
  | .rational q,_ => some (.point q)
  | .var i,box => some (box i)
  | .add e f,box => do return (←e.dyadicEval box).add (←f.dyadicEval box)
  | .neg e,box => do return (←e.dyadicEval box).neg
  | .mul e f,box => do return (←e.dyadicEval box).mul (←f.dyadicEval box)
  | .inv e,box => do (←e.dyadicEval box).inv?

theorem dyadicEval_contains {n : ℕ} (e : RationalExpr n)
    {x : Fin n→ℝ} {box : Fin n→DyadicInterval} {I : DyadicInterval}
    (hx : ∀ i,(box i).contains (x i)) (he : e.dyadicEval box=some I) :
    I.contains (e.realEval x) := by
  induction e generalizing I with
  | rational q =>
    cases he
    exact DyadicInterval.point_contains q
  | var i =>
    cases he
    exact hx i
  | add e f ihE ihF =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E =>
      cases hF : f.dyadicEval box with
      | none => simp [dyadicEval,hE,hF] at he
      | some F =>
        have hI : E.add F=I := by simpa [dyadicEval,hE,hF] using he
        rw [←hI]
        exact DyadicInterval.add_contains (ihE hE) (ihF hF)
  | neg e ih =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E =>
      have hI : E.neg=I := by simpa [dyadicEval,hE] using he
      rw [←hI]
      exact DyadicInterval.neg_contains (ih hE)
  | mul e f ihE ihF =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E =>
      cases hF : f.dyadicEval box with
      | none => simp [dyadicEval,hE,hF] at he
      | some F =>
        have hI : E.mul F=I := by simpa [dyadicEval,hE,hF] using he
        rw [←hI]
        exact DyadicInterval.mul_contains (ihE hE) (ihF hF)
  | inv e ih =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E =>
      exact DyadicInterval.inv?_contains (ih hE) (by simpa [dyadicEval,hE] using he)

end RationalExpr
end SparseLowerTail.Numerics

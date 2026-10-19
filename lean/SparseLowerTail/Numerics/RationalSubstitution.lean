import SparseLowerTail.Numerics.RationalExpr

/-! Exact expression substitution for reusing the certificate and its
polynomial derivatives in rational coefficient solves. -/
namespace SparseLowerTail.Numerics
namespace RationalExpr

def subst {n m : ℕ} (σ : Fin n → RationalExpr m) : RationalExpr n → RationalExpr m
  | .rational q => .rational q
  | .var i => σ i
  | .add e f => .add (e.subst σ) (f.subst σ)
  | .neg e => .neg (e.subst σ)
  | .mul e f => .mul (e.subst σ) (f.subst σ)
  | .inv e => .inv (e.subst σ)

@[simp] theorem subst_realEval {n m : ℕ} (e : RationalExpr n)
    (σ : Fin n → RationalExpr m) (x : Fin m → ℝ) :
    (e.subst σ).realEval x=e.realEval (fun i => (σ i).realEval x) := by
  induction e with
  | rational q => rfl
  | var i => rfl
  | add e f he hf => simp only [subst,realEval,he,hf]
  | neg e he => simp only [subst,realEval,he]
  | mul e f he hf => simp only [subst,realEval,he,hf]
  | inv e he => simp only [subst,realEval,he]

end RationalExpr
namespace PolynomialExpr

/-- Substitute polynomial parameters before converting to rational expressions.
This permits verified zero folding of fixed coefficient slots. -/
def subst {n m : ℕ} (σ : Fin n → PolynomialExpr m) : PolynomialExpr n → PolynomialExpr m
  | .rational q => .rational q
  | .var i => σ i
  | .add e f => .add (e.subst σ) (f.subst σ)
  | .neg e => .neg (e.subst σ)
  | .mul e f => .mul (e.subst σ) (f.subst σ)

@[simp] theorem subst_realEval {n m : ℕ} (e : PolynomialExpr n)
    (σ : Fin n → PolynomialExpr m) (x : Fin m → ℝ) :
    (e.subst σ).realEval x=e.realEval (fun i => (σ i).realEval x) := by
  induction e with
  | rational q => rfl
  | var i => rfl
  | add e f he hf => simp only [subst,realEval,he,hf]
  | neg e he => simp only [subst,realEval,he]
  | mul e f he hf => simp only [subst,realEval,he,hf]

def toRational {n : ℕ} : PolynomialExpr n → RationalExpr n
  | .rational q => .rational q
  | .var i => .var i
  | .add e f => .add e.toRational f.toRational
  | .neg e => .neg e.toRational
  | .mul e f => .mul e.toRational f.toRational

@[simp] theorem toRational_realEval {n : ℕ} (e : PolynomialExpr n) (x : Fin n → ℝ) :
    e.toRational.realEval x=e.realEval x := by
  induction e with
  | rational q => rfl
  | var i => rfl
  | add e f he hf => simp only [toRational,realEval,RationalExpr.realEval,he,hf]
  | neg e he => simp only [toRational,realEval,RationalExpr.realEval,he]
  | mul e f he hf => simp only [toRational,realEval,RationalExpr.realEval,he,hf]

def rationalSubst {n m : ℕ} (e : PolynomialExpr n) (σ : Fin n → RationalExpr m) :
    RationalExpr m := e.toRational.subst σ

@[simp] theorem rationalSubst_realEval {n m : ℕ} (e : PolynomialExpr n)
    (σ : Fin n → RationalExpr m) (x : Fin m → ℝ) :
    (e.rationalSubst σ).realEval x=e.realEval (fun i => (σ i).realEval x) := by
  simp only [rationalSubst,RationalExpr.subst_realEval,toRational_realEval]

end PolynomialExpr
end SparseLowerTail.Numerics

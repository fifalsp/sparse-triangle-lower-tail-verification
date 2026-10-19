import SparseLowerTail.Numerics.IntervalExpr

/-! Verified constant folding and symbolic differentiation. They reduce the
expression size before kernel evaluation without changing the real function. -/
namespace SparseLowerTail.Numerics.PolynomialExpr

def rename {n m : ℕ} (f : Fin n → Fin m) : PolynomialExpr n → PolynomialExpr m
  | .rational r => .rational r
  | .var i => .var (f i)
  | .add a b => .add (rename f a) (rename f b)
  | .neg a => .neg (rename f a)
  | .mul a b => .mul (rename f a) (rename f b)

@[simp] theorem realEval_rename {n m : ℕ} (e : PolynomialExpr n)
    (f : Fin n → Fin m) (x : Fin m → ℝ) :
    (e.rename f).realEval x = e.realEval (fun i => x (f i)) := by
  induction e with
  | rational r => rfl
  | var i => rfl
  | add a b ha hb => simp only [rename,realEval,ha,hb]
  | neg a ha => simp only [rename,realEval,ha]
  | mul a b ha hb => simp only [rename,realEval,ha,hb]

def smartAdd {n : ℕ} : PolynomialExpr n → PolynomialExpr n → PolynomialExpr n
  | .rational r,.rational s => .rational (r+s)
  | .rational r,b => if r=0 then b else .add (.rational r) b
  | a,.rational s => if s=0 then a else .add a (.rational s)
  | a,b => .add a b

def smartNeg {n : ℕ} : PolynomialExpr n → PolynomialExpr n
  | .rational r => .rational (-r)
  | .neg a => a
  | a => .neg a

def smartMul {n : ℕ} : PolynomialExpr n → PolynomialExpr n → PolynomialExpr n
  | .rational r,.rational s => .rational (r*s)
  | .rational r,b => if r=0 then .rational 0 else if r=1 then b else .mul (.rational r) b
  | a,.rational s => if s=0 then .rational 0 else if s=1 then a else .mul a (.rational s)
  | a,b => .mul a b

@[simp] theorem realEval_smartAdd {n : ℕ} (a b : PolynomialExpr n) (x : Fin n → ℝ) :
    (smartAdd a b).realEval x = a.realEval x+b.realEval x := by
  cases a <;> cases b <;> simp [smartAdd,realEval] <;> split_ifs <;> simp_all [realEval]

@[simp] theorem realEval_smartNeg {n : ℕ} (a : PolynomialExpr n) (x : Fin n → ℝ) :
    (smartNeg a).realEval x = -a.realEval x := by
  cases a <;> simp [smartNeg,realEval]

@[simp] theorem realEval_smartMul {n : ℕ} (a b : PolynomialExpr n) (x : Fin n → ℝ) :
    (smartMul a b).realEval x = a.realEval x*b.realEval x := by
  cases a <;> cases b <;> simp [smartMul,realEval] <;> split_ifs <;> simp_all [realEval]

def simplify {n : ℕ} : PolynomialExpr n → PolynomialExpr n
  | .rational r => .rational r
  | .var i => .var i
  | .add a b => smartAdd (simplify a) (simplify b)
  | .neg a => smartNeg (simplify a)
  | .mul a b => smartMul (simplify a) (simplify b)

@[simp] theorem realEval_simplify {n : ℕ} (e : PolynomialExpr n) (x : Fin n → ℝ) :
    e.simplify.realEval x = e.realEval x := by
  induction e with
  | rational r => rfl
  | var i => rfl
  | add a b ha hb => simp only [simplify,realEval_smartAdd,realEval,ha,hb]
  | neg a ha => simp only [simplify,realEval_smartNeg,realEval,ha]
  | mul a b ha hb => simp only [simplify,realEval_smartMul,realEval,ha,hb]

def derivative {n : ℕ} (d : Fin n → PolynomialExpr n) (e : PolynomialExpr n) :
    PolynomialExpr n := (e.along d).simplify

theorem hasDerivAt_derivative {n : ℕ} (e : PolynomialExpr n)
    (d : Fin n → PolynomialExpr n) {x : ℝ → Fin n → ℝ} {s : ℝ}
    (hx : ∀ i, HasDerivAt (fun t => x t i) ((d i).realEval (x s)) s) :
    HasDerivAt (fun t => e.realEval (x t)) ((derivative d e).realEval (x s)) s := by
  simpa only [derivative,realEval_simplify] using e.hasDerivAt_realEval d hx

end SparseLowerTail.Numerics.PolynomialExpr

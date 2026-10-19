import SparseLowerTail.Numerics.DyadicInterval

/-! Rational constants are converted to outward dyadic intervals once. Their
literal enclosures are checked separately, then reused by each leaf evaluator. -/
namespace SparseLowerTail.Numerics

inductive CachedPolynomialExpr (n : ℕ) where
  | rational (q : ℚ) (interval : DyadicInterval)
  | var (i : Fin n)
  | add (e f : CachedPolynomialExpr n)
  | neg (e : CachedPolynomialExpr n)
  | mul (e f : CachedPolynomialExpr n)
  deriving Repr

namespace CachedPolynomialExpr

def erase {n : ℕ} : CachedPolynomialExpr n→PolynomialExpr n
  | .rational q _ => .rational q
  | .var i => .var i
  | .add e f => .add e.erase f.erase
  | .neg e => .neg e.erase
  | .mul e f => .mul e.erase f.erase

def Valid {n : ℕ} : CachedPolynomialExpr n→Prop
  | .rational q I => I=DyadicInterval.point q
  | .var _ => True
  | .add e f => e.Valid ∧ f.Valid
  | .neg e => e.Valid
  | .mul e f => e.Valid ∧ f.Valid

instance validDecidable {n : ℕ} : (e : CachedPolynomialExpr n)→Decidable e.Valid
  | .rational q I => inferInstanceAs (Decidable (I=DyadicInterval.point q))
  | .var _ => isTrue True.intro
  | .add e f => @instDecidableAnd _ _ (validDecidable e) (validDecidable f)
  | .neg e => validDecidable e
  | .mul e f => @instDecidableAnd _ _ (validDecidable e) (validDecidable f)

def eval {n : ℕ} : CachedPolynomialExpr n→(Fin n→DyadicInterval)→DyadicInterval
  | .rational _ I,_ => I
  | .var i,box => box i
  | .add e f,box => (e.eval box).add (f.eval box)
  | .neg e,box => (e.eval box).neg
  | .mul e f,box => (e.eval box).mul (f.eval box)

/-- The fast evaluator is extensionally the checked polynomial evaluator.
This is a symbolic induction; the cached constants are not recalculated here. -/
theorem eval_eq {n : ℕ} (e : CachedPolynomialExpr n) (h : e.Valid)
    (box : Fin n→DyadicInterval) : e.eval box=e.erase.dyadicEval box := by
  induction e with
  | rational q I => exact h
  | var i => rfl
  | add e f he hf => exact congrArg₂ DyadicInterval.add (he h.1) (hf h.2)
  | neg e he => exact congrArg DyadicInterval.neg (he h)
  | mul e f he hf => exact congrArg₂ DyadicInterval.mul (he h.1) (hf h.2)

theorem eval_contains {n : ℕ} (e : CachedPolynomialExpr n) (h : e.Valid)
    {box : Fin n→DyadicInterval} {x : Fin n→ℝ}
    (hx : ∀ i,(box i).contains (x i)) : (e.eval box).contains (e.erase.realEval x) := by
  rw [e.eval_eq h]
  exact e.erase.dyadicEval_contains hx

end CachedPolynomialExpr
end SparseLowerTail.Numerics

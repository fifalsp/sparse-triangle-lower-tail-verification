import SparseLowerTail.Numerics.RationalExpr
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Symbolic chain rules for rational certificate coefficients. Successful
interval evaluation certifies every denominator needed by the chain rule;
division at zero is never silently treated as differentiable. -/
namespace SparseLowerTail.Numerics.RationalExpr

def along {n : ℕ} (d : Fin n → RationalExpr n) : RationalExpr n → RationalExpr n
  | .rational _ => .rational 0
  | .var i => d i
  | .add e f => .add (along d e) (along d f)
  | .neg e => .neg (along d e)
  | .mul e f => .add (.mul (along d e) f) (.mul e (along d f))
  | .inv e => .neg (.mul (along d e) (.mul (.inv e) (.inv e)))

/-- Every denominator in the expression is nonzero at this input. -/
def Domain {n : ℕ} : RationalExpr n → (Fin n → ℝ) → Prop
  | .rational _,_ => True
  | .var _,_ => True
  | .add e f,x => e.Domain x ∧ f.Domain x
  | .neg e,x => e.Domain x
  | .mul e f,x => e.Domain x ∧ f.Domain x
  | .inv e,x => e.Domain x ∧ e.realEval x≠0

theorem hasDerivAt_realEval {n : ℕ} (e : RationalExpr n)
    (d : Fin n → RationalExpr n) {x : ℝ → Fin n → ℝ} {s : ℝ}
    (hx : ∀i,HasDerivAt (fun t => x t i) ((d i).realEval (x s)) s)
    (he : e.Domain (x s)) :
    HasDerivAt (fun t => e.realEval (x t)) ((e.along d).realEval (x s)) s := by
  induction e with
  | rational r => simpa only [along,realEval,Rat.cast_zero] using hasDerivAt_const s (r : ℝ)
  | var i => exact hx i
  | add e f ihE ihF => exact (ihE he.1).add (ihF he.2)
  | neg e ih => exact (ih he).neg
  | mul e f ihE ihF => exact (ihE he.1).mul (ihF he.2)
  | inv e ih =>
    convert (ih he.1).inv he.2 using 1
    simp only [along,realEval,div_eq_mul_inv,pow_two]
    ring

private theorem ne_zero_of_inv_checked {I J : DyadicInterval} {x : ℝ}
    (hx : I.contains x) (hJ : I.inv?=some J) : x≠0 := by
  unfold DyadicInterval.inv? at hJ
  split_ifs at hJ with hp hn
  · exact (DyadicInterval.pos_of_lower_pos hx hp).ne'
  · have h := DyadicInterval.pos_of_lower_pos (DyadicInterval.neg_contains hx)
      (show 0<I.neg.lower by simpa [DyadicInterval.neg] using neg_pos.mpr hn)
    linarith

/-- The existing fail-closed evaluator also supplies the analytic domain
obligation, throughout the entire input box. -/
theorem domain_of_dyadicEval {n : ℕ} (e : RationalExpr n)
    {x : Fin n → ℝ} {box : Fin n → DyadicInterval} {I : DyadicInterval}
    (hx : ∀i,(box i).contains (x i)) (he : e.dyadicEval box=some I) : e.Domain x := by
  induction e generalizing I with
  | rational _ => trivial
  | var _ => trivial
  | add e f ihE ihF =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E =>
      cases hF : f.dyadicEval box with
      | none => simp [dyadicEval,hE,hF] at he
      | some F => exact ⟨ihE hE,ihF hF⟩
  | neg e ih =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E => exact ih hE
  | mul e f ihE ihF =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E =>
      cases hF : f.dyadicEval box with
      | none => simp [dyadicEval,hE,hF] at he
      | some F => exact ⟨ihE hE,ihF hF⟩
  | inv e ih =>
    cases hE : e.dyadicEval box with
    | none => simp [dyadicEval,hE] at he
    | some E =>
      exact ⟨ih hE,ne_zero_of_inv_checked (e.dyadicEval_contains hx hE)
        (by simpa [dyadicEval,hE] using he)⟩

theorem hasDerivAt_of_dyadicEval {n : ℕ} (e : RationalExpr n)
    (d : Fin n → RationalExpr n) {x : ℝ → Fin n → ℝ} {s : ℝ}
    (hx : ∀i,HasDerivAt (fun t => x t i) ((d i).realEval (x s)) s)
    {box : Fin n → DyadicInterval} {I : DyadicInterval}
    (hbox : ∀i,(box i).contains (x s i)) (he : e.dyadicEval box=some I) :
    HasDerivAt (fun t => e.realEval (x t)) ((e.along d).realEval (x s)) s :=
  e.hasDerivAt_realEval d hx (e.domain_of_dyadicEval hbox he)

end SparseLowerTail.Numerics.RationalExpr

import SparseLowerTail.Numerics.DyadicInterval

/-! A shared-register expression evaluator. Each common subexpression can be
computed once. A binary register tree avoids linear list lookups. The analytic
correctness theorem relates the numeric program to its symbolic expression run;
register aliasing cannot introduce an unsound result, because both runs use the
same register semantics and every output identity is checked separately. -/
namespace SparseLowerTail.Numerics

inductive RegisterTree (α : Type)
  | leaf : α → RegisterTree α
  | branch : RegisterTree α → RegisterTree α → RegisterTree α
  deriving Repr

namespace RegisterTree

def get {α : Type} : RegisterTree α → ℕ → α
  | .leaf a, _ => a
  | .branch l r, i => if i%2=0 then l.get (i/2) else r.get (i/2)

def set {α : Type} : RegisterTree α → ℕ → α → RegisterTree α
  | .leaf _, _, a => .leaf a
  | .branch l r, i, a => if i%2=0 then .branch (l.set (i/2) a) r
    else .branch l (r.set (i/2) a)

def uniform {α : Type} : ℕ → α → RegisterTree α
  | 0, a => .leaf a
  | n+1, a => .branch (uniform n a) (uniform n a)

inductive Rel {α β : Type} (R : α → β → Prop) : RegisterTree α → RegisterTree β → Prop
  | leaf {a b} : R a b → Rel R (.leaf a) (.leaf b)
  | branch {l₁ r₁ l₂ r₂} : Rel R l₁ l₂ → Rel R r₁ r₂ → Rel R (.branch l₁ r₁) (.branch l₂ r₂)

theorem Rel.get {α β : Type} {R : α → β → Prop} {a : RegisterTree α} {b : RegisterTree β}
    (h : Rel R a b) (i : ℕ) : R (a.get i) (b.get i) := by
  induction h generalizing i with
  | leaf h => exact h
  | branch hl hr ihl ihr =>
    simp only [RegisterTree.get]
    split_ifs
    · exact ihl _
    · exact ihr _

theorem Rel.set {α β : Type} {R : α → β → Prop} {a : RegisterTree α} {b : RegisterTree β}
    (h : Rel R a b) (i : ℕ) {x : α} {y : β} (hxy : R x y) :
    Rel R (a.set i x) (b.set i y) := by
  induction h generalizing i with
  | leaf h => exact .leaf hxy
  | branch hl hr ihl ihr =>
    simp only [RegisterTree.set]
    split_ifs
    · exact .branch (ihl _) hr
    · exact .branch hl (ihr _)

theorem Rel.uniform {α β : Type} {R : α → β → Prop} {a : α} {b : β}
    (h : R a b) (depth : ℕ) : Rel R (RegisterTree.uniform depth a) (RegisterTree.uniform depth b) := by
  induction depth with
  | zero => exact .leaf h
  | succ depth ih => exact .branch ih ih

end RegisterTree

inductive IntervalInstruction (n : ℕ)
  | rational : ℚ → IntervalInstruction n
  | var : Fin n → IntervalInstruction n
  | add : ℕ → ℕ → IntervalInstruction n
  | neg : ℕ → IntervalInstruction n
  | mul : ℕ → ℕ → IntervalInstruction n
  deriving DecidableEq, Repr

namespace IntervalInstruction

def symbolic {n : ℕ} : IntervalInstruction n → RegisterTree (PolynomialExpr n) → PolynomialExpr n
  | .rational r, _ => .rational r
  | .var i, _ => .var i
  | .add i j, st => .add (st.get i) (st.get j)
  | .neg i, st => .neg (st.get i)
  | .mul i j, st => .mul (st.get i) (st.get j)

def dyadic {n : ℕ} (box : Fin n → DyadicInterval) : IntervalInstruction n → RegisterTree DyadicInterval → DyadicInterval
  | .rational r, _ => .point r
  | .var i, _ => box i
  | .add i j, st => (st.get i).add (st.get j)
  | .neg i, st => (st.get i).neg
  | .mul i j, st => (st.get i).mul (st.get j)

theorem dyadic_contains {n : ℕ} (cmd : IntervalInstruction n)
    {x : Fin n → ℝ} {box : Fin n → DyadicInterval}
    (hx : ∀ i, (box i).contains (x i))
    {a : RegisterTree (PolynomialExpr n)} {b : RegisterTree DyadicInterval}
    (hst : RegisterTree.Rel (fun e I => I.contains (e.realEval x)) a b) :
    (cmd.dyadic box b).contains ((cmd.symbolic a).realEval x) := by
  cases cmd with
  | rational r => exact DyadicInterval.point_contains r
  | var i => exact hx i
  | add i j => exact DyadicInterval.add_contains (hst.get i) (hst.get j)
  | neg i => exact DyadicInterval.neg_contains (hst.get i)
  | mul i j => exact DyadicInterval.mul_contains (hst.get i) (hst.get j)

theorem dyadic_eq {n : ℕ} (cmd : IntervalInstruction n)
    (box : Fin n → DyadicInterval)
    {a : RegisterTree (PolynomialExpr n)} {b : RegisterTree DyadicInterval}
    (hst : RegisterTree.Rel (fun e I => I = e.dyadicEval box) a b) :
    cmd.dyadic box b = (cmd.symbolic a).dyadicEval box := by
  cases cmd with
  | rational r => rfl
  | var i => rfl
  | add i j => exact congrArg₂ DyadicInterval.add (hst.get i) (hst.get j)
  | neg i => exact congrArg DyadicInterval.neg (hst.get i)
  | mul i j => exact congrArg₂ DyadicInterval.mul (hst.get i) (hst.get j)

end IntervalInstruction

namespace IntervalProgram

def run {n : ℕ} {α : Type} (sem : IntervalInstruction n → RegisterTree α → α) :
    List (IntervalInstruction n) → ℕ → RegisterTree α → RegisterTree α
  | [], _, st => st
  | cmd::rest, index, st => run sem rest (index+1) (st.set index (sem cmd st))

theorem run_rel {n : ℕ} {α β : Type} {R : α → β → Prop}
    (sa : IntervalInstruction n → RegisterTree α → α)
    (sb : IntervalInstruction n → RegisterTree β → β)
    (hs : ∀ cmd a b, RegisterTree.Rel R a b → R (sa cmd a) (sb cmd b))
    (code : List (IntervalInstruction n)) (index : ℕ)
    {a : RegisterTree α} {b : RegisterTree β} (hab : RegisterTree.Rel R a b) :
    RegisterTree.Rel R (run sa code index a) (run sb code index b) := by
  induction code generalizing index a b with
  | nil => exact hab
  | cons cmd rest ih => exact ih _ (hab.set index (hs cmd _ _ hab))

def symbolic {n : ℕ} (code : List (IntervalInstruction n)) (depth : ℕ) : RegisterTree (PolynomialExpr n) :=
  run IntervalInstruction.symbolic code 0 (RegisterTree.uniform depth (.rational 0))

def dyadic {n : ℕ} (code : List (IntervalInstruction n)) (depth : ℕ)
    (box : Fin n → DyadicInterval) : RegisterTree DyadicInterval :=
  run (IntervalInstruction.dyadic box) code 0 (RegisterTree.uniform depth (.point 0))

theorem dyadic_contains {n : ℕ} (code : List (IntervalInstruction n)) (depth output : ℕ)
    {x : Fin n → ℝ} {box : Fin n → DyadicInterval}
    (hx : ∀ i, (box i).contains (x i)) :
    ((dyadic code depth box).get output).contains (((symbolic code depth).get output).realEval x) := by
  have H : RegisterTree.Rel (fun e I => I.contains (e.realEval x))
      (symbolic code depth) (dyadic code depth box) := by
    apply run_rel IntervalInstruction.symbolic (IntervalInstruction.dyadic box)
    · intro cmd a b h
      exact cmd.dyadic_contains hx h
    · exact RegisterTree.Rel.uniform (R := fun e I => I.contains (e.realEval x))
        (a := PolynomialExpr.rational 0) (b := DyadicInterval.point 0)
        (DyadicInterval.point_contains 0) depth
  exact H.get output

/-- The shared-register run gives exactly the same outward interval as the
expanded expression run, allowing existing Taylor bounds to be reused. -/
theorem dyadic_eq {n : ℕ} (code : List (IntervalInstruction n)) (depth output : ℕ)
    (box : Fin n → DyadicInterval) :
    (dyadic code depth box).get output = ((symbolic code depth).get output).dyadicEval box := by
  have H : RegisterTree.Rel (fun e I => I = e.dyadicEval box)
      (symbolic code depth) (dyadic code depth box) := by
    apply run_rel IntervalInstruction.symbolic (IntervalInstruction.dyadic box)
    · intro cmd a b h
      exact cmd.dyadic_eq box h
    · exact RegisterTree.Rel.uniform (R := fun e I => I = e.dyadicEval box)
        (a := PolynomialExpr.rational 0) (b := DyadicInterval.point 0) rfl depth
  exact H.get output

end IntervalProgram
end SparseLowerTail.Numerics

import SparseLowerTail.Numerics.IntervalArithmetic

/-! Exact midpoint subdivision in arbitrary finite dimension. In particular,
the family Hessian needs four coordinates: the parameter and three offsets.
The checker reconstructs every split and rejects missing table entries. -/
noncomputable section
namespace SparseLowerTail.Numerics

structure ReplayBox (n : ℕ) where
  lower : Fin n → ℚ
  upper : Fin n → ℚ

namespace ReplayBox

def Contains {n : ℕ} (B : ReplayBox n) (x : Fin n → ℝ) : Prop :=
  ∀i,Bounds (x i) (B.lower i : ℝ) (B.upper i : ℝ)

def SameEndpoints {n : ℕ} (B C : ReplayBox n) : Prop :=
  ∀i,B.lower i=C.lower i ∧ B.upper i=C.upper i

instance {n : ℕ} (B C : ReplayBox n) : Decidable (B.SameEndpoints C) :=
  inferInstanceAs (Decidable (∀i,B.lower i=C.lower i ∧ B.upper i=C.upper i))

theorem contains_of_sameEndpoints {n : ℕ} {B C : ReplayBox n}
    (h : B.SameEndpoints C) {x : Fin n → ℝ} (hx : B.Contains x) : C.Contains x := by
  intro i
  simpa only [(h i).1,(h i).2] using hx i

def midpoint {n : ℕ} (B : ReplayBox n) (i : Fin n) : ℚ :=
  (B.lower i+B.upper i)/2

def left {n : ℕ} (B : ReplayBox n) (i : Fin n) : ReplayBox n :=
  ⟨B.lower,fun j => if j=i then B.midpoint i else B.upper j⟩

def right {n : ℕ} (B : ReplayBox n) (i : Fin n) : ReplayBox n :=
  ⟨fun j => if j=i then B.midpoint i else B.lower j,B.upper⟩

theorem contains_left_or_right {n : ℕ} (B : ReplayBox n) (i : Fin n)
    {x : Fin n → ℝ} (hx : B.Contains x) :
    (B.left i).Contains x ∨ (B.right i).Contains x := by
  by_cases h : x i≤(B.midpoint i : ℝ)
  · left
    intro j
    by_cases hji : j=i
    · subst j
      exact ⟨(hx i).1,by simpa [left] using h⟩
    · simpa [left,hji] using hx j
  · right
    intro j
    by_cases hji : j=i
    · subst j
      exact ⟨by simpa [right] using (le_of_lt (lt_of_not_ge h)),(hx i).2⟩
    · simpa [right,hji] using hx j

end ReplayBox

inductive BoxReplay (n : ℕ) where
  | leaf (index : ℕ)
  | split (axis : Fin n) (left right : BoxReplay n)
  deriving Repr

def BoxReplay.Valid {n : ℕ} (table : ℕ → Option (ReplayBox n)) :
    BoxReplay n → ReplayBox n → Prop
  | .leaf i,B => match table i with
      | none => False
      | some C => B.SameEndpoints C
  | .split i l r,B => l.Valid table (B.left i) ∧ r.Valid table (B.right i)

instance BoxReplay.validDecidable {n : ℕ} (table : ℕ → Option (ReplayBox n))
    (T : BoxReplay n) (B : ReplayBox n) : Decidable (T.Valid table B) := by
  induction T generalizing B with
  | leaf i => unfold BoxReplay.Valid; split <;> infer_instance
  | split i l r hl hr =>
    unfold BoxReplay.Valid
    exact @instDecidableAnd _ _ (hl _) (hr _)

/-- Every point of the original closed box reaches a proved table entry.
The leaf property can itself be the conclusion of another checked subtree. -/
theorem BoxReplay.sound {n : ℕ} {table : ℕ → Option (ReplayBox n)}
    {P : (Fin n → ℝ) → Prop}
    (hleaf : ∀i C,table i=some C → ∀x,C.Contains x → P x)
    (T : BoxReplay n) {B : ReplayBox n} (hT : T.Valid table B) :
    ∀x,B.Contains x → P x := by
  induction T generalizing B with
  | leaf i =>
    intro x hx
    cases he : table i with
    | none => simp [BoxReplay.Valid,he] at hT
    | some C =>
      have hh : B.SameEndpoints C := by simpa [BoxReplay.Valid,he] using hT
      exact hleaf i C he x (ReplayBox.contains_of_sameEndpoints hh hx)
  | split i l r hl hr =>
    intro x hx
    rcases B.contains_left_or_right i hx with h | h
    · exact hl hT.1 x h
    · exact hr hT.2 x h

end SparseLowerTail.Numerics

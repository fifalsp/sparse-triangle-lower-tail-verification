import SparseLowerTail.Section05.OrderedBoxTightening

/-! Data-only replay of a sorted-box subdivision proposal. Every leaf must match
an independently proved table box; every empty node proves an inconsistent
interval. The checker never trusts a search program's success flag. -/
noncomputable section
namespace SparseLowerTail.Section05

/-- The split coordinate is stored; the exact midpoint is reconstructed. -/
inductive CoverReplayTree where
  | leaf (index : ℕ)
  | empty
  | split (axis : Fin 3) (left right : CoverReplayTree)
  deriving Repr

/-- Coordinate equality is finite and decidable, even though a box is encoded
by endpoint functions. -/
def LogBox.SameEndpoints (B C : LogBox) : Prop :=
  ∀ i,B.lower i=C.lower i ∧ B.upper i=C.upper i

instance (B C : LogBox) : Decidable (B.SameEndpoints C) :=
  inferInstanceAs (Decidable (∀ i,B.lower i=C.lower i ∧ B.upper i=C.upper i))

theorem LogBox.eq_of_sameEndpoints {B C : LogBox} (h : B.SameEndpoints C) : B=C :=
  LogBox.ext (fun i => (h i).1) (fun i => (h i).2)

def LogBox.midpoint (B : LogBox) (i : Fin 3) : ℚ := (B.lower i+B.upper i)/2

/-- A missing table index is rejected. The table can be supplied by a finite
array lookup; no out-of-range default box is silently accepted. -/
def CoverReplayTree.Valid (table : ℕ→Option LogBox) : CoverReplayTree→LogBox→Prop
  | .leaf i,B => match table i with
      | none => False
      | some C => B.tightenOrdered.SameEndpoints C
  | .empty,B => ∃ i : Fin 3,B.tightenOrdered.upper i<B.tightenOrdered.lower i
  | .split i l r,B =>
      let C := B.tightenOrdered
      l.Valid table (C.left i (C.midpoint i)) ∧ r.Valid table (C.right i (C.midpoint i))

instance CoverReplayTree.validDecidable (table : ℕ→Option LogBox)
    (T : CoverReplayTree) (B : LogBox) : Decidable (T.Valid table B) := by
  induction T generalizing B with
  | leaf i =>
    unfold CoverReplayTree.Valid
    split <;> infer_instance
  | empty =>
    unfold CoverReplayTree.Valid
    infer_instance
  | split i l r hl hr =>
    unfold CoverReplayTree.Valid
    exact @instDecidableAnd _ _ (hl _) (hr _)

/-- Semantic soundness of a purely numerical subdivision tree. Bounds are
reconstructed at each node and every ordered point reaches a proved leaf. -/
theorem CoverReplayTree.sound {table : ℕ→Option LogBox} {Q : ℝ}
    {P : EdgeTriple→Prop}
    (hleaf : ∀ i C,table i=some C → ∀ q∈C.region,q∈orderedLogDomain Q → P q)
    (T : CoverReplayTree) {B : LogBox} (hT : T.Valid table B) :
    ∀ q∈B.region,q∈orderedLogDomain Q → P q := by
  induction T generalizing B with
  | leaf i =>
    intro q hq hD
    have hq' := (B.mem_tightenOrdered_iff q hD.2.2.1 hD.2.1).mpr hq
    cases he : table i with
    | none => simp [CoverReplayTree.Valid,he] at hT
    | some C =>
      have hh : B.tightenOrdered=C := LogBox.eq_of_sameEndpoints
        (by simpa [CoverReplayTree.Valid,he] using hT)
      exact hleaf i C he q (hh ▸ hq') hD
  | empty =>
    intro q hq hD
    have hq' := (B.mem_tightenOrdered_iff q hD.2.2.1 hD.2.1).mpr hq
    obtain ⟨i,hi⟩ := hT
    have hi' : (B.tightenOrdered.upper i:ℝ)<(B.tightenOrdered.lower i:ℝ) := by exact_mod_cast hi
    exact False.elim (not_lt_of_ge ((hq' i).1.trans (hq' i).2) hi')
  | split i l r hl hr =>
    intro q hq hD
    have hq' := (B.mem_tightenOrdered_iff q hD.2.2.1 hD.2.1).mpr hq
    rcases B.tightenOrdered.mem_left_or_right hq' i (B.tightenOrdered.midpoint i) with h | h
    · exact hl hT.1 q h hD
    · exact hr hT.2 q h hD

end SparseLowerTail.Section05

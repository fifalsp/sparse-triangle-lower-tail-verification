import SparseLowerTail.Section05.CoverTreeReplay
import SparseLowerTail.Numerics.IntervalProgram

/-! Balanced finite lookup tables for exact cover replay. Each table entry is
checked separately; lookup soundness avoids a linear case split on leaf indices. -/
namespace SparseLowerTail.Numerics.RegisterTree

def All {α : Type} (P : α → Prop) : RegisterTree α → Prop
  | .leaf a => P a
  | .branch l r => l.All P ∧ r.All P

theorem All.get {α : Type} {P : α → Prop} {t : RegisterTree α}
    (h : t.All P) (i : ℕ) : P (t.get i) := by
  induction t generalizing i with
  | leaf a => exact h
  | branch l r hl hr =>
    simp only [RegisterTree.get]
    split_ifs
    · exact hl h.1 _
    · exact hr h.2 _
end SparseLowerTail.Numerics.RegisterTree

noncomputable section
namespace SparseLowerTail.Section05
open Numerics

def CoverBoxProperty (Q : ℝ) (P : EdgeTriple → Prop) : Option LogBox → Prop
  | none => True
  | some B => ∀ q ∈ B.region, q ∈ orderedLogDomain Q → P q

theorem CoverReplayTree.sound_table {table : RegisterTree (Option LogBox)}
    {Q : ℝ} {P : EdgeTriple → Prop}
    (hleaf : table.All (CoverBoxProperty Q P))
    (T : CoverReplayTree) {B : LogBox} (hT : T.Valid table.get B) :
    ∀ q∈B.region,q∈orderedLogDomain Q → P q := by
  refine T.sound (Q := Q) (P := P) ?_ hT
  intro i C hi
  have h := hleaf.get i
  simpa only [hi,CoverBoxProperty] using h

end SparseLowerTail.Section05

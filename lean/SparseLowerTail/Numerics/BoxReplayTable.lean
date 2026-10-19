import SparseLowerTail.Numerics.BoxReplay
import SparseLowerTail.Section05.CoverReplayTable

/-! Balanced lookup tables for multidimensional subdivision proofs. -/
noncomputable section
namespace SparseLowerTail.Numerics

def ReplayBoxProperty {n : ℕ} (P : (Fin n → ℝ) → Prop) : Option (ReplayBox n) → Prop
  | none => True
  | some B => ∀x,B.Contains x → P x

theorem BoxReplay.sound_table {n : ℕ} {table : RegisterTree (Option (ReplayBox n))}
    {P : (Fin n → ℝ) → Prop} (hleaf : table.All (ReplayBoxProperty P))
    (T : BoxReplay n) {B : ReplayBox n} (hT : T.Valid table.get B) :
    ∀x,B.Contains x → P x := by
  refine T.sound (P := P) ?_ hT
  intro i C hi
  have h := hleaf.get i
  simpa only [hi,ReplayBoxProperty] using h

end SparseLowerTail.Numerics

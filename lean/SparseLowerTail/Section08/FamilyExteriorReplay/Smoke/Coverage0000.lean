import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Leaves0000

/-! Generated proposal data. Every theorem must pass the Lean kernel.
The full ABB neighborhood remains an explicit internal premise. -/
namespace SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage0000
def initialBox : ReplayBox 4 := ⟨![(39/10 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(53/10 : ℚ),(3/8 : ℚ),(3/8 : ℚ),(3/4 : ℚ)]⟩
def leafTable : RegisterTree (Option (ReplayBox 4)) := (.branch (.branch (.branch (.branch (.leaf (some domain0)) (.leaf (some domain8))) (.branch (.leaf (some domain4)) (.leaf (none)))) (.branch (.branch (.leaf (some domain2)) (.leaf (none))) (.branch (.leaf (some domain6)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some domain1)) (.leaf (some domain9))) (.branch (.leaf (some domain5)) (.leaf (none)))) (.branch (.branch (.leaf (some domain3)) (.leaf (none))) (.branch (.leaf (some domain7)) (.leaf (none))))))
def subdivision : BoxReplay 4 := (.split 3 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 0 (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7))) (.split 1 (.leaf 8) (.leaf 9))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (hABB : FamilyABBLocal) : leafTable.All (ReplayBoxProperty familyCompactProperty) := ⟨⟨⟨⟨conclusion0 hABB,conclusion8 hABB⟩,⟨conclusion4 hABB,True.intro⟩⟩,⟨⟨conclusion2 hABB,True.intro⟩,⟨conclusion6 hABB,True.intro⟩⟩⟩,⟨⟨⟨conclusion1 hABB,conclusion9 hABB⟩,⟨conclusion5 hABB,True.intro⟩⟩,⟨⟨conclusion3 hABB,True.intro⟩,⟨conclusion7 hABB,True.intro⟩⟩⟩⟩
theorem covered (hABB : FamilyABBLocal) : ∀x,initialBox.Contains x → familyCompactProperty x :=
  subdivision.sound_table (leaf_proofs hABB) valid
end Coverage0000

end SparseLowerTail.Section08.FamilyExteriorReplay.Smoke

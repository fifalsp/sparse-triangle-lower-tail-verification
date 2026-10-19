import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Leaves0000

/-! Generated untrusted proposals; all assertions require Lean kernel checks. -/
namespace SparseLowerTail.Section08.FamilyABBReplay.Smoke
open SparseLowerTail.Numerics
open SparseLowerTail.Certificate SparseLowerTail.Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage0000
def initialBox : ReplayBox 4 := ⟨![(39/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)],![(251/64 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ)]⟩
def leafTable : RegisterTree (Option (ReplayBox 4)) := (.branch (.branch (.branch (.branch (.branch (.leaf (some offsetBox0)) (.leaf (some offsetBox16))) (.branch (.leaf (some offsetBox8)) (.leaf (none)))) (.branch (.branch (.leaf (some offsetBox4)) (.leaf (none))) (.branch (.leaf (some offsetBox12)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some offsetBox2)) (.leaf (some offsetBox18))) (.branch (.leaf (some offsetBox10)) (.leaf (none)))) (.branch (.branch (.leaf (some offsetBox6)) (.leaf (none))) (.branch (.leaf (some offsetBox14)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some offsetBox1)) (.leaf (some offsetBox17))) (.branch (.leaf (some offsetBox9)) (.leaf (none)))) (.branch (.branch (.leaf (some offsetBox5)) (.leaf (none))) (.branch (.leaf (some offsetBox13)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some offsetBox3)) (.leaf (some offsetBox19))) (.branch (.leaf (some offsetBox11)) (.leaf (none)))) (.branch (.branch (.leaf (some offsetBox7)) (.leaf (none))) (.branch (.leaf (some offsetBox15)) (.leaf (none)))))))
def subdivision : BoxReplay 4 := (.split 1 (.split 2 (.split 3 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.leaf 2)) (.split 0 (.split 1 (.leaf 3) (.leaf 4)) (.leaf 5))) (.split 3 (.split 0 (.split 1 (.leaf 6) (.leaf 7)) (.leaf 8)) (.split 0 (.split 1 (.leaf 9) (.leaf 10)) (.leaf 11)))) (.split 2 (.split 3 (.split 0 (.leaf 12) (.leaf 13)) (.split 0 (.leaf 14) (.leaf 15))) (.split 3 (.split 0 (.leaf 16) (.leaf 17)) (.split 0 (.leaf 18) (.leaf 19)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs : leafTable.All (ReplayBoxProperty familyABBOffsetProperty) := ⟨⟨⟨⟨⟨conclusion0,conclusion16⟩,⟨conclusion8,True.intro⟩⟩,⟨⟨conclusion4,True.intro⟩,⟨conclusion12,True.intro⟩⟩⟩,⟨⟨⟨conclusion2,conclusion18⟩,⟨conclusion10,True.intro⟩⟩,⟨⟨conclusion6,True.intro⟩,⟨conclusion14,True.intro⟩⟩⟩⟩,⟨⟨⟨⟨conclusion1,conclusion17⟩,⟨conclusion9,True.intro⟩⟩,⟨⟨conclusion5,True.intro⟩,⟨conclusion13,True.intro⟩⟩⟩,⟨⟨⟨conclusion3,conclusion19⟩,⟨conclusion11,True.intro⟩⟩,⟨⟨conclusion7,True.intro⟩,⟨conclusion15,True.intro⟩⟩⟩⟩⟩
theorem covered : ∀x,initialBox.Contains x → familyABBOffsetProperty x :=
  subdivision.sound_table leaf_proofs valid
end Coverage0000

end SparseLowerTail.Section08.FamilyABBReplay.Smoke

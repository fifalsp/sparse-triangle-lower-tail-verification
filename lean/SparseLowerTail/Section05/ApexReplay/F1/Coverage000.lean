import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.ApexReplay.F1.Leaves000

/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace SparseLowerTail.Section05.ApexReplay.F1
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage000
def initialBox : LogBox := ⟨![(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(3287/8192 : ℚ),(3287/8192 : ℚ),(3287/8192 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box0)) (.leaf (some box8))) (.branch (.leaf (some box4)) (.leaf (none)))) (.branch (.branch (.leaf (some box2)) (.leaf (some box10))) (.branch (.leaf (some box6)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box1)) (.leaf (some box9))) (.branch (.leaf (some box5)) (.leaf (none)))) (.branch (.branch (.leaf (some box3)) (.leaf (none))) (.branch (.leaf (some box7)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 0 (.split 0 (.leaf 0) (.leaf 1)) (.split 1 (.split 0 (.leaf 2) (.split 1 (.leaf 3) (.leaf 4))) (.split 2 (.split 0 (.leaf 5) (.split 1 (.leaf 6) (.leaf 7))) (.split 0 (.leaf 8) (.split 1 (.leaf 9) (.leaf 10))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (ApexLeafConclusion 0)) :=
  ⟨⟨⟨⟨(fun _ hq _ => conclusion0 hq),(fun _ hq _ => conclusion8 hq)⟩,⟨(fun _ hq _ => conclusion4 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => conclusion2 hq),(fun _ hq _ => conclusion10 hq)⟩,⟨(fun _ hq _ => conclusion6 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => conclusion1 hq),(fun _ hq _ => conclusion9 hq)⟩,⟨(fun _ hq _ => conclusion5 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => conclusion3 hq),True.intro⟩,⟨(fun _ hq _ => conclusion7 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → ApexLeafConclusion 0 q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage000

end SparseLowerTail.Section05.ApexReplay.F1

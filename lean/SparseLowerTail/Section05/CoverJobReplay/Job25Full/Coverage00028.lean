import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00038
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00039

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00028
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box612)) (.leaf (some box628))) (.branch (.leaf (some box620)) (.leaf (none)))) (.branch (.branch (.leaf (some box616)) (.leaf (some box632))) (.branch (.leaf (some box624)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box614)) (.leaf (some box630))) (.branch (.leaf (some box622)) (.leaf (none)))) (.branch (.branch (.leaf (some box618)) (.leaf (some box634))) (.branch (.leaf (some box626)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box613)) (.leaf (some box629))) (.branch (.leaf (some box621)) (.leaf (none)))) (.branch (.branch (.leaf (some box617)) (.leaf (some box633))) (.branch (.leaf (some box625)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box615)) (.leaf (some box631))) (.branch (.leaf (some box623)) (.leaf (none)))) (.branch (.branch (.leaf (some box619)) (.leaf (some box635))) (.branch (.leaf (some box627)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 2 (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7))) (.split 0 (.split 1 (.leaf 8) (.leaf 9)) (.split 1 (.leaf 10) (.leaf 11))))) (.split 1 (.split 0 (.split 1 (.leaf 12) (.leaf 13)) (.split 1 (.leaf 14) (.leaf 15))) (.split 2 (.split 0 (.split 1 (.leaf 16) (.leaf 17)) (.split 1 (.leaf 18) (.leaf 19))) (.split 0 (.split 1 (.leaf 20) (.leaf 21)) (.split 1 (.leaf 22) (.leaf 23))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive612 hq),(fun _ hq _ => positive628 hq)⟩,⟨(fun _ hq _ => positive620 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive616 hq),(fun _ hq _ => positive632 hq)⟩,⟨(fun _ hq _ => positive624 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive614 hq),(fun _ hq _ => positive630 hq)⟩,⟨(fun _ hq _ => positive622 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive618 hq),(fun _ hq _ => positive634 hq)⟩,⟨(fun _ hq _ => positive626 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive613 hq),(fun _ hq _ => positive629 hq)⟩,⟨(fun _ hq _ => positive621 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive617 hq),(fun _ hq _ => positive633 hq)⟩,⟨(fun _ hq _ => positive625 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive615 hq),(fun _ hq _ => positive631 hq)⟩,⟨(fun _ hq _ => positive623 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive619 hq),(fun _ hq _ => positive635 hq)⟩,⟨(fun _ hq _ => positive627 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00028

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

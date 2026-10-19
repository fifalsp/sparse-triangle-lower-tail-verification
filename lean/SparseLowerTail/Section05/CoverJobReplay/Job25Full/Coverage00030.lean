import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00040
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00041
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00042

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00030
def initialBox : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box648)) (.leaf (some box664))) (.branch (.leaf (some box656)) (.leaf (some box672)))) (.branch (.branch (.leaf (some box652)) (.leaf (some box668))) (.branch (.leaf (some box660)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box650)) (.leaf (some box666))) (.branch (.leaf (some box658)) (.leaf (some box674)))) (.branch (.branch (.leaf (some box654)) (.leaf (some box670))) (.branch (.leaf (some box662)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box649)) (.leaf (some box665))) (.branch (.leaf (some box657)) (.leaf (some box673)))) (.branch (.branch (.leaf (some box653)) (.leaf (some box669))) (.branch (.leaf (some box661)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box651)) (.leaf (some box667))) (.branch (.leaf (some box659)) (.leaf (some box675)))) (.branch (.branch (.leaf (some box655)) (.leaf (some box671))) (.branch (.leaf (some box663)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 2 (.leaf 16) (.leaf 17)) (.split 1 (.split 2 (.leaf 18) (.leaf 19)) (.split 2 (.leaf 20) (.leaf 21)))) (.split 0 (.split 2 (.leaf 22) (.leaf 23)) (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive648 hq),(fun _ hq _ => positive664 hq)⟩,⟨(fun _ hq _ => positive656 hq),(fun _ hq _ => positive672 hq)⟩⟩,⟨⟨(fun _ hq _ => positive652 hq),(fun _ hq _ => positive668 hq)⟩,⟨(fun _ hq _ => positive660 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive650 hq),(fun _ hq _ => positive666 hq)⟩,⟨(fun _ hq _ => positive658 hq),(fun _ hq _ => positive674 hq)⟩⟩,⟨⟨(fun _ hq _ => positive654 hq),(fun _ hq _ => positive670 hq)⟩,⟨(fun _ hq _ => positive662 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive649 hq),(fun _ hq _ => positive665 hq)⟩,⟨(fun _ hq _ => positive657 hq),(fun _ hq _ => positive673 hq)⟩⟩,⟨⟨(fun _ hq _ => positive653 hq),(fun _ hq _ => positive669 hq)⟩,⟨(fun _ hq _ => positive661 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive651 hq),(fun _ hq _ => positive667 hq)⟩,⟨(fun _ hq _ => positive659 hq),(fun _ hq _ => positive675 hq)⟩⟩,⟨⟨(fun _ hq _ => positive655 hq),(fun _ hq _ => positive671 hq)⟩,⟨(fun _ hq _ => positive663 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00030

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

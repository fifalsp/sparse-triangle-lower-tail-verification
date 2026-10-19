import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00002
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00003

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00002
def initialBox : LogBox := ⟨![(4821/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box42)) (.leaf (some box58))) (.branch (.leaf (some box50)) (.leaf (none)))) (.branch (.branch (.leaf (some box46)) (.leaf (none))) (.branch (.leaf (some box54)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box44)) (.leaf (some box60))) (.branch (.leaf (some box52)) (.leaf (none)))) (.branch (.branch (.leaf (some box48)) (.leaf (none))) (.branch (.leaf (some box56)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box43)) (.leaf (some box59))) (.branch (.leaf (some box51)) (.leaf (none)))) (.branch (.branch (.leaf (some box47)) (.leaf (none))) (.branch (.leaf (some box55)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box45)) (.leaf (some box61))) (.branch (.leaf (some box53)) (.leaf (none)))) (.branch (.branch (.leaf (some box49)) (.leaf (none))) (.branch (.leaf (some box57)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.leaf 0) (.split 2 (.leaf 1) (.leaf 2))) (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.split 2 (.leaf 12) (.leaf 13)))) (.split 0 (.split 1 (.leaf 14) (.split 2 (.leaf 15) (.leaf 16))) (.split 1 (.leaf 17) (.split 2 (.leaf 18) (.leaf 19))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive42 hq),(fun _ hq _ => positive58 hq)⟩,⟨(fun _ hq _ => positive50 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive46 hq),True.intro⟩,⟨(fun _ hq _ => positive54 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive44 hq),(fun _ hq _ => positive60 hq)⟩,⟨(fun _ hq _ => positive52 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive48 hq),True.intro⟩,⟨(fun _ hq _ => positive56 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive43 hq),(fun _ hq _ => positive59 hq)⟩,⟨(fun _ hq _ => positive51 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive47 hq),True.intro⟩,⟨(fun _ hq _ => positive55 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive45 hq),(fun _ hq _ => positive61 hq)⟩,⟨(fun _ hq _ => positive53 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive49 hq),True.intro⟩,⟨(fun _ hq _ => positive57 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00002

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

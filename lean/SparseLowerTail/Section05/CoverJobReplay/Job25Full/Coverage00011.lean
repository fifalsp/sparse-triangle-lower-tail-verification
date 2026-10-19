import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00012
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00013

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00011
def initialBox : LogBox := ⟨![(4821/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box200)) (.leaf (some box216))) (.branch (.leaf (some box208)) (.leaf (none)))) (.branch (.branch (.leaf (some box204)) (.leaf (none))) (.branch (.leaf (some box212)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box202)) (.leaf (none))) (.branch (.leaf (some box210)) (.leaf (none)))) (.branch (.branch (.leaf (some box206)) (.leaf (none))) (.branch (.leaf (some box214)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box201)) (.leaf (some box217))) (.branch (.leaf (some box209)) (.leaf (none)))) (.branch (.branch (.leaf (some box205)) (.leaf (none))) (.branch (.leaf (some box213)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box203)) (.leaf (none))) (.branch (.leaf (some box211)) (.leaf (none)))) (.branch (.branch (.leaf (some box207)) (.leaf (none))) (.branch (.leaf (some box215)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.leaf 0) (.split 2 (.leaf 1) (.leaf 2))) (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.split 2 (.leaf 12) (.leaf 13)))) (.split 0 (.split 1 (.leaf 14) (.leaf 15)) (.split 1 (.leaf 16) (.leaf 17)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive200 hq),(fun _ hq _ => positive216 hq)⟩,⟨(fun _ hq _ => positive208 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive204 hq),True.intro⟩,⟨(fun _ hq _ => positive212 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive202 hq),True.intro⟩,⟨(fun _ hq _ => positive210 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive206 hq),True.intro⟩,⟨(fun _ hq _ => positive214 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive201 hq),(fun _ hq _ => positive217 hq)⟩,⟨(fun _ hq _ => positive209 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive205 hq),True.intro⟩,⟨(fun _ hq _ => positive213 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive203 hq),True.intro⟩,⟨(fun _ hq _ => positive211 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive207 hq),True.intro⟩,⟨(fun _ hq _ => positive215 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00011

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00011
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00012

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00010
def initialBox : LogBox := ⟨![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box188)) (.leaf (some box196))) (.branch (.leaf (some box192)) (.leaf (none)))) (.branch (.branch (.leaf (some box190)) (.leaf (some box198))) (.branch (.leaf (some box194)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box189)) (.leaf (some box197))) (.branch (.leaf (some box193)) (.leaf (none)))) (.branch (.branch (.leaf (some box191)) (.leaf (some box199))) (.branch (.leaf (some box195)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 2 (.split 0 (.leaf 4) (.leaf 5)) (.leaf 6))) (.split 1 (.split 0 (.split 1 (.leaf 7) (.leaf 8)) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive188 hq),(fun _ hq _ => positive196 hq)⟩,⟨(fun _ hq _ => positive192 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive190 hq),(fun _ hq _ => positive198 hq)⟩,⟨(fun _ hq _ => positive194 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive189 hq),(fun _ hq _ => positive197 hq)⟩,⟨(fun _ hq _ => positive193 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive191 hq),(fun _ hq _ => positive199 hq)⟩,⟨(fun _ hq _ => positive195 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00010

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

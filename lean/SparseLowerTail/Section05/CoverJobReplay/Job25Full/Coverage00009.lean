import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00010
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00011

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00009
def initialBox : LogBox := ⟨![(8035/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box175)) (.leaf (some box183))) (.branch (.leaf (some box179)) (.leaf (some box187)))) (.branch (.branch (.leaf (some box177)) (.leaf (some box185))) (.branch (.leaf (some box181)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box176)) (.leaf (some box184))) (.branch (.leaf (some box180)) (.leaf (none)))) (.branch (.branch (.leaf (some box178)) (.leaf (some box186))) (.branch (.leaf (some box182)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7)))) (.split 2 (.split 0 (.leaf 8) (.leaf 9)) (.split 0 (.split 1 (.leaf 10) (.leaf 11)) (.leaf 12))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive175 hq),(fun _ hq _ => positive183 hq)⟩,⟨(fun _ hq _ => positive179 hq),(fun _ hq _ => positive187 hq)⟩⟩,⟨⟨(fun _ hq _ => positive177 hq),(fun _ hq _ => positive185 hq)⟩,⟨(fun _ hq _ => positive181 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive176 hq),(fun _ hq _ => positive184 hq)⟩,⟨(fun _ hq _ => positive180 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive178 hq),(fun _ hq _ => positive186 hq)⟩,⟨(fun _ hq _ => positive182 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00009

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

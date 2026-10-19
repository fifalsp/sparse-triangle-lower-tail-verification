import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00050
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00051

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00036
def initialBox : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box809)) (.leaf (some box817))) (.branch (.leaf (some box813)) (.leaf (some box821)))) (.branch (.branch (.leaf (some box811)) (.leaf (some box819))) (.branch (.leaf (some box815)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box810)) (.leaf (some box818))) (.branch (.leaf (some box814)) (.leaf (some box822)))) (.branch (.branch (.leaf (some box812)) (.leaf (some box820))) (.branch (.leaf (some box816)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7)))) (.split 2 (.split 0 (.split 1 (.leaf 8) (.leaf 9)) (.leaf 10)) (.split 0 (.split 1 (.leaf 11) (.leaf 12)) (.leaf 13))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive809 hq),(fun _ hq _ => positive817 hq)⟩,⟨(fun _ hq _ => positive813 hq),(fun _ hq _ => positive821 hq)⟩⟩,⟨⟨(fun _ hq _ => positive811 hq),(fun _ hq _ => positive819 hq)⟩,⟨(fun _ hq _ => positive815 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive810 hq),(fun _ hq _ => positive818 hq)⟩,⟨(fun _ hq _ => positive814 hq),(fun _ hq _ => positive822 hq)⟩⟩,⟨⟨(fun _ hq _ => positive812 hq),(fun _ hq _ => positive820 hq)⟩,⟨(fun _ hq _ => positive816 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00036

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

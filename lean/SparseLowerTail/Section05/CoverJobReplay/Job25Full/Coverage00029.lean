import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00039
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00040

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00029
def initialBox : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box636)) (.leaf (some box644))) (.branch (.leaf (some box640)) (.leaf (none)))) (.branch (.branch (.leaf (some box638)) (.leaf (some box646))) (.branch (.leaf (some box642)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box637)) (.leaf (some box645))) (.branch (.leaf (some box641)) (.leaf (none)))) (.branch (.branch (.leaf (some box639)) (.leaf (some box647))) (.branch (.leaf (some box643)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 2 (.leaf 0) (.leaf 1)) (.split 1 (.split 2 (.leaf 2) (.leaf 3)) (.split 2 (.leaf 4) (.leaf 5)))) (.split 0 (.split 2 (.leaf 6) (.leaf 7)) (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive636 hq),(fun _ hq _ => positive644 hq)⟩,⟨(fun _ hq _ => positive640 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive638 hq),(fun _ hq _ => positive646 hq)⟩,⟨(fun _ hq _ => positive642 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive637 hq),(fun _ hq _ => positive645 hq)⟩,⟨(fun _ hq _ => positive641 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive639 hq),(fun _ hq _ => positive647 hq)⟩,⟨(fun _ hq _ => positive643 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00029

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

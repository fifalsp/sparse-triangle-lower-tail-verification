import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00003
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00004

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00003
def initialBox : LogBox := ⟨![(1607/2048 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box62)) (.leaf (some box70))) (.branch (.leaf (some box66)) (.leaf (some box74)))) (.branch (.branch (.leaf (some box64)) (.leaf (some box72))) (.branch (.leaf (some box68)) (.leaf (some box76))))) (.branch (.branch (.branch (.leaf (some box63)) (.leaf (some box71))) (.branch (.leaf (some box67)) (.leaf (some box75)))) (.branch (.branch (.leaf (some box65)) (.leaf (some box73))) (.branch (.leaf (some box69)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 2 (.leaf 0) (.leaf 1)) (.split 1 (.split 2 (.leaf 2) (.leaf 3)) (.split 2 (.leaf 4) (.leaf 5)))) (.split 0 (.split 2 (.split 0 (.leaf 6) (.leaf 7)) (.split 0 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.split 0 (.leaf 11) (.leaf 12))) (.split 2 (.leaf 13) (.leaf 14)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive62 hq),(fun _ hq _ => positive70 hq)⟩,⟨(fun _ hq _ => positive66 hq),(fun _ hq _ => positive74 hq)⟩⟩,⟨⟨(fun _ hq _ => positive64 hq),(fun _ hq _ => positive72 hq)⟩,⟨(fun _ hq _ => positive68 hq),(fun _ hq _ => positive76 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive63 hq),(fun _ hq _ => positive71 hq)⟩,⟨(fun _ hq _ => positive67 hq),(fun _ hq _ => positive75 hq)⟩⟩,⟨⟨(fun _ hq _ => positive65 hq),(fun _ hq _ => positive73 hq)⟩,⟨(fun _ hq _ => positive69 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00003

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

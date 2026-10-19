import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00046
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00047
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00048

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00034
def initialBox : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box746)) (.leaf (some box762))) (.branch (.leaf (some box754)) (.leaf (some box770)))) (.branch (.branch (.leaf (some box750)) (.leaf (some box766))) (.branch (.leaf (some box758)) (.leaf (some box774))))) (.branch (.branch (.branch (.leaf (some box748)) (.leaf (some box764))) (.branch (.leaf (some box756)) (.leaf (some box772)))) (.branch (.branch (.leaf (some box752)) (.leaf (some box768))) (.branch (.leaf (some box760)) (.leaf (some box776)))))) (.branch (.branch (.branch (.branch (.leaf (some box747)) (.leaf (some box763))) (.branch (.leaf (some box755)) (.leaf (some box771)))) (.branch (.branch (.leaf (some box751)) (.leaf (some box767))) (.branch (.leaf (some box759)) (.leaf (some box775))))) (.branch (.branch (.branch (.leaf (some box749)) (.leaf (some box765))) (.branch (.leaf (some box757)) (.leaf (some box773)))) (.branch (.branch (.leaf (some box753)) (.leaf (some box769))) (.branch (.leaf (some box761)) (.leaf (some box777)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 16) (.leaf 17)) (.split 2 (.leaf 18) (.leaf 19))) (.split 1 (.split 2 (.leaf 20) (.leaf 21)) (.split 2 (.leaf 22) (.leaf 23)))) (.split 0 (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))) (.split 1 (.split 2 (.leaf 28) (.leaf 29)) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive746 hq),(fun _ hq _ => positive762 hq)⟩,⟨(fun _ hq _ => positive754 hq),(fun _ hq _ => positive770 hq)⟩⟩,⟨⟨(fun _ hq _ => positive750 hq),(fun _ hq _ => positive766 hq)⟩,⟨(fun _ hq _ => positive758 hq),(fun _ hq _ => positive774 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive748 hq),(fun _ hq _ => positive764 hq)⟩,⟨(fun _ hq _ => positive756 hq),(fun _ hq _ => positive772 hq)⟩⟩,⟨⟨(fun _ hq _ => positive752 hq),(fun _ hq _ => positive768 hq)⟩,⟨(fun _ hq _ => positive760 hq),(fun _ hq _ => positive776 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive747 hq),(fun _ hq _ => positive763 hq)⟩,⟨(fun _ hq _ => positive755 hq),(fun _ hq _ => positive771 hq)⟩⟩,⟨⟨(fun _ hq _ => positive751 hq),(fun _ hq _ => positive767 hq)⟩,⟨(fun _ hq _ => positive759 hq),(fun _ hq _ => positive775 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive749 hq),(fun _ hq _ => positive765 hq)⟩,⟨(fun _ hq _ => positive757 hq),(fun _ hq _ => positive773 hq)⟩⟩,⟨⟨(fun _ hq _ => positive753 hq),(fun _ hq _ => positive769 hq)⟩,⟨(fun _ hq _ => positive761 hq),(fun _ hq _ => positive777 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00034

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

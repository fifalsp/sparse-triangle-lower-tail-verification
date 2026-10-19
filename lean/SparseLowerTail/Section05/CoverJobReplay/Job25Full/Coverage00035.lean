import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00048
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00049
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00050

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00035
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box778)) (.leaf (some box794))) (.branch (.leaf (some box786)) (.leaf (some box802)))) (.branch (.branch (.leaf (some box782)) (.leaf (some box798))) (.branch (.leaf (some box790)) (.leaf (some box806))))) (.branch (.branch (.branch (.leaf (some box780)) (.leaf (some box796))) (.branch (.leaf (some box788)) (.leaf (some box804)))) (.branch (.branch (.leaf (some box784)) (.leaf (some box800))) (.branch (.leaf (some box792)) (.leaf (some box808)))))) (.branch (.branch (.branch (.branch (.leaf (some box779)) (.leaf (some box795))) (.branch (.leaf (some box787)) (.leaf (some box803)))) (.branch (.branch (.leaf (some box783)) (.leaf (some box799))) (.branch (.leaf (some box791)) (.leaf (some box807))))) (.branch (.branch (.branch (.leaf (some box781)) (.leaf (some box797))) (.branch (.leaf (some box789)) (.leaf (some box805)))) (.branch (.branch (.leaf (some box785)) (.leaf (some box801))) (.branch (.leaf (some box793)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.leaf 12) (.split 2 (.leaf 13) (.leaf 14))))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 15) (.leaf 16)) (.split 2 (.leaf 17) (.leaf 18))) (.split 1 (.split 2 (.leaf 19) (.leaf 20)) (.split 2 (.leaf 21) (.leaf 22)))) (.split 0 (.split 1 (.split 2 (.leaf 23) (.leaf 24)) (.split 2 (.leaf 25) (.leaf 26))) (.split 1 (.split 2 (.leaf 27) (.leaf 28)) (.split 2 (.leaf 29) (.leaf 30))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive778 hq),(fun _ hq _ => positive794 hq)⟩,⟨(fun _ hq _ => positive786 hq),(fun _ hq _ => positive802 hq)⟩⟩,⟨⟨(fun _ hq _ => positive782 hq),(fun _ hq _ => positive798 hq)⟩,⟨(fun _ hq _ => positive790 hq),(fun _ hq _ => positive806 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive780 hq),(fun _ hq _ => positive796 hq)⟩,⟨(fun _ hq _ => positive788 hq),(fun _ hq _ => positive804 hq)⟩⟩,⟨⟨(fun _ hq _ => positive784 hq),(fun _ hq _ => positive800 hq)⟩,⟨(fun _ hq _ => positive792 hq),(fun _ hq _ => positive808 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive779 hq),(fun _ hq _ => positive795 hq)⟩,⟨(fun _ hq _ => positive787 hq),(fun _ hq _ => positive803 hq)⟩⟩,⟨⟨(fun _ hq _ => positive783 hq),(fun _ hq _ => positive799 hq)⟩,⟨(fun _ hq _ => positive791 hq),(fun _ hq _ => positive807 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive781 hq),(fun _ hq _ => positive797 hq)⟩,⟨(fun _ hq _ => positive789 hq),(fun _ hq _ => positive805 hq)⟩⟩,⟨⟨(fun _ hq _ => positive785 hq),(fun _ hq _ => positive801 hq)⟩,⟨(fun _ hq _ => positive793 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00035

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

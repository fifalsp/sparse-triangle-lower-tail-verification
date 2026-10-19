import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00052
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00053

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00038
def initialBox : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box835)) (.leaf (some box851))) (.branch (.leaf (some box843)) (.leaf (some box859)))) (.branch (.branch (.leaf (some box839)) (.leaf (some box855))) (.branch (.leaf (some box847)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box837)) (.leaf (some box853))) (.branch (.leaf (some box845)) (.leaf (some box861)))) (.branch (.branch (.leaf (some box841)) (.leaf (some box857))) (.branch (.leaf (some box849)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box836)) (.leaf (some box852))) (.branch (.leaf (some box844)) (.leaf (some box860)))) (.branch (.branch (.leaf (some box840)) (.leaf (some box856))) (.branch (.leaf (some box848)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box838)) (.leaf (some box854))) (.branch (.leaf (some box846)) (.leaf (some box862)))) (.branch (.branch (.leaf (some box842)) (.leaf (some box858))) (.branch (.leaf (some box850)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 2 (.leaf 16) (.leaf 17)) (.split 1 (.split 2 (.leaf 18) (.leaf 19)) (.split 2 (.leaf 20) (.leaf 21)))) (.split 0 (.split 2 (.leaf 22) (.leaf 23)) (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive835 hq),(fun _ hq _ => positive851 hq)⟩,⟨(fun _ hq _ => positive843 hq),(fun _ hq _ => positive859 hq)⟩⟩,⟨⟨(fun _ hq _ => positive839 hq),(fun _ hq _ => positive855 hq)⟩,⟨(fun _ hq _ => positive847 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive837 hq),(fun _ hq _ => positive853 hq)⟩,⟨(fun _ hq _ => positive845 hq),(fun _ hq _ => positive861 hq)⟩⟩,⟨⟨(fun _ hq _ => positive841 hq),(fun _ hq _ => positive857 hq)⟩,⟨(fun _ hq _ => positive849 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive836 hq),(fun _ hq _ => positive852 hq)⟩,⟨(fun _ hq _ => positive844 hq),(fun _ hq _ => positive860 hq)⟩⟩,⟨⟨(fun _ hq _ => positive840 hq),(fun _ hq _ => positive856 hq)⟩,⟨(fun _ hq _ => positive848 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive838 hq),(fun _ hq _ => positive854 hq)⟩,⟨(fun _ hq _ => positive846 hq),(fun _ hq _ => positive862 hq)⟩⟩,⟨⟨(fun _ hq _ => positive842 hq),(fun _ hq _ => positive858 hq)⟩,⟨(fun _ hq _ => positive850 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00038

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00053
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00054
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00055

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00039
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box863)) (.leaf (some box879))) (.branch (.leaf (some box871)) (.leaf (none)))) (.branch (.branch (.leaf (some box867)) (.leaf (none))) (.branch (.leaf (some box875)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box865)) (.leaf (some box881))) (.branch (.leaf (some box873)) (.leaf (none)))) (.branch (.branch (.leaf (some box869)) (.leaf (none))) (.branch (.leaf (some box877)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box864)) (.leaf (some box880))) (.branch (.leaf (some box872)) (.leaf (none)))) (.branch (.branch (.leaf (some box868)) (.leaf (none))) (.branch (.leaf (some box876)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box866)) (.leaf (none))) (.branch (.leaf (some box874)) (.leaf (none)))) (.branch (.branch (.leaf (some box870)) (.leaf (none))) (.branch (.leaf (some box878)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 2 (.split 0 (.split 2 (.leaf 0) (.leaf 1)) (.split 1 (.split 2 (.leaf 2) (.leaf 3)) (.split 2 (.leaf 4) (.leaf 5)))) (.split 0 (.split 2 (.leaf 6) (.leaf 7)) (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.leaf 10)))) (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 11) (.leaf 12)) (.leaf 13)) (.split 0 (.split 1 (.leaf 14) (.leaf 15)) (.leaf 16))) (.split 2 (.leaf 17) (.leaf 18))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive863 hq),(fun _ hq _ => positive879 hq)⟩,⟨(fun _ hq _ => positive871 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive867 hq),True.intro⟩,⟨(fun _ hq _ => positive875 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive865 hq),(fun _ hq _ => positive881 hq)⟩,⟨(fun _ hq _ => positive873 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive869 hq),True.intro⟩,⟨(fun _ hq _ => positive877 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive864 hq),(fun _ hq _ => positive880 hq)⟩,⟨(fun _ hq _ => positive872 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive868 hq),True.intro⟩,⟨(fun _ hq _ => positive876 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive866 hq),True.intro⟩,⟨(fun _ hq _ => positive874 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive870 hq),True.intro⟩,⟨(fun _ hq _ => positive878 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00039

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

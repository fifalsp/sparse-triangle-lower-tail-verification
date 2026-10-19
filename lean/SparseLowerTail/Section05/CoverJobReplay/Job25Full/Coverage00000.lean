import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00000
def initialBox : LogBox := ⟨![(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box0)) (.leaf (some box16))) (.branch (.leaf (some box8)) (.leaf (none)))) (.branch (.branch (.leaf (some box4)) (.leaf (none))) (.branch (.leaf (some box12)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box2)) (.leaf (some box18))) (.branch (.leaf (some box10)) (.leaf (none)))) (.branch (.branch (.leaf (some box6)) (.leaf (none))) (.branch (.leaf (some box14)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box1)) (.leaf (some box17))) (.branch (.leaf (some box9)) (.leaf (none)))) (.branch (.branch (.leaf (some box5)) (.leaf (none))) (.branch (.leaf (some box13)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box3)) (.leaf (some box19))) (.branch (.leaf (some box11)) (.leaf (none)))) (.branch (.branch (.leaf (some box7)) (.leaf (none))) (.branch (.leaf (some box15)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 0 (.leaf 0) (.split 1 (.leaf 1) (.leaf 2))) (.split 1 (.split 0 (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5))) (.split 1 (.leaf 6) (.split 2 (.leaf 7) (.leaf 8)))) (.split 2 (.split 0 (.split 2 (.leaf 9) (.leaf 10)) (.split 1 (.split 2 (.leaf 11) (.leaf 12)) (.split 2 (.leaf 13) (.leaf 14)))) (.split 0 (.leaf 15) (.split 1 (.leaf 16) (.split 2 (.leaf 17) (.split 0 (.leaf 18) (.leaf 19))))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive0 hq),(fun _ hq _ => positive16 hq)⟩,⟨(fun _ hq _ => positive8 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive4 hq),True.intro⟩,⟨(fun _ hq _ => positive12 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive2 hq),(fun _ hq _ => positive18 hq)⟩,⟨(fun _ hq _ => positive10 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive6 hq),True.intro⟩,⟨(fun _ hq _ => positive14 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive1 hq),(fun _ hq _ => positive17 hq)⟩,⟨(fun _ hq _ => positive9 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive5 hq),True.intro⟩,⟨(fun _ hq _ => positive13 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive3 hq),(fun _ hq _ => positive19 hq)⟩,⟨(fun _ hq _ => positive11 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive7 hq),True.intro⟩,⟨(fun _ hq _ => positive15 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00000

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

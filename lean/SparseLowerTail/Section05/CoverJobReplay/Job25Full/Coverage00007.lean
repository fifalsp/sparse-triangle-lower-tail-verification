import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00008
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00009

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00007
def initialBox : LogBox := ⟨![(8035/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box136)) (.leaf (some box152))) (.branch (.leaf (some box144)) (.leaf (none)))) (.branch (.branch (.leaf (some box140)) (.leaf (none))) (.branch (.leaf (some box148)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box138)) (.leaf (none))) (.branch (.leaf (some box146)) (.leaf (none)))) (.branch (.branch (.leaf (some box142)) (.leaf (none))) (.branch (.leaf (some box150)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box137)) (.leaf (some box153))) (.branch (.leaf (some box145)) (.leaf (none)))) (.branch (.branch (.leaf (some box141)) (.leaf (none))) (.branch (.leaf (some box149)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box139)) (.leaf (none))) (.branch (.leaf (some box147)) (.leaf (none)))) (.branch (.branch (.leaf (some box143)) (.leaf (none))) (.branch (.leaf (some box151)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.leaf 0) (.split 2 (.leaf 1) (.leaf 2))) (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.split 2 (.leaf 12) (.leaf 13)))) (.split 0 (.split 1 (.leaf 14) (.leaf 15)) (.split 1 (.leaf 16) (.leaf 17)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive136 hq),(fun _ hq _ => positive152 hq)⟩,⟨(fun _ hq _ => positive144 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive140 hq),True.intro⟩,⟨(fun _ hq _ => positive148 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive138 hq),True.intro⟩,⟨(fun _ hq _ => positive146 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive142 hq),True.intro⟩,⟨(fun _ hq _ => positive150 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive137 hq),(fun _ hq _ => positive153 hq)⟩,⟨(fun _ hq _ => positive145 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive141 hq),True.intro⟩,⟨(fun _ hq _ => positive149 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive139 hq),True.intro⟩,⟨(fun _ hq _ => positive147 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive143 hq),True.intro⟩,⟨(fun _ hq _ => positive151 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00007

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00022
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00023

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00019
def initialBox : LogBox := ⟨![(8035/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box360)) (.leaf (some box376))) (.branch (.leaf (some box368)) (.leaf (none)))) (.branch (.branch (.leaf (some box364)) (.leaf (none))) (.branch (.leaf (some box372)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box362)) (.leaf (none))) (.branch (.leaf (some box370)) (.leaf (none)))) (.branch (.branch (.leaf (some box366)) (.leaf (none))) (.branch (.leaf (some box374)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box361)) (.leaf (some box377))) (.branch (.leaf (some box369)) (.leaf (none)))) (.branch (.branch (.leaf (some box365)) (.leaf (none))) (.branch (.leaf (some box373)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box363)) (.leaf (none))) (.branch (.leaf (some box371)) (.leaf (none)))) (.branch (.branch (.leaf (some box367)) (.leaf (none))) (.branch (.leaf (some box375)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 2 (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7))) (.leaf 8))) (.split 1 (.split 0 (.split 1 (.leaf 9) (.leaf 10)) (.split 1 (.leaf 11) (.leaf 12))) (.split 2 (.split 0 (.split 1 (.leaf 13) (.leaf 14)) (.split 1 (.leaf 15) (.leaf 16))) (.leaf 17))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive360 hq),(fun _ hq _ => positive376 hq)⟩,⟨(fun _ hq _ => positive368 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive364 hq),True.intro⟩,⟨(fun _ hq _ => positive372 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive362 hq),True.intro⟩,⟨(fun _ hq _ => positive370 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive366 hq),True.intro⟩,⟨(fun _ hq _ => positive374 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive361 hq),(fun _ hq _ => positive377 hq)⟩,⟨(fun _ hq _ => positive369 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive365 hq),True.intro⟩,⟨(fun _ hq _ => positive373 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive363 hq),True.intro⟩,⟨(fun _ hq _ => positive371 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive367 hq),True.intro⟩,⟨(fun _ hq _ => positive375 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00019

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

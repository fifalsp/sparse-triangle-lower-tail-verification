import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00042
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00043
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00044

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00032
def initialBox : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box686)) (.leaf (some box702))) (.branch (.leaf (some box694)) (.leaf (some box710)))) (.branch (.branch (.leaf (some box690)) (.leaf (some box706))) (.branch (.leaf (some box698)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box688)) (.leaf (some box704))) (.branch (.leaf (some box696)) (.leaf (some box712)))) (.branch (.branch (.leaf (some box692)) (.leaf (some box708))) (.branch (.leaf (some box700)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box687)) (.leaf (some box703))) (.branch (.leaf (some box695)) (.leaf (some box711)))) (.branch (.branch (.leaf (some box691)) (.leaf (some box707))) (.branch (.leaf (some box699)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box689)) (.leaf (some box705))) (.branch (.leaf (some box697)) (.leaf (some box713)))) (.branch (.branch (.leaf (some box693)) (.leaf (some box709))) (.branch (.leaf (some box701)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 2 (.leaf 16) (.leaf 17)) (.split 1 (.split 2 (.leaf 18) (.leaf 19)) (.split 2 (.leaf 20) (.leaf 21)))) (.split 0 (.split 2 (.leaf 22) (.leaf 23)) (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive686 hq),(fun _ hq _ => positive702 hq)⟩,⟨(fun _ hq _ => positive694 hq),(fun _ hq _ => positive710 hq)⟩⟩,⟨⟨(fun _ hq _ => positive690 hq),(fun _ hq _ => positive706 hq)⟩,⟨(fun _ hq _ => positive698 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive688 hq),(fun _ hq _ => positive704 hq)⟩,⟨(fun _ hq _ => positive696 hq),(fun _ hq _ => positive712 hq)⟩⟩,⟨⟨(fun _ hq _ => positive692 hq),(fun _ hq _ => positive708 hq)⟩,⟨(fun _ hq _ => positive700 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive687 hq),(fun _ hq _ => positive703 hq)⟩,⟨(fun _ hq _ => positive695 hq),(fun _ hq _ => positive711 hq)⟩⟩,⟨⟨(fun _ hq _ => positive691 hq),(fun _ hq _ => positive707 hq)⟩,⟨(fun _ hq _ => positive699 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive689 hq),(fun _ hq _ => positive705 hq)⟩,⟨(fun _ hq _ => positive697 hq),(fun _ hq _ => positive713 hq)⟩⟩,⟨⟨(fun _ hq _ => positive693 hq),(fun _ hq _ => positive709 hq)⟩,⟨(fun _ hq _ => positive701 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00032

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

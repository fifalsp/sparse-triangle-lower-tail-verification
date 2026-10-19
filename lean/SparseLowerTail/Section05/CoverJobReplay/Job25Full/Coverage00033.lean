import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00044
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00045
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00046

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00033
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box714)) (.leaf (some box730))) (.branch (.leaf (some box722)) (.leaf (some box738)))) (.branch (.branch (.leaf (some box718)) (.leaf (some box734))) (.branch (.leaf (some box726)) (.leaf (some box742))))) (.branch (.branch (.branch (.leaf (some box716)) (.leaf (some box732))) (.branch (.leaf (some box724)) (.leaf (some box740)))) (.branch (.branch (.leaf (some box720)) (.leaf (some box736))) (.branch (.leaf (some box728)) (.leaf (some box744)))))) (.branch (.branch (.branch (.branch (.leaf (some box715)) (.leaf (some box731))) (.branch (.leaf (some box723)) (.leaf (some box739)))) (.branch (.branch (.leaf (some box719)) (.leaf (some box735))) (.branch (.leaf (some box727)) (.leaf (some box743))))) (.branch (.branch (.branch (.leaf (some box717)) (.leaf (some box733))) (.branch (.leaf (some box725)) (.leaf (some box741)))) (.branch (.branch (.leaf (some box721)) (.leaf (some box737))) (.branch (.leaf (some box729)) (.leaf (some box745)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 16) (.leaf 17)) (.split 2 (.leaf 18) (.leaf 19))) (.split 1 (.split 2 (.leaf 20) (.leaf 21)) (.split 2 (.leaf 22) (.leaf 23)))) (.split 0 (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))) (.split 1 (.split 2 (.leaf 28) (.leaf 29)) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive714 hq),(fun _ hq _ => positive730 hq)⟩,⟨(fun _ hq _ => positive722 hq),(fun _ hq _ => positive738 hq)⟩⟩,⟨⟨(fun _ hq _ => positive718 hq),(fun _ hq _ => positive734 hq)⟩,⟨(fun _ hq _ => positive726 hq),(fun _ hq _ => positive742 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive716 hq),(fun _ hq _ => positive732 hq)⟩,⟨(fun _ hq _ => positive724 hq),(fun _ hq _ => positive740 hq)⟩⟩,⟨⟨(fun _ hq _ => positive720 hq),(fun _ hq _ => positive736 hq)⟩,⟨(fun _ hq _ => positive728 hq),(fun _ hq _ => positive744 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive715 hq),(fun _ hq _ => positive731 hq)⟩,⟨(fun _ hq _ => positive723 hq),(fun _ hq _ => positive739 hq)⟩⟩,⟨⟨(fun _ hq _ => positive719 hq),(fun _ hq _ => positive735 hq)⟩,⟨(fun _ hq _ => positive727 hq),(fun _ hq _ => positive743 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive717 hq),(fun _ hq _ => positive733 hq)⟩,⟨(fun _ hq _ => positive725 hq),(fun _ hq _ => positive741 hq)⟩⟩,⟨⟨(fun _ hq _ => positive721 hq),(fun _ hq _ => positive737 hq)⟩,⟨(fun _ hq _ => positive729 hq),(fun _ hq _ => positive745 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00033

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00036
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00037
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00038

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00027
def initialBox : LogBox := ⟨![(11249/2048 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box580)) (.leaf (some box596))) (.branch (.leaf (some box588)) (.leaf (some box604)))) (.branch (.branch (.leaf (some box584)) (.leaf (some box600))) (.branch (.leaf (some box592)) (.leaf (some box608))))) (.branch (.branch (.branch (.leaf (some box582)) (.leaf (some box598))) (.branch (.leaf (some box590)) (.leaf (some box606)))) (.branch (.branch (.leaf (some box586)) (.leaf (some box602))) (.branch (.leaf (some box594)) (.leaf (some box610)))))) (.branch (.branch (.branch (.branch (.leaf (some box581)) (.leaf (some box597))) (.branch (.leaf (some box589)) (.leaf (some box605)))) (.branch (.branch (.leaf (some box585)) (.leaf (some box601))) (.branch (.leaf (some box593)) (.leaf (some box609))))) (.branch (.branch (.branch (.leaf (some box583)) (.leaf (some box599))) (.branch (.leaf (some box591)) (.leaf (some box607)))) (.branch (.branch (.leaf (some box587)) (.leaf (some box603))) (.branch (.leaf (some box595)) (.leaf (some box611)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 16) (.leaf 17)) (.split 2 (.leaf 18) (.leaf 19))) (.split 1 (.split 2 (.leaf 20) (.leaf 21)) (.split 2 (.leaf 22) (.leaf 23)))) (.split 0 (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))) (.split 1 (.split 2 (.leaf 28) (.leaf 29)) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive580 hq),(fun _ hq _ => positive596 hq)⟩,⟨(fun _ hq _ => positive588 hq),(fun _ hq _ => positive604 hq)⟩⟩,⟨⟨(fun _ hq _ => positive584 hq),(fun _ hq _ => positive600 hq)⟩,⟨(fun _ hq _ => positive592 hq),(fun _ hq _ => positive608 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive582 hq),(fun _ hq _ => positive598 hq)⟩,⟨(fun _ hq _ => positive590 hq),(fun _ hq _ => positive606 hq)⟩⟩,⟨⟨(fun _ hq _ => positive586 hq),(fun _ hq _ => positive602 hq)⟩,⟨(fun _ hq _ => positive594 hq),(fun _ hq _ => positive610 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive581 hq),(fun _ hq _ => positive597 hq)⟩,⟨(fun _ hq _ => positive589 hq),(fun _ hq _ => positive605 hq)⟩⟩,⟨⟨(fun _ hq _ => positive585 hq),(fun _ hq _ => positive601 hq)⟩,⟨(fun _ hq _ => positive593 hq),(fun _ hq _ => positive609 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive583 hq),(fun _ hq _ => positive599 hq)⟩,⟨(fun _ hq _ => positive591 hq),(fun _ hq _ => positive607 hq)⟩⟩,⟨⟨(fun _ hq _ => positive587 hq),(fun _ hq _ => positive603 hq)⟩,⟨(fun _ hq _ => positive595 hq),(fun _ hq _ => positive611 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00027

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

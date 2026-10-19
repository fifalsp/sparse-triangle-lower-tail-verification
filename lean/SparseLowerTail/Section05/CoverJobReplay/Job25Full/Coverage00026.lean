import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00034
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00035
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00036

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00026
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box548)) (.leaf (some box564))) (.branch (.leaf (some box556)) (.leaf (some box572)))) (.branch (.branch (.leaf (some box552)) (.leaf (some box568))) (.branch (.leaf (some box560)) (.leaf (some box576))))) (.branch (.branch (.branch (.leaf (some box550)) (.leaf (some box566))) (.branch (.leaf (some box558)) (.leaf (some box574)))) (.branch (.branch (.leaf (some box554)) (.leaf (some box570))) (.branch (.leaf (some box562)) (.leaf (some box578)))))) (.branch (.branch (.branch (.branch (.leaf (some box549)) (.leaf (some box565))) (.branch (.leaf (some box557)) (.leaf (some box573)))) (.branch (.branch (.leaf (some box553)) (.leaf (some box569))) (.branch (.leaf (some box561)) (.leaf (some box577))))) (.branch (.branch (.branch (.leaf (some box551)) (.leaf (some box567))) (.branch (.leaf (some box559)) (.leaf (some box575)))) (.branch (.branch (.leaf (some box555)) (.leaf (some box571))) (.branch (.leaf (some box563)) (.leaf (some box579)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 16) (.leaf 17)) (.split 2 (.leaf 18) (.leaf 19))) (.split 1 (.split 2 (.leaf 20) (.leaf 21)) (.split 2 (.leaf 22) (.leaf 23)))) (.split 0 (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))) (.split 1 (.split 2 (.leaf 28) (.leaf 29)) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive548 hq),(fun _ hq _ => positive564 hq)⟩,⟨(fun _ hq _ => positive556 hq),(fun _ hq _ => positive572 hq)⟩⟩,⟨⟨(fun _ hq _ => positive552 hq),(fun _ hq _ => positive568 hq)⟩,⟨(fun _ hq _ => positive560 hq),(fun _ hq _ => positive576 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive550 hq),(fun _ hq _ => positive566 hq)⟩,⟨(fun _ hq _ => positive558 hq),(fun _ hq _ => positive574 hq)⟩⟩,⟨⟨(fun _ hq _ => positive554 hq),(fun _ hq _ => positive570 hq)⟩,⟨(fun _ hq _ => positive562 hq),(fun _ hq _ => positive578 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive549 hq),(fun _ hq _ => positive565 hq)⟩,⟨(fun _ hq _ => positive557 hq),(fun _ hq _ => positive573 hq)⟩⟩,⟨⟨(fun _ hq _ => positive553 hq),(fun _ hq _ => positive569 hq)⟩,⟨(fun _ hq _ => positive561 hq),(fun _ hq _ => positive577 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive551 hq),(fun _ hq _ => positive567 hq)⟩,⟨(fun _ hq _ => positive559 hq),(fun _ hq _ => positive575 hq)⟩⟩,⟨⟨(fun _ hq _ => positive555 hq),(fun _ hq _ => positive571 hq)⟩,⟨(fun _ hq _ => positive563 hq),(fun _ hq _ => positive579 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00026

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

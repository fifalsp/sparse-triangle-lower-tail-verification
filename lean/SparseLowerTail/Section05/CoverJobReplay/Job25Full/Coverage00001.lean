import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00001
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00002

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00001
def initialBox : LogBox := ⟨![(1607/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box20)) (.leaf (some box36))) (.branch (.leaf (some box28)) (.leaf (none)))) (.branch (.branch (.leaf (some box24)) (.leaf (some box40))) (.branch (.leaf (some box32)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box22)) (.leaf (some box38))) (.branch (.leaf (some box30)) (.leaf (none)))) (.branch (.branch (.leaf (some box26)) (.leaf (none))) (.branch (.leaf (some box34)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box21)) (.leaf (some box37))) (.branch (.leaf (some box29)) (.leaf (none)))) (.branch (.branch (.leaf (some box25)) (.leaf (some box41))) (.branch (.leaf (some box33)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box23)) (.leaf (some box39))) (.branch (.leaf (some box31)) (.leaf (none)))) (.branch (.branch (.leaf (some box27)) (.leaf (none))) (.branch (.leaf (some box35)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.leaf 0) (.split 2 (.leaf 1) (.leaf 2))) (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.split 2 (.leaf 12) (.leaf 13)))) (.split 0 (.split 1 (.leaf 14) (.split 2 (.leaf 15) (.split 0 (.leaf 16) (.leaf 17)))) (.split 1 (.leaf 18) (.split 2 (.leaf 19) (.split 0 (.leaf 20) (.leaf 21)))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive20 hq),(fun _ hq _ => positive36 hq)⟩,⟨(fun _ hq _ => positive28 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive24 hq),(fun _ hq _ => positive40 hq)⟩,⟨(fun _ hq _ => positive32 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive22 hq),(fun _ hq _ => positive38 hq)⟩,⟨(fun _ hq _ => positive30 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive26 hq),True.intro⟩,⟨(fun _ hq _ => positive34 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive21 hq),(fun _ hq _ => positive37 hq)⟩,⟨(fun _ hq _ => positive29 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive25 hq),(fun _ hq _ => positive41 hq)⟩,⟨(fun _ hq _ => positive33 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive23 hq),(fun _ hq _ => positive39 hq)⟩,⟨(fun _ hq _ => positive31 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive27 hq),True.intro⟩,⟨(fun _ hq _ => positive35 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00001

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

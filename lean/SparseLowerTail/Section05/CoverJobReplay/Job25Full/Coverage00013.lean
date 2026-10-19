import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00014
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00015
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00016

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00013
def initialBox : LogBox := ⟨![(4821/2048 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box235)) (.leaf (some box251))) (.branch (.leaf (some box243)) (.leaf (some box259)))) (.branch (.branch (.leaf (some box239)) (.leaf (some box255))) (.branch (.leaf (some box247)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box237)) (.leaf (some box253))) (.branch (.leaf (some box245)) (.leaf (none)))) (.branch (.branch (.leaf (some box241)) (.leaf (some box257))) (.branch (.leaf (some box249)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box236)) (.leaf (some box252))) (.branch (.leaf (some box244)) (.leaf (some box260)))) (.branch (.branch (.leaf (some box240)) (.leaf (some box256))) (.branch (.leaf (some box248)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box238)) (.leaf (some box254))) (.branch (.leaf (some box246)) (.leaf (none)))) (.branch (.branch (.leaf (some box242)) (.leaf (some box258))) (.branch (.leaf (some box250)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7)))) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 10) (.leaf 11)) (.split 1 (.leaf 12) (.leaf 13))) (.split 0 (.split 1 (.leaf 14) (.leaf 15)) (.split 1 (.leaf 16) (.leaf 17)))) (.split 2 (.leaf 18) (.leaf 19)))) (.split 0 (.split 1 (.leaf 20) (.split 2 (.leaf 21) (.leaf 22))) (.split 1 (.leaf 23) (.split 2 (.leaf 24) (.leaf 25)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive235 hq),(fun _ hq _ => positive251 hq)⟩,⟨(fun _ hq _ => positive243 hq),(fun _ hq _ => positive259 hq)⟩⟩,⟨⟨(fun _ hq _ => positive239 hq),(fun _ hq _ => positive255 hq)⟩,⟨(fun _ hq _ => positive247 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive237 hq),(fun _ hq _ => positive253 hq)⟩,⟨(fun _ hq _ => positive245 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive241 hq),(fun _ hq _ => positive257 hq)⟩,⟨(fun _ hq _ => positive249 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive236 hq),(fun _ hq _ => positive252 hq)⟩,⟨(fun _ hq _ => positive244 hq),(fun _ hq _ => positive260 hq)⟩⟩,⟨⟨(fun _ hq _ => positive240 hq),(fun _ hq _ => positive256 hq)⟩,⟨(fun _ hq _ => positive248 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive238 hq),(fun _ hq _ => positive254 hq)⟩,⟨(fun _ hq _ => positive246 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive242 hq),(fun _ hq _ => positive258 hq)⟩,⟨(fun _ hq _ => positive250 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00013

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00017
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00018

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00015
def initialBox : LogBox := ⟨![(4821/2048 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box275)) (.leaf (some box291))) (.branch (.leaf (some box283)) (.leaf (some box299)))) (.branch (.branch (.leaf (some box279)) (.leaf (some box295))) (.branch (.leaf (some box287)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box277)) (.leaf (some box293))) (.branch (.leaf (some box285)) (.leaf (some box301)))) (.branch (.branch (.leaf (some box281)) (.leaf (some box297))) (.branch (.leaf (some box289)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box276)) (.leaf (some box292))) (.branch (.leaf (some box284)) (.leaf (some box300)))) (.branch (.branch (.leaf (some box280)) (.leaf (some box296))) (.branch (.leaf (some box288)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box278)) (.leaf (some box294))) (.branch (.leaf (some box286)) (.leaf (some box302)))) (.branch (.branch (.leaf (some box282)) (.leaf (some box298))) (.branch (.leaf (some box290)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 2 (.leaf 16) (.leaf 17)) (.split 1 (.split 2 (.leaf 18) (.leaf 19)) (.split 2 (.leaf 20) (.leaf 21)))) (.split 0 (.split 2 (.leaf 22) (.leaf 23)) (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive275 hq),(fun _ hq _ => positive291 hq)⟩,⟨(fun _ hq _ => positive283 hq),(fun _ hq _ => positive299 hq)⟩⟩,⟨⟨(fun _ hq _ => positive279 hq),(fun _ hq _ => positive295 hq)⟩,⟨(fun _ hq _ => positive287 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive277 hq),(fun _ hq _ => positive293 hq)⟩,⟨(fun _ hq _ => positive285 hq),(fun _ hq _ => positive301 hq)⟩⟩,⟨⟨(fun _ hq _ => positive281 hq),(fun _ hq _ => positive297 hq)⟩,⟨(fun _ hq _ => positive289 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive276 hq),(fun _ hq _ => positive292 hq)⟩,⟨(fun _ hq _ => positive284 hq),(fun _ hq _ => positive300 hq)⟩⟩,⟨⟨(fun _ hq _ => positive280 hq),(fun _ hq _ => positive296 hq)⟩,⟨(fun _ hq _ => positive288 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive278 hq),(fun _ hq _ => positive294 hq)⟩,⟨(fun _ hq _ => positive286 hq),(fun _ hq _ => positive302 hq)⟩⟩,⟨⟨(fun _ hq _ => positive282 hq),(fun _ hq _ => positive298 hq)⟩,⟨(fun _ hq _ => positive290 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00015

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

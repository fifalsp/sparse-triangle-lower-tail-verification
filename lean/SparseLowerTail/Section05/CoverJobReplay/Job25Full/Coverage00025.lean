import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00032
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00033
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00034

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00025
def initialBox : LogBox := ⟨![(11249/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box516)) (.leaf (some box532))) (.branch (.leaf (some box524)) (.leaf (some box540)))) (.branch (.branch (.leaf (some box520)) (.leaf (some box536))) (.branch (.leaf (some box528)) (.leaf (some box544))))) (.branch (.branch (.branch (.leaf (some box518)) (.leaf (some box534))) (.branch (.leaf (some box526)) (.leaf (some box542)))) (.branch (.branch (.leaf (some box522)) (.leaf (some box538))) (.branch (.leaf (some box530)) (.leaf (some box546)))))) (.branch (.branch (.branch (.branch (.leaf (some box517)) (.leaf (some box533))) (.branch (.leaf (some box525)) (.leaf (some box541)))) (.branch (.branch (.leaf (some box521)) (.leaf (some box537))) (.branch (.leaf (some box529)) (.leaf (some box545))))) (.branch (.branch (.branch (.leaf (some box519)) (.leaf (some box535))) (.branch (.leaf (some box527)) (.leaf (some box543)))) (.branch (.branch (.leaf (some box523)) (.leaf (some box539))) (.branch (.leaf (some box531)) (.leaf (some box547)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 2 (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7))) (.leaf 8))) (.split 1 (.split 0 (.split 1 (.leaf 9) (.leaf 10)) (.split 1 (.leaf 11) (.leaf 12))) (.split 2 (.split 0 (.split 1 (.leaf 13) (.leaf 14)) (.split 1 (.leaf 15) (.leaf 16))) (.leaf 17)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 18) (.leaf 19)) (.split 2 (.leaf 20) (.leaf 21))) (.split 1 (.split 2 (.leaf 22) (.leaf 23)) (.split 2 (.leaf 24) (.leaf 25)))) (.split 0 (.split 1 (.leaf 26) (.split 2 (.leaf 27) (.leaf 28))) (.split 1 (.leaf 29) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive516 hq),(fun _ hq _ => positive532 hq)⟩,⟨(fun _ hq _ => positive524 hq),(fun _ hq _ => positive540 hq)⟩⟩,⟨⟨(fun _ hq _ => positive520 hq),(fun _ hq _ => positive536 hq)⟩,⟨(fun _ hq _ => positive528 hq),(fun _ hq _ => positive544 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive518 hq),(fun _ hq _ => positive534 hq)⟩,⟨(fun _ hq _ => positive526 hq),(fun _ hq _ => positive542 hq)⟩⟩,⟨⟨(fun _ hq _ => positive522 hq),(fun _ hq _ => positive538 hq)⟩,⟨(fun _ hq _ => positive530 hq),(fun _ hq _ => positive546 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive517 hq),(fun _ hq _ => positive533 hq)⟩,⟨(fun _ hq _ => positive525 hq),(fun _ hq _ => positive541 hq)⟩⟩,⟨⟨(fun _ hq _ => positive521 hq),(fun _ hq _ => positive537 hq)⟩,⟨(fun _ hq _ => positive529 hq),(fun _ hq _ => positive545 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive519 hq),(fun _ hq _ => positive535 hq)⟩,⟨(fun _ hq _ => positive527 hq),(fun _ hq _ => positive543 hq)⟩⟩,⟨⟨(fun _ hq _ => positive523 hq),(fun _ hq _ => positive539 hq)⟩,⟨(fun _ hq _ => positive531 hq),(fun _ hq _ => positive547 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00025

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00030
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00031
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00032

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00024
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box484)) (.leaf (some box500))) (.branch (.leaf (some box492)) (.leaf (some box508)))) (.branch (.branch (.leaf (some box488)) (.leaf (some box504))) (.branch (.leaf (some box496)) (.leaf (some box512))))) (.branch (.branch (.branch (.leaf (some box486)) (.leaf (some box502))) (.branch (.leaf (some box494)) (.leaf (some box510)))) (.branch (.branch (.leaf (some box490)) (.leaf (some box506))) (.branch (.leaf (some box498)) (.leaf (some box514)))))) (.branch (.branch (.branch (.branch (.leaf (some box485)) (.leaf (some box501))) (.branch (.leaf (some box493)) (.leaf (some box509)))) (.branch (.branch (.leaf (some box489)) (.leaf (some box505))) (.branch (.leaf (some box497)) (.leaf (some box513))))) (.branch (.branch (.branch (.leaf (some box487)) (.leaf (some box503))) (.branch (.leaf (some box495)) (.leaf (some box511)))) (.branch (.branch (.leaf (some box491)) (.leaf (some box507))) (.branch (.leaf (some box499)) (.leaf (some box515)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 2 (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7))) (.leaf 8))) (.split 1 (.split 0 (.split 1 (.leaf 9) (.leaf 10)) (.split 1 (.leaf 11) (.leaf 12))) (.split 2 (.split 0 (.split 1 (.leaf 13) (.leaf 14)) (.split 1 (.leaf 15) (.leaf 16))) (.leaf 17)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 18) (.leaf 19)) (.split 2 (.leaf 20) (.leaf 21))) (.split 1 (.split 2 (.leaf 22) (.leaf 23)) (.split 2 (.leaf 24) (.leaf 25)))) (.split 0 (.split 1 (.leaf 26) (.split 2 (.leaf 27) (.leaf 28))) (.split 1 (.leaf 29) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive484 hq),(fun _ hq _ => positive500 hq)⟩,⟨(fun _ hq _ => positive492 hq),(fun _ hq _ => positive508 hq)⟩⟩,⟨⟨(fun _ hq _ => positive488 hq),(fun _ hq _ => positive504 hq)⟩,⟨(fun _ hq _ => positive496 hq),(fun _ hq _ => positive512 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive486 hq),(fun _ hq _ => positive502 hq)⟩,⟨(fun _ hq _ => positive494 hq),(fun _ hq _ => positive510 hq)⟩⟩,⟨⟨(fun _ hq _ => positive490 hq),(fun _ hq _ => positive506 hq)⟩,⟨(fun _ hq _ => positive498 hq),(fun _ hq _ => positive514 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive485 hq),(fun _ hq _ => positive501 hq)⟩,⟨(fun _ hq _ => positive493 hq),(fun _ hq _ => positive509 hq)⟩⟩,⟨⟨(fun _ hq _ => positive489 hq),(fun _ hq _ => positive505 hq)⟩,⟨(fun _ hq _ => positive497 hq),(fun _ hq _ => positive513 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive487 hq),(fun _ hq _ => positive503 hq)⟩,⟨(fun _ hq _ => positive495 hq),(fun _ hq _ => positive511 hq)⟩⟩,⟨⟨(fun _ hq _ => positive491 hq),(fun _ hq _ => positive507 hq)⟩,⟨(fun _ hq _ => positive499 hq),(fun _ hq _ => positive515 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00024

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

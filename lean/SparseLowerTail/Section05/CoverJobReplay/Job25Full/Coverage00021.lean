import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00024
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00025
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00026

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00021
def initialBox : LogBox := ⟨![(1607/512 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box396)) (.leaf (some box412))) (.branch (.leaf (some box404)) (.leaf (some box420)))) (.branch (.branch (.leaf (some box400)) (.leaf (some box416))) (.branch (.leaf (some box408)) (.leaf (some box424))))) (.branch (.branch (.branch (.leaf (some box398)) (.leaf (some box414))) (.branch (.leaf (some box406)) (.leaf (some box422)))) (.branch (.branch (.leaf (some box402)) (.leaf (some box418))) (.branch (.leaf (some box410)) (.leaf (some box426)))))) (.branch (.branch (.branch (.branch (.leaf (some box397)) (.leaf (some box413))) (.branch (.leaf (some box405)) (.leaf (some box421)))) (.branch (.branch (.leaf (some box401)) (.leaf (some box417))) (.branch (.leaf (some box409)) (.leaf (some box425))))) (.branch (.branch (.branch (.leaf (some box399)) (.leaf (some box415))) (.branch (.leaf (some box407)) (.leaf (some box423)))) (.branch (.branch (.leaf (some box403)) (.leaf (some box419))) (.branch (.leaf (some box411)) (.leaf (some box427)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 16) (.leaf 17)) (.split 2 (.leaf 18) (.leaf 19))) (.split 1 (.split 2 (.leaf 20) (.leaf 21)) (.split 2 (.leaf 22) (.leaf 23)))) (.split 0 (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))) (.split 1 (.split 2 (.leaf 28) (.leaf 29)) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive396 hq),(fun _ hq _ => positive412 hq)⟩,⟨(fun _ hq _ => positive404 hq),(fun _ hq _ => positive420 hq)⟩⟩,⟨⟨(fun _ hq _ => positive400 hq),(fun _ hq _ => positive416 hq)⟩,⟨(fun _ hq _ => positive408 hq),(fun _ hq _ => positive424 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive398 hq),(fun _ hq _ => positive414 hq)⟩,⟨(fun _ hq _ => positive406 hq),(fun _ hq _ => positive422 hq)⟩⟩,⟨⟨(fun _ hq _ => positive402 hq),(fun _ hq _ => positive418 hq)⟩,⟨(fun _ hq _ => positive410 hq),(fun _ hq _ => positive426 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive397 hq),(fun _ hq _ => positive413 hq)⟩,⟨(fun _ hq _ => positive405 hq),(fun _ hq _ => positive421 hq)⟩⟩,⟨⟨(fun _ hq _ => positive401 hq),(fun _ hq _ => positive417 hq)⟩,⟨(fun _ hq _ => positive409 hq),(fun _ hq _ => positive425 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive399 hq),(fun _ hq _ => positive415 hq)⟩,⟨(fun _ hq _ => positive407 hq),(fun _ hq _ => positive423 hq)⟩⟩,⟨⟨(fun _ hq _ => positive403 hq),(fun _ hq _ => positive419 hq)⟩,⟨(fun _ hq _ => positive411 hq),(fun _ hq _ => positive427 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00021

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00026
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00027
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00028

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00022
def initialBox : LogBox := ⟨![(8035/2048 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box428)) (.leaf (some box444))) (.branch (.leaf (some box436)) (.leaf (some box452)))) (.branch (.branch (.leaf (some box432)) (.leaf (some box448))) (.branch (.leaf (some box440)) (.leaf (some box456))))) (.branch (.branch (.branch (.leaf (some box430)) (.leaf (some box446))) (.branch (.leaf (some box438)) (.leaf (some box454)))) (.branch (.branch (.leaf (some box434)) (.leaf (some box450))) (.branch (.leaf (some box442)) (.leaf (some box458)))))) (.branch (.branch (.branch (.branch (.leaf (some box429)) (.leaf (some box445))) (.branch (.leaf (some box437)) (.leaf (some box453)))) (.branch (.branch (.leaf (some box433)) (.leaf (some box449))) (.branch (.leaf (some box441)) (.leaf (some box457))))) (.branch (.branch (.branch (.leaf (some box431)) (.leaf (some box447))) (.branch (.leaf (some box439)) (.leaf (some box455)))) (.branch (.branch (.leaf (some box435)) (.leaf (some box451))) (.branch (.leaf (some box443)) (.leaf (some box459)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11))) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15))))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 16) (.leaf 17)) (.split 2 (.leaf 18) (.leaf 19))) (.split 1 (.split 2 (.leaf 20) (.leaf 21)) (.split 2 (.leaf 22) (.leaf 23)))) (.split 0 (.split 1 (.split 2 (.leaf 24) (.leaf 25)) (.split 2 (.leaf 26) (.leaf 27))) (.split 1 (.split 2 (.leaf 28) (.leaf 29)) (.split 2 (.leaf 30) (.leaf 31))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive428 hq),(fun _ hq _ => positive444 hq)⟩,⟨(fun _ hq _ => positive436 hq),(fun _ hq _ => positive452 hq)⟩⟩,⟨⟨(fun _ hq _ => positive432 hq),(fun _ hq _ => positive448 hq)⟩,⟨(fun _ hq _ => positive440 hq),(fun _ hq _ => positive456 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive430 hq),(fun _ hq _ => positive446 hq)⟩,⟨(fun _ hq _ => positive438 hq),(fun _ hq _ => positive454 hq)⟩⟩,⟨⟨(fun _ hq _ => positive434 hq),(fun _ hq _ => positive450 hq)⟩,⟨(fun _ hq _ => positive442 hq),(fun _ hq _ => positive458 hq)⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive429 hq),(fun _ hq _ => positive445 hq)⟩,⟨(fun _ hq _ => positive437 hq),(fun _ hq _ => positive453 hq)⟩⟩,⟨⟨(fun _ hq _ => positive433 hq),(fun _ hq _ => positive449 hq)⟩,⟨(fun _ hq _ => positive441 hq),(fun _ hq _ => positive457 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive431 hq),(fun _ hq _ => positive447 hq)⟩,⟨(fun _ hq _ => positive439 hq),(fun _ hq _ => positive455 hq)⟩⟩,⟨⟨(fun _ hq _ => positive435 hq),(fun _ hq _ => positive451 hq)⟩,⟨(fun _ hq _ => positive443 hq),(fun _ hq _ => positive459 hq)⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00022

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

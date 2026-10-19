import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00028
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00029
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00030

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00023
def initialBox : LogBox := ⟨![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box460)) (.leaf (some box476))) (.branch (.leaf (some box468)) (.leaf (none)))) (.branch (.branch (.leaf (some box464)) (.leaf (some box480))) (.branch (.leaf (some box472)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box462)) (.leaf (some box478))) (.branch (.leaf (some box470)) (.leaf (none)))) (.branch (.branch (.leaf (some box466)) (.leaf (some box482))) (.branch (.leaf (some box474)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box461)) (.leaf (some box477))) (.branch (.leaf (some box469)) (.leaf (none)))) (.branch (.branch (.leaf (some box465)) (.leaf (some box481))) (.branch (.leaf (some box473)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box463)) (.leaf (some box479))) (.branch (.leaf (some box471)) (.leaf (none)))) (.branch (.branch (.leaf (some box467)) (.leaf (some box483))) (.branch (.leaf (some box475)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 2 (.split 0 (.split 1 (.leaf 4) (.leaf 5)) (.split 1 (.leaf 6) (.leaf 7))) (.split 0 (.split 1 (.leaf 8) (.leaf 9)) (.split 1 (.leaf 10) (.leaf 11))))) (.split 1 (.split 0 (.split 1 (.leaf 12) (.leaf 13)) (.split 1 (.leaf 14) (.leaf 15))) (.split 2 (.split 0 (.split 1 (.leaf 16) (.leaf 17)) (.split 1 (.leaf 18) (.leaf 19))) (.split 0 (.split 1 (.leaf 20) (.leaf 21)) (.split 1 (.leaf 22) (.leaf 23))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive460 hq),(fun _ hq _ => positive476 hq)⟩,⟨(fun _ hq _ => positive468 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive464 hq),(fun _ hq _ => positive480 hq)⟩,⟨(fun _ hq _ => positive472 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive462 hq),(fun _ hq _ => positive478 hq)⟩,⟨(fun _ hq _ => positive470 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive466 hq),(fun _ hq _ => positive482 hq)⟩,⟨(fun _ hq _ => positive474 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive461 hq),(fun _ hq _ => positive477 hq)⟩,⟨(fun _ hq _ => positive469 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive465 hq),(fun _ hq _ => positive481 hq)⟩,⟨(fun _ hq _ => positive473 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive463 hq),(fun _ hq _ => positive479 hq)⟩,⟨(fun _ hq _ => positive471 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive467 hq),(fun _ hq _ => positive483 hq)⟩,⟨(fun _ hq _ => positive475 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00023

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

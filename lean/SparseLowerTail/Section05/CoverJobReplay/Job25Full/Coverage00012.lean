import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00013
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00014

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00012
def initialBox : LogBox := ⟨![(11249/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box218)) (.leaf (some box234))) (.branch (.leaf (some box226)) (.leaf (none)))) (.branch (.branch (.leaf (some box222)) (.leaf (none))) (.branch (.leaf (some box230)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box220)) (.leaf (none))) (.branch (.leaf (some box228)) (.leaf (none)))) (.branch (.branch (.leaf (some box224)) (.leaf (none))) (.branch (.leaf (some box232)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box219)) (.leaf (none))) (.branch (.leaf (some box227)) (.leaf (none)))) (.branch (.branch (.leaf (some box223)) (.leaf (none))) (.branch (.leaf (some box231)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box221)) (.leaf (none))) (.branch (.leaf (some box229)) (.leaf (none)))) (.branch (.branch (.leaf (some box225)) (.leaf (none))) (.branch (.leaf (some box233)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.leaf 0) (.split 2 (.leaf 1) (.leaf 2))) (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.leaf 12))) (.split 0 (.split 1 (.leaf 13) (.leaf 14)) (.split 1 (.leaf 15) (.leaf 16)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive218 hq),(fun _ hq _ => positive234 hq)⟩,⟨(fun _ hq _ => positive226 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive222 hq),True.intro⟩,⟨(fun _ hq _ => positive230 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive220 hq),True.intro⟩,⟨(fun _ hq _ => positive228 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive224 hq),True.intro⟩,⟨(fun _ hq _ => positive232 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive219 hq),True.intro⟩,⟨(fun _ hq _ => positive227 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive223 hq),True.intro⟩,⟨(fun _ hq _ => positive231 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive221 hq),True.intro⟩,⟨(fun _ hq _ => positive229 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive225 hq),True.intro⟩,⟨(fun _ hq _ => positive233 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00012

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

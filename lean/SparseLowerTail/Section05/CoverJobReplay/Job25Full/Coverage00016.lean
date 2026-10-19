import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00018
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00019

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00016
def initialBox : LogBox := ⟨![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box303)) (.leaf (some box311))) (.branch (.leaf (some box307)) (.leaf (some box315)))) (.branch (.branch (.leaf (some box305)) (.leaf (some box313))) (.branch (.leaf (some box309)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box304)) (.leaf (some box312))) (.branch (.leaf (some box308)) (.leaf (none)))) (.branch (.branch (.leaf (some box306)) (.leaf (some box314))) (.branch (.leaf (some box310)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 0 (.split 0 (.leaf 0) (.split 1 (.leaf 1) (.leaf 2))) (.split 1 (.split 0 (.split 1 (.leaf 3) (.leaf 4)) (.split 1 (.leaf 5) (.leaf 6))) (.split 2 (.split 0 (.leaf 7) (.split 1 (.leaf 8) (.leaf 9))) (.split 0 (.leaf 10) (.split 1 (.leaf 11) (.leaf 12))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive303 hq),(fun _ hq _ => positive311 hq)⟩,⟨(fun _ hq _ => positive307 hq),(fun _ hq _ => positive315 hq)⟩⟩,⟨⟨(fun _ hq _ => positive305 hq),(fun _ hq _ => positive313 hq)⟩,⟨(fun _ hq _ => positive309 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive304 hq),(fun _ hq _ => positive312 hq)⟩,⟨(fun _ hq _ => positive308 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive306 hq),(fun _ hq _ => positive314 hq)⟩,⟨(fun _ hq _ => positive310 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00016

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

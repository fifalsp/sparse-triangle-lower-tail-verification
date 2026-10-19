import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job00Smoke.Leaves00000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job00Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00000
def initialBox : LogBox := ⟨![(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(3287/16384 : ℚ),(3287/16384 : ℚ),(3287/16384 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.leaf (some box0)) (.leaf (some box2))) (.branch (.leaf (some box1)) (.leaf (none))))
def subdivision : CoverReplayTree := (.split 0 (.leaf 0) (.split 1 (.leaf 1) (.leaf 2)))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 0)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 0)) (CoverGeometry.nonapexVertex 0) q)) :=
  ⟨⟨(fun _ hq _ => positive0 hq),(fun _ hq _ => positive2 hq)⟩,⟨(fun _ hq _ => positive1 hq),True.intro⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 0)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 0)) (CoverGeometry.nonapexVertex 0) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00000

end SparseLowerTail.Section05.CoverJobReplay.Job00Smoke

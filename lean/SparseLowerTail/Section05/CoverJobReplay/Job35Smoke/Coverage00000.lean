import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job35Smoke.Leaves00000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job35Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00000
def initialBox : LogBox := ⟨![(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4629/16384 : ℚ),(4629/16384 : ℚ),(4629/16384 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.leaf (some box0)) (.leaf (some box2))) (.branch (.leaf (some box1)) (.leaf (some box3))))
def subdivision : CoverReplayTree := (.split 0 (.leaf 0) (.split 1 (.leaf 1) (.split 2 (.leaf 2) (.leaf 3))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 35)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 35)) (CoverGeometry.nonapexVertex 35) q)) :=
  ⟨⟨(fun _ hq _ => positive0 hq),(fun _ hq _ => positive2 hq)⟩,⟨(fun _ hq _ => positive1 hq),(fun _ hq _ => positive3 hq)⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 35)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 35)) (CoverGeometry.nonapexVertex 35) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00000

end SparseLowerTail.Section05.CoverJobReplay.Job35Smoke

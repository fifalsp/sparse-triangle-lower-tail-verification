import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00016
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00017

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00014
def initialBox : LogBox := ⟨![(1607/1024 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box261)) (.leaf (some box269))) (.branch (.leaf (some box265)) (.leaf (some box273)))) (.branch (.branch (.leaf (some box263)) (.leaf (some box271))) (.branch (.leaf (some box267)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box262)) (.leaf (some box270))) (.branch (.leaf (some box266)) (.leaf (some box274)))) (.branch (.branch (.leaf (some box264)) (.leaf (some box272))) (.branch (.leaf (some box268)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 2 (.split 0 (.leaf 0) (.leaf 1)) (.split 0 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.split 2 (.leaf 6) (.leaf 7)))) (.split 0 (.split 2 (.leaf 8) (.leaf 9)) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.split 2 (.leaf 12) (.leaf 13)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive261 hq),(fun _ hq _ => positive269 hq)⟩,⟨(fun _ hq _ => positive265 hq),(fun _ hq _ => positive273 hq)⟩⟩,⟨⟨(fun _ hq _ => positive263 hq),(fun _ hq _ => positive271 hq)⟩,⟨(fun _ hq _ => positive267 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive262 hq),(fun _ hq _ => positive270 hq)⟩,⟨(fun _ hq _ => positive266 hq),(fun _ hq _ => positive274 hq)⟩⟩,⟨⟨(fun _ hq _ => positive264 hq),(fun _ hq _ => positive272 hq)⟩,⟨(fun _ hq _ => positive268 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00014

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

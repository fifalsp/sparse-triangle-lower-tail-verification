import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00006
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00007

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00005
def initialBox : LogBox := ⟨![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box100)) (.leaf (some box108))) (.branch (.leaf (some box104)) (.leaf (some box112)))) (.branch (.branch (.leaf (some box102)) (.leaf (some box110))) (.branch (.leaf (some box106)) (.leaf (some box114))))) (.branch (.branch (.branch (.leaf (some box101)) (.leaf (some box109))) (.branch (.leaf (some box105)) (.leaf (some box113)))) (.branch (.branch (.leaf (some box103)) (.leaf (some box111))) (.branch (.leaf (some box107)) (.leaf (some box115))))))
def subdivision : CoverReplayTree := (.split 0 (.split 0 (.split 0 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.split 2 (.leaf 3) (.leaf 4)))) (.split 1 (.split 0 (.split 1 (.leaf 5) (.split 2 (.leaf 6) (.leaf 7))) (.split 1 (.leaf 8) (.leaf 9))) (.split 2 (.split 0 (.split 2 (.leaf 10) (.leaf 11)) (.split 1 (.leaf 12) (.leaf 13))) (.split 0 (.leaf 14) (.leaf 15)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive100 hq),(fun _ hq _ => positive108 hq)⟩,⟨(fun _ hq _ => positive104 hq),(fun _ hq _ => positive112 hq)⟩⟩,⟨⟨(fun _ hq _ => positive102 hq),(fun _ hq _ => positive110 hq)⟩,⟨(fun _ hq _ => positive106 hq),(fun _ hq _ => positive114 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive101 hq),(fun _ hq _ => positive109 hq)⟩,⟨(fun _ hq _ => positive105 hq),(fun _ hq _ => positive113 hq)⟩⟩,⟨⟨(fun _ hq _ => positive103 hq),(fun _ hq _ => positive111 hq)⟩,⟨(fun _ hq _ => positive107 hq),(fun _ hq _ => positive115 hq)⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00005

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00051
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00052

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00037
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box823)) (.leaf (some box831))) (.branch (.leaf (some box827)) (.leaf (none)))) (.branch (.branch (.leaf (some box825)) (.leaf (some box833))) (.branch (.leaf (some box829)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box824)) (.leaf (some box832))) (.branch (.leaf (some box828)) (.leaf (none)))) (.branch (.branch (.leaf (some box826)) (.leaf (some box834))) (.branch (.leaf (some box830)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 2 (.leaf 0) (.leaf 1)) (.split 1 (.split 2 (.leaf 2) (.leaf 3)) (.split 2 (.leaf 4) (.leaf 5)))) (.split 0 (.split 2 (.leaf 6) (.leaf 7)) (.split 1 (.split 2 (.leaf 8) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive823 hq),(fun _ hq _ => positive831 hq)⟩,⟨(fun _ hq _ => positive827 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive825 hq),(fun _ hq _ => positive833 hq)⟩,⟨(fun _ hq _ => positive829 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive824 hq),(fun _ hq _ => positive832 hq)⟩,⟨(fun _ hq _ => positive828 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive826 hq),(fun _ hq _ => positive834 hq)⟩,⟨(fun _ hq _ => positive830 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00037

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

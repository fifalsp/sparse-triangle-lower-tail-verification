import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00042

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00031
def initialBox : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.leaf (some box676)) (.leaf (some box684))) (.branch (.leaf (some box680)) (.leaf (none)))) (.branch (.branch (.leaf (some box678)) (.leaf (none))) (.branch (.leaf (some box682)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box677)) (.leaf (some box685))) (.branch (.leaf (some box681)) (.leaf (none)))) (.branch (.branch (.leaf (some box679)) (.leaf (none))) (.branch (.leaf (some box683)) (.leaf (none))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 2 (.leaf 0) (.leaf 1)) (.split 1 (.split 2 (.leaf 2) (.leaf 3)) (.split 2 (.leaf 4) (.leaf 5)))) (.split 0 (.leaf 6) (.split 1 (.leaf 7) (.split 2 (.leaf 8) (.leaf 9)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨(fun _ hq _ => positive676 hq),(fun _ hq _ => positive684 hq)⟩,⟨(fun _ hq _ => positive680 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive678 hq),True.intro⟩,⟨(fun _ hq _ => positive682 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive677 hq),(fun _ hq _ => positive685 hq)⟩,⟨(fun _ hq _ => positive681 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive679 hq),True.intro⟩,⟨(fun _ hq _ => positive683 hq),True.intro⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00031

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

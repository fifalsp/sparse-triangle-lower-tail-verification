import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00055
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00056

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00040
def initialBox : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box882)) (.leaf (some box898))) (.branch (.leaf (some box890)) (.leaf (none)))) (.branch (.branch (.leaf (some box886)) (.leaf (none))) (.branch (.leaf (some box894)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box884)) (.leaf (some box900))) (.branch (.leaf (some box892)) (.leaf (none)))) (.branch (.branch (.leaf (some box888)) (.leaf (none))) (.branch (.leaf (some box896)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box883)) (.leaf (some box899))) (.branch (.leaf (some box891)) (.leaf (none)))) (.branch (.branch (.leaf (some box887)) (.leaf (none))) (.branch (.leaf (some box895)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box885)) (.leaf (some box901))) (.branch (.leaf (some box893)) (.leaf (none)))) (.branch (.branch (.leaf (some box889)) (.leaf (none))) (.branch (.leaf (some box897)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 0 (.leaf 0) (.split 1 (.leaf 1) (.split 2 (.leaf 2) (.leaf 3)))) (.split 1 (.split 0 (.split 1 (.leaf 4) (.split 2 (.leaf 5) (.leaf 6))) (.split 1 (.leaf 7) (.split 2 (.leaf 8) (.leaf 9)))) (.split 2 (.split 0 (.split 2 (.leaf 10) (.leaf 11)) (.split 1 (.split 2 (.leaf 12) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15)))) (.split 0 (.leaf 16) (.split 1 (.leaf 17) (.split 2 (.leaf 18) (.leaf 19)))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive882 hq),(fun _ hq _ => positive898 hq)⟩,⟨(fun _ hq _ => positive890 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive886 hq),True.intro⟩,⟨(fun _ hq _ => positive894 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive884 hq),(fun _ hq _ => positive900 hq)⟩,⟨(fun _ hq _ => positive892 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive888 hq),True.intro⟩,⟨(fun _ hq _ => positive896 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive883 hq),(fun _ hq _ => positive899 hq)⟩,⟨(fun _ hq _ => positive891 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive887 hq),True.intro⟩,⟨(fun _ hq _ => positive895 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive885 hq),(fun _ hq _ => positive901 hq)⟩,⟨(fun _ hq _ => positive893 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive889 hq),True.intro⟩,⟨(fun _ hq _ => positive897 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00040

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

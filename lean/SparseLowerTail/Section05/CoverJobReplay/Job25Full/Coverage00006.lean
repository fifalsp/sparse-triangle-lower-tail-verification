import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00007
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00008

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00006
def initialBox : LogBox := ⟨![(1607/1024 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box116)) (.leaf (some box132))) (.branch (.leaf (some box124)) (.leaf (none)))) (.branch (.branch (.leaf (some box120)) (.leaf (none))) (.branch (.leaf (some box128)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box118)) (.leaf (some box134))) (.branch (.leaf (some box126)) (.leaf (none)))) (.branch (.branch (.leaf (some box122)) (.leaf (none))) (.branch (.leaf (some box130)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box117)) (.leaf (some box133))) (.branch (.leaf (some box125)) (.leaf (none)))) (.branch (.branch (.leaf (some box121)) (.leaf (none))) (.branch (.leaf (some box129)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box119)) (.leaf (some box135))) (.branch (.leaf (some box127)) (.leaf (none)))) (.branch (.branch (.leaf (some box123)) (.leaf (none))) (.branch (.leaf (some box131)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 0 (.split 1 (.leaf 0) (.split 2 (.leaf 1) (.leaf 2))) (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.split 2 (.leaf 12) (.leaf 13)))) (.split 0 (.split 1 (.leaf 14) (.split 2 (.leaf 15) (.leaf 16))) (.split 1 (.leaf 17) (.split 2 (.leaf 18) (.leaf 19))))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive116 hq),(fun _ hq _ => positive132 hq)⟩,⟨(fun _ hq _ => positive124 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive120 hq),True.intro⟩,⟨(fun _ hq _ => positive128 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive118 hq),(fun _ hq _ => positive134 hq)⟩,⟨(fun _ hq _ => positive126 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive122 hq),True.intro⟩,⟨(fun _ hq _ => positive130 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive117 hq),(fun _ hq _ => positive133 hq)⟩,⟨(fun _ hq _ => positive125 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive121 hq),True.intro⟩,⟨(fun _ hq _ => positive129 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive119 hq),(fun _ hq _ => positive135 hq)⟩,⟨(fun _ hq _ => positive127 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive123 hq),True.intro⟩,⟨(fun _ hq _ => positive131 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00006

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

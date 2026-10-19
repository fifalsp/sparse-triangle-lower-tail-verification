import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00056
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00057
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00058

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00041
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box902)) (.leaf (some box918))) (.branch (.leaf (some box910)) (.leaf (some box926)))) (.branch (.branch (.leaf (some box906)) (.leaf (some box922))) (.branch (.leaf (some box914)) (.leaf (some box930))))) (.branch (.branch (.branch (.leaf (some box904)) (.leaf (some box920))) (.branch (.leaf (some box912)) (.leaf (some box928)))) (.branch (.branch (.leaf (some box908)) (.leaf (some box924))) (.branch (.leaf (some box916)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box903)) (.leaf (some box919))) (.branch (.leaf (some box911)) (.leaf (some box927)))) (.branch (.branch (.leaf (some box907)) (.leaf (some box923))) (.branch (.leaf (some box915)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box905)) (.leaf (some box921))) (.branch (.leaf (some box913)) (.leaf (some box929)))) (.branch (.branch (.leaf (some box909)) (.leaf (some box925))) (.branch (.leaf (some box917)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.split 2 (.leaf 1) (.leaf 2))) (.split 1 (.leaf 3) (.split 2 (.leaf 4) (.leaf 5)))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.split 2 (.leaf 12) (.leaf 13)))) (.split 0 (.split 1 (.leaf 14) (.split 2 (.leaf 15) (.leaf 16))) (.split 1 (.leaf 17) (.leaf 18))))) (.split 1 (.split 0 (.split 1 (.leaf 19) (.leaf 20)) (.split 1 (.leaf 21) (.leaf 22))) (.split 2 (.split 0 (.split 1 (.leaf 23) (.leaf 24)) (.leaf 25)) (.split 0 (.split 1 (.leaf 26) (.leaf 27)) (.leaf 28)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive902 hq),(fun _ hq _ => positive918 hq)⟩,⟨(fun _ hq _ => positive910 hq),(fun _ hq _ => positive926 hq)⟩⟩,⟨⟨(fun _ hq _ => positive906 hq),(fun _ hq _ => positive922 hq)⟩,⟨(fun _ hq _ => positive914 hq),(fun _ hq _ => positive930 hq)⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive904 hq),(fun _ hq _ => positive920 hq)⟩,⟨(fun _ hq _ => positive912 hq),(fun _ hq _ => positive928 hq)⟩⟩,⟨⟨(fun _ hq _ => positive908 hq),(fun _ hq _ => positive924 hq)⟩,⟨(fun _ hq _ => positive916 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive903 hq),(fun _ hq _ => positive919 hq)⟩,⟨(fun _ hq _ => positive911 hq),(fun _ hq _ => positive927 hq)⟩⟩,⟨⟨(fun _ hq _ => positive907 hq),(fun _ hq _ => positive923 hq)⟩,⟨(fun _ hq _ => positive915 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive905 hq),(fun _ hq _ => positive921 hq)⟩,⟨(fun _ hq _ => positive913 hq),(fun _ hq _ => positive929 hq)⟩⟩,⟨⟨(fun _ hq _ => positive909 hq),(fun _ hq _ => positive925 hq)⟩,⟨(fun _ hq _ => positive917 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00041

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

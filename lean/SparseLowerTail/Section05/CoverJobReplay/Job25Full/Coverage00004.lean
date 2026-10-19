import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00004
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00005
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00006

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00004
def initialBox : LogBox := ⟨![(4821/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box77)) (.leaf (some box93))) (.branch (.leaf (some box85)) (.leaf (none)))) (.branch (.branch (.leaf (some box81)) (.leaf (some box97))) (.branch (.leaf (some box89)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box79)) (.leaf (some box95))) (.branch (.leaf (some box87)) (.leaf (none)))) (.branch (.branch (.leaf (some box83)) (.leaf (some box99))) (.branch (.leaf (some box91)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box78)) (.leaf (some box94))) (.branch (.leaf (some box86)) (.leaf (none)))) (.branch (.branch (.leaf (some box82)) (.leaf (some box98))) (.branch (.leaf (some box90)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box80)) (.leaf (some box96))) (.branch (.leaf (some box88)) (.leaf (none)))) (.branch (.branch (.leaf (some box84)) (.leaf (none))) (.branch (.leaf (some box92)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.split 2 (.leaf 2) (.leaf 3))) (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.leaf 6))) (.split 0 (.split 1 (.split 2 (.leaf 7) (.leaf 8)) (.split 2 (.leaf 9) (.leaf 10))) (.split 1 (.split 2 (.leaf 11) (.leaf 12)) (.split 2 (.leaf 13) (.leaf 14))))) (.split 2 (.split 0 (.leaf 15) (.split 1 (.leaf 16) (.leaf 17))) (.split 0 (.split 2 (.leaf 18) (.leaf 19)) (.split 1 (.split 2 (.leaf 20) (.leaf 21)) (.leaf 22)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive77 hq),(fun _ hq _ => positive93 hq)⟩,⟨(fun _ hq _ => positive85 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive81 hq),(fun _ hq _ => positive97 hq)⟩,⟨(fun _ hq _ => positive89 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive79 hq),(fun _ hq _ => positive95 hq)⟩,⟨(fun _ hq _ => positive87 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive83 hq),(fun _ hq _ => positive99 hq)⟩,⟨(fun _ hq _ => positive91 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive78 hq),(fun _ hq _ => positive94 hq)⟩,⟨(fun _ hq _ => positive86 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive82 hq),(fun _ hq _ => positive98 hq)⟩,⟨(fun _ hq _ => positive90 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive80 hq),(fun _ hq _ => positive96 hq)⟩,⟨(fun _ hq _ => positive88 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive84 hq),True.intro⟩,⟨(fun _ hq _ => positive92 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00004

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

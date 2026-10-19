import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00009
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00010

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00008
def initialBox : LogBox := ⟨![(1607/1024 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box154)) (.leaf (some box170))) (.branch (.leaf (some box162)) (.leaf (none)))) (.branch (.branch (.leaf (some box158)) (.leaf (some box174))) (.branch (.leaf (some box166)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box156)) (.leaf (some box172))) (.branch (.leaf (some box164)) (.leaf (none)))) (.branch (.branch (.leaf (some box160)) (.leaf (none))) (.branch (.leaf (some box168)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box155)) (.leaf (some box171))) (.branch (.leaf (some box163)) (.leaf (none)))) (.branch (.branch (.leaf (some box159)) (.leaf (none))) (.branch (.leaf (some box167)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box157)) (.leaf (some box173))) (.branch (.leaf (some box165)) (.leaf (none)))) (.branch (.branch (.leaf (some box161)) (.leaf (none))) (.branch (.leaf (some box169)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 1 (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 0) (.leaf 1)) (.leaf 2)) (.split 1 (.split 2 (.leaf 3) (.leaf 4)) (.leaf 5))) (.split 0 (.split 1 (.split 2 (.leaf 6) (.leaf 7)) (.split 2 (.leaf 8) (.leaf 9))) (.split 1 (.split 2 (.leaf 10) (.leaf 11)) (.leaf 12)))) (.split 2 (.split 0 (.split 1 (.leaf 13) (.leaf 14)) (.split 1 (.leaf 15) (.leaf 16))) (.split 0 (.split 1 (.leaf 17) (.leaf 18)) (.split 1 (.leaf 19) (.leaf 20)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive154 hq),(fun _ hq _ => positive170 hq)⟩,⟨(fun _ hq _ => positive162 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive158 hq),(fun _ hq _ => positive174 hq)⟩,⟨(fun _ hq _ => positive166 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive156 hq),(fun _ hq _ => positive172 hq)⟩,⟨(fun _ hq _ => positive164 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive160 hq),True.intro⟩,⟨(fun _ hq _ => positive168 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive155 hq),(fun _ hq _ => positive171 hq)⟩,⟨(fun _ hq _ => positive163 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive159 hq),True.intro⟩,⟨(fun _ hq _ => positive167 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive157 hq),(fun _ hq _ => positive173 hq)⟩,⟨(fun _ hq _ => positive165 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive161 hq),True.intro⟩,⟨(fun _ hq _ => positive169 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00008

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00021
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00022

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00018
def initialBox : LogBox := ⟨![(1607/512 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box339)) (.leaf (some box355))) (.branch (.leaf (some box347)) (.leaf (none)))) (.branch (.branch (.leaf (some box343)) (.leaf (some box359))) (.branch (.leaf (some box351)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box341)) (.leaf (some box357))) (.branch (.leaf (some box349)) (.leaf (none)))) (.branch (.branch (.leaf (some box345)) (.leaf (none))) (.branch (.leaf (some box353)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box340)) (.leaf (some box356))) (.branch (.leaf (some box348)) (.leaf (none)))) (.branch (.branch (.leaf (some box344)) (.leaf (none))) (.branch (.leaf (some box352)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box342)) (.leaf (some box358))) (.branch (.leaf (some box350)) (.leaf (none)))) (.branch (.branch (.leaf (some box346)) (.leaf (none))) (.branch (.leaf (some box354)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 0 (.leaf 4) (.leaf 5))) (.split 2 (.leaf 6) (.leaf 7))) (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 8) (.leaf 9)) (.split 1 (.leaf 10) (.leaf 11))) (.leaf 12)) (.split 2 (.leaf 13) (.leaf 14)))) (.split 0 (.split 1 (.leaf 15) (.split 2 (.leaf 16) (.leaf 17))) (.split 1 (.leaf 18) (.split 2 (.leaf 19) (.leaf 20)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive339 hq),(fun _ hq _ => positive355 hq)⟩,⟨(fun _ hq _ => positive347 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive343 hq),(fun _ hq _ => positive359 hq)⟩,⟨(fun _ hq _ => positive351 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive341 hq),(fun _ hq _ => positive357 hq)⟩,⟨(fun _ hq _ => positive349 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive345 hq),True.intro⟩,⟨(fun _ hq _ => positive353 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive340 hq),(fun _ hq _ => positive356 hq)⟩,⟨(fun _ hq _ => positive348 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive344 hq),True.intro⟩,⟨(fun _ hq _ => positive352 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive342 hq),(fun _ hq _ => positive358 hq)⟩,⟨(fun _ hq _ => positive350 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive346 hq),True.intro⟩,⟨(fun _ hq _ => positive354 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00018

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

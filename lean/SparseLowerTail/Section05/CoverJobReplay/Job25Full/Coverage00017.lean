import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00019
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00020
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00021

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00017
def initialBox : LogBox := ⟨![(1607/512 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box316)) (.leaf (some box332))) (.branch (.leaf (some box324)) (.leaf (none)))) (.branch (.branch (.leaf (some box320)) (.leaf (some box336))) (.branch (.leaf (some box328)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box318)) (.leaf (some box334))) (.branch (.leaf (some box326)) (.leaf (none)))) (.branch (.branch (.leaf (some box322)) (.leaf (some box338))) (.branch (.leaf (some box330)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box317)) (.leaf (some box333))) (.branch (.leaf (some box325)) (.leaf (none)))) (.branch (.branch (.leaf (some box321)) (.leaf (some box337))) (.branch (.leaf (some box329)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box319)) (.leaf (some box335))) (.branch (.leaf (some box327)) (.leaf (none)))) (.branch (.branch (.leaf (some box323)) (.leaf (none))) (.branch (.leaf (some box331)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 0 (.split 1 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.split 2 (.split 0 (.split 1 (.split 2 (.leaf 4) (.leaf 5)) (.leaf 6)) (.split 1 (.split 2 (.leaf 7) (.leaf 8)) (.leaf 9))) (.split 0 (.split 1 (.leaf 10) (.leaf 11)) (.leaf 12)))) (.split 1 (.split 0 (.split 1 (.leaf 13) (.leaf 14)) (.split 1 (.leaf 15) (.leaf 16))) (.split 2 (.split 0 (.split 1 (.leaf 17) (.leaf 18)) (.split 1 (.leaf 19) (.leaf 20))) (.split 0 (.leaf 21) (.leaf 22)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive316 hq),(fun _ hq _ => positive332 hq)⟩,⟨(fun _ hq _ => positive324 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive320 hq),(fun _ hq _ => positive336 hq)⟩,⟨(fun _ hq _ => positive328 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive318 hq),(fun _ hq _ => positive334 hq)⟩,⟨(fun _ hq _ => positive326 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive322 hq),(fun _ hq _ => positive338 hq)⟩,⟨(fun _ hq _ => positive330 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive317 hq),(fun _ hq _ => positive333 hq)⟩,⟨(fun _ hq _ => positive325 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive321 hq),(fun _ hq _ => positive337 hq)⟩,⟨(fun _ hq _ => positive329 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive319 hq),(fun _ hq _ => positive335 hq)⟩,⟨(fun _ hq _ => positive327 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive323 hq),True.intro⟩,⟨(fun _ hq _ => positive331 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00017

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

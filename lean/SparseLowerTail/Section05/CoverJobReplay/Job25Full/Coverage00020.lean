import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00023
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00024

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00020
def initialBox : LogBox := ⟨![(8035/2048 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box378)) (.leaf (some box394))) (.branch (.leaf (some box386)) (.leaf (none)))) (.branch (.branch (.leaf (some box382)) (.leaf (none))) (.branch (.leaf (some box390)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box380)) (.leaf (none))) (.branch (.leaf (some box388)) (.leaf (none)))) (.branch (.branch (.leaf (some box384)) (.leaf (none))) (.branch (.leaf (some box392)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box379)) (.leaf (some box395))) (.branch (.leaf (some box387)) (.leaf (none)))) (.branch (.branch (.leaf (some box383)) (.leaf (none))) (.branch (.leaf (some box391)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box381)) (.leaf (none))) (.branch (.leaf (some box389)) (.leaf (none)))) (.branch (.branch (.leaf (some box385)) (.leaf (none))) (.branch (.leaf (some box393)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 0) (.leaf 1)) (.split 1 (.leaf 2) (.leaf 3))) (.leaf 4)) (.split 2 (.leaf 5) (.leaf 6))) (.split 1 (.split 2 (.split 0 (.leaf 7) (.leaf 8)) (.leaf 9)) (.split 2 (.leaf 10) (.leaf 11)))) (.split 0 (.split 1 (.leaf 12) (.split 2 (.leaf 13) (.leaf 14))) (.split 1 (.leaf 15) (.split 2 (.leaf 16) (.leaf 17)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive378 hq),(fun _ hq _ => positive394 hq)⟩,⟨(fun _ hq _ => positive386 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive382 hq),True.intro⟩,⟨(fun _ hq _ => positive390 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive380 hq),True.intro⟩,⟨(fun _ hq _ => positive388 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive384 hq),True.intro⟩,⟨(fun _ hq _ => positive392 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive379 hq),(fun _ hq _ => positive395 hq)⟩,⟨(fun _ hq _ => positive387 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive383 hq),True.intro⟩,⟨(fun _ hq _ => positive391 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive381 hq),True.intro⟩,⟨(fun _ hq _ => positive389 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive385 hq),True.intro⟩,⟨(fun _ hq _ => positive393 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00020

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

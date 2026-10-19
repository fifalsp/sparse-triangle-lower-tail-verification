import SparseLowerTail.Section05.CoverReplayTable
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00058
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Leaves00059

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage00042
def initialBox : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/256 : ℚ)]⟩
def leafTable : RegisterTree (Option LogBox) := (.branch (.branch (.branch (.branch (.branch (.leaf (some box931)) (.leaf (some box947))) (.branch (.leaf (some box939)) (.leaf (none)))) (.branch (.branch (.leaf (some box935)) (.leaf (some box951))) (.branch (.leaf (some box943)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box933)) (.leaf (some box949))) (.branch (.leaf (some box941)) (.leaf (none)))) (.branch (.branch (.leaf (some box937)) (.leaf (none))) (.branch (.leaf (some box945)) (.leaf (none)))))) (.branch (.branch (.branch (.branch (.leaf (some box932)) (.leaf (some box948))) (.branch (.leaf (some box940)) (.leaf (none)))) (.branch (.branch (.leaf (some box936)) (.leaf (none))) (.branch (.leaf (some box944)) (.leaf (none))))) (.branch (.branch (.branch (.leaf (some box934)) (.leaf (some box950))) (.branch (.leaf (some box942)) (.leaf (none)))) (.branch (.branch (.leaf (some box938)) (.leaf (none))) (.branch (.leaf (some box946)) (.leaf (none)))))))
def subdivision : CoverReplayTree := (.split 2 (.split 0 (.split 2 (.split 0 (.split 2 (.leaf 0) (.leaf 1)) (.split 1 (.split 2 (.leaf 2) (.leaf 3)) (.split 2 (.leaf 4) (.leaf 5)))) (.split 0 (.split 2 (.leaf 6) (.leaf 7)) (.split 1 (.leaf 8) (.leaf 9)))) (.split 1 (.split 2 (.split 0 (.split 1 (.leaf 10) (.leaf 11)) (.leaf 12)) (.leaf 13)) (.split 2 (.leaf 14) (.leaf 15)))) (.split 0 (.split 0 (.leaf 16) (.leaf 17)) (.split 1 (.leaf 18) (.split 2 (.leaf 19) (.leaf 20)))))
theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel
theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q)) :=
  ⟨⟨⟨⟨⟨(fun _ hq _ => positive931 hq),(fun _ hq _ => positive947 hq)⟩,⟨(fun _ hq _ => positive939 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive935 hq),(fun _ hq _ => positive951 hq)⟩,⟨(fun _ hq _ => positive943 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive933 hq),(fun _ hq _ => positive949 hq)⟩,⟨(fun _ hq _ => positive941 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive937 hq),True.intro⟩,⟨(fun _ hq _ => positive945 hq),True.intro⟩⟩⟩⟩,⟨⟨⟨⟨(fun _ hq _ => positive932 hq),(fun _ hq _ => positive948 hq)⟩,⟨(fun _ hq _ => positive940 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive936 hq),True.intro⟩,⟨(fun _ hq _ => positive944 hq),True.intro⟩⟩⟩,⟨⟨⟨(fun _ hq _ => positive934 hq),(fun _ hq _ => positive950 hq)⟩,⟨(fun _ hq _ => positive942 hq),True.intro⟩⟩,⟨⟨(fun _ hq _ => positive938 hq),True.intro⟩,⟨(fun _ hq _ => positive946 hq),True.intro⟩⟩⟩⟩⟩
theorem covered {Q : ℝ} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → 0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage00042

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

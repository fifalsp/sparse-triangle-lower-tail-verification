import SparseLowerTail.Section05.ApexReplay.F1Smoke.Endpoints0000
import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.ApexRefinedTaylorBox
import SparseLowerTail.Section05.ApexReplay.F1Smoke.Boxes057

/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace SparseLowerTail.Section05.ApexReplay.F1Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def data14732 : S1TaylorBoxData := ⟨box14732,![exp14,exp6,exp3],![exp16,exp8,exp5],![exp15,exp7,exp4]⟩
theorem data14732_lower_valid : ∀ j, (data14732.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp3_valid
theorem data14732_upper_valid : ∀ j, (data14732.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp8_valid
  · exact exp5_valid
theorem data14732_center_valid : ∀ j, (data14732.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp15_valid
  · exact exp7_valid
  · exact exp4_valid
theorem margin14732 : 0 < data14732.apexRefinedMargin 0 := by decide +kernel
theorem conclusion14732 {q : EdgeTriple} (hq : q ∈ box14732.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data14732.apexRefined_positive 0
    data14732_lower_valid data14732_upper_valid data14732_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin14732 hq

theorem conclusion14733 {q : EdgeTriple} (hq : q ∈ box14733.region) :
    ApexLeafConclusion 0 q :=
  box14733.apexLeafConclusion_of_contact (mixed := true)
    (by decide +kernel) hq

end SparseLowerTail.Section05.ApexReplay.F1Smoke

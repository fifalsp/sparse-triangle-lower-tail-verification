import SparseLowerTail.Section05.ApexReplay.F1Smoke.Endpoints0000
import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.ApexRefinedTaylorBox
import SparseLowerTail.Section05.ApexReplay.F1Smoke.Boxes119

/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace SparseLowerTail.Section05.ApexReplay.F1Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def data30518 : S1TaylorBoxData := ⟨box30518,![exp11,exp11,exp9],![exp13,exp13,exp11],![exp12,exp12,exp10]⟩
theorem data30518_lower_valid : ∀ j, (data30518.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp11_valid
  · exact exp11_valid
  · exact exp9_valid
theorem data30518_upper_valid : ∀ j, (data30518.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp13_valid
  · exact exp13_valid
  · exact exp11_valid
theorem data30518_center_valid : ∀ j, (data30518.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp12_valid
  · exact exp10_valid
theorem margin30518 : 0 < data30518.apexRefinedMargin 0 := by decide +kernel
theorem conclusion30518 {q : EdgeTriple} (hq : q ∈ box30518.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data30518.apexRefined_positive 0
    data30518_lower_valid data30518_upper_valid data30518_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin30518 hq

theorem conclusion30519 {q : EdgeTriple} (hq : q ∈ box30519.region) :
    ApexLeafConclusion 0 q :=
  box30519.apexLeafConclusion_of_contact (mixed := false)
    (by decide +kernel) hq

end SparseLowerTail.Section05.ApexReplay.F1Smoke

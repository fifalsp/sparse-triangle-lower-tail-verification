import SparseLowerTail.Section05.ApexReplay.F1Smoke.Endpoints0000
import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.ApexRefinedTaylorBox
import SparseLowerTail.Section05.ApexReplay.F1Smoke.Boxes000

/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace SparseLowerTail.Section05.ApexReplay.F1Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def data0 : S1TaylorBoxData := ⟨box0,![exp0,exp0,exp0],![exp2,exp2,exp2],![exp1,exp1,exp1]⟩
theorem data0_lower_valid : ∀ j, (data0.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp0_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data0_upper_valid : ∀ j, (data0.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp2_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data0_center_valid : ∀ j, (data0.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin0 : 0 < data0.apexRefinedMargin 0 := by decide +kernel
theorem conclusion0 {q : EdgeTriple} (hq : q ∈ box0.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data0.apexRefined_positive 0
    data0_lower_valid data0_upper_valid data0_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin0 hq

end SparseLowerTail.Section05.ApexReplay.F1Smoke

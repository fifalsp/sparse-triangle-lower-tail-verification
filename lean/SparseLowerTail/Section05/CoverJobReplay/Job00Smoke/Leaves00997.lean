import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job00Smoke.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job00Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box15962 : LogBox := ⟨![(23009/4096 : ℚ),(23009/4096 : ℚ),(23009/4096 : ℚ)],![(3287/512 : ℚ),(3287/512 : ℚ),(3287/512 : ℚ)]⟩
def data15962 : S1TaylorBoxData := ⟨box15962,![exp5,exp5,exp5],![exp7,exp7,exp7],![exp6,exp6,exp6]⟩
theorem data15962_lower_valid : ∀ j, (data15962.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp5_valid
  · exact exp5_valid
  · exact exp5_valid
theorem data15962_upper_valid : ∀ j, (data15962.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp7_valid
  · exact exp7_valid
  · exact exp7_valid
theorem data15962_center_valid : ∀ j, (data15962.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin15962 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data15962 0 := by decide +kernel
theorem positive15962 {q : EdgeTriple} (hq : q ∈ box15962.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 0)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 0)) (CoverGeometry.nonapexVertex 0) q :=
  RefinedCover.S1TaylorBoxData.job_positive data15962 0
    data15962_lower_valid data15962_upper_valid data15962_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin15962 hq

end SparseLowerTail.Section05.CoverJobReplay.Job00Smoke

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job35Smoke.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job35Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box12466 : LogBox := ⟨![(23145/4096 : ℚ),(4629/1024 : ℚ),(4629/1024 : ℚ)],![(13887/2048 : ℚ),(23145/4096 : ℚ),(23145/4096 : ℚ)]⟩
def data12466 : S1TaylorBoxData := ⟨box12466,![exp7,exp5,exp5],![exp9,exp7,exp7],![exp8,exp6,exp6]⟩
theorem data12466_lower_valid : ∀ j, (data12466.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp7_valid
  · exact exp5_valid
  · exact exp5_valid
theorem data12466_upper_valid : ∀ j, (data12466.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp9_valid
  · exact exp7_valid
  · exact exp7_valid
theorem data12466_center_valid : ∀ j, (data12466.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin12466 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data12466) 35)).lower := by
  decide +kernel
theorem positive12466 {q : EdgeTriple} (hq : q ∈ box12466.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 35)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 35)) (CoverGeometry.nonapexVertex 35) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data12466)
    ⟨data12466_lower_valid,data12466_upper_valid⟩ 35 margin12466 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

end SparseLowerTail.Section05.CoverJobReplay.Job35Smoke

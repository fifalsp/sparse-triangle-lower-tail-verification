import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job35Smoke.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job35Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box28521 : LogBox := ⟨![(4629/512 : ℚ),(4629/512 : ℚ),(4629/512 : ℚ)],![(4629/256 : ℚ),(4629/256 : ℚ),(4629/256 : ℚ)]⟩
def data28521 : S1TaylorBoxData := ⟨box28521,![exp10,exp10,exp10],![exp12,exp12,exp12],![exp11,exp11,exp11]⟩
theorem data28521_lower_valid : ∀ j, (data28521.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data28521_upper_valid : ∀ j, (data28521.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp12_valid
  · exact exp12_valid
theorem data28521_center_valid : ∀ j, (data28521.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp11_valid
  · exact exp11_valid
  · exact exp11_valid
theorem margin28521 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data28521) 35)).lower := by
  decide +kernel
theorem positive28521 {q : EdgeTriple} (hq : q ∈ box28521.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 35)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 35)) (CoverGeometry.nonapexVertex 35) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data28521)
    ⟨data28521_lower_valid,data28521_upper_valid⟩ 35 margin28521 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

end SparseLowerTail.Section05.CoverJobReplay.Job35Smoke

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job00Smoke.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job00Smoke
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box0 : LogBox := ⟨![(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(3287/32768 : ℚ),(3287/32768 : ℚ),(3287/32768 : ℚ)]⟩
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
theorem margin0 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data0 0 := by decide +kernel
theorem positive0 {q : EdgeTriple} (hq : q ∈ box0.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 0)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 0)) (CoverGeometry.nonapexVertex 0) q :=
  RefinedCover.S1TaylorBoxData.job_positive data0 0
    data0_lower_valid data0_upper_valid data0_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin0 hq

def box1 : LogBox := ⟨![(3287/32768 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(3287/16384 : ℚ),(3287/32768 : ℚ),(3287/32768 : ℚ)]⟩
def data1 : S1TaylorBoxData := ⟨box1,![exp2,exp0,exp0],![exp4,exp2,exp2],![exp3,exp1,exp1]⟩
theorem data1_lower_valid : ∀ j, (data1.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp2_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data1_upper_valid : ∀ j, (data1.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data1_center_valid : ∀ j, (data1.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp3_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin1 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data1 0 := by decide +kernel
theorem positive1 {q : EdgeTriple} (hq : q ∈ box1.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 0)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 0)) (CoverGeometry.nonapexVertex 0) q :=
  RefinedCover.S1TaylorBoxData.job_positive data1 0
    data1_lower_valid data1_upper_valid data1_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin1 hq

def box2 : LogBox := ⟨![(3287/32768 : ℚ),(3287/32768 : ℚ),(0/1 : ℚ)],![(3287/16384 : ℚ),(3287/16384 : ℚ),(3287/16384 : ℚ)]⟩
def data2 : S1TaylorBoxData := ⟨box2,![exp2,exp2,exp0],![exp4,exp4,exp4],![exp3,exp3,exp2]⟩
theorem data2_lower_valid : ∀ j, (data2.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp2_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data2_upper_valid : ∀ j, (data2.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data2_center_valid : ∀ j, (data2.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp3_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin2 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data2 0 := by decide +kernel
theorem positive2 {q : EdgeTriple} (hq : q ∈ box2.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 0)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 0)) (CoverGeometry.nonapexVertex 0) q :=
  RefinedCover.S1TaylorBoxData.job_positive data2 0
    data2_lower_valid data2_upper_valid data2_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin2 hq

end SparseLowerTail.Section05.CoverJobReplay.Job00Smoke

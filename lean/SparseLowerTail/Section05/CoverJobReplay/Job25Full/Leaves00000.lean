import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box0 : LogBox := ⟨![(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
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
theorem margin0 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data0) 25)).lower := by
  decide +kernel
theorem positive0 {q : EdgeTriple} (hq : q ∈ box0.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data0)
    ⟨data0_lower_valid,data0_upper_valid⟩ 25 margin0 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box1 : LogBox := ⟨![(1607/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
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
    0 < RefinedCover.S1TaylorBoxData.jobMargin data1 25 := by decide +kernel
theorem positive1 {q : EdgeTriple} (hq : q ∈ box1.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data1 25
    data1_lower_valid data1_upper_valid data1_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin1 hq

def box2 : LogBox := ⟨![(1607/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(1607/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
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
    0 < RefinedCover.S1TaylorBoxData.jobMargin data2 25 := by decide +kernel
theorem positive2 {q : EdgeTriple} (hq : q ∈ box2.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data2 25
    data2_lower_valid data2_upper_valid data2_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin2 hq

def box3 : LogBox := ⟨![(1607/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4821/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data3 : S1TaylorBoxData := ⟨box3,![exp4,exp0,exp0],![exp6,exp2,exp2],![exp5,exp1,exp1]⟩
theorem data3_lower_valid : ∀ j, (data3.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data3_upper_valid : ∀ j, (data3.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data3_center_valid : ∀ j, (data3.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp5_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin3 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data3 25 := by decide +kernel
theorem positive3 {q : EdgeTriple} (hq : q ∈ box3.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data3 25
    data3_lower_valid data3_upper_valid data3_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin3 hq

def box4 : LogBox := ⟨![(1607/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(4821/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data4 : S1TaylorBoxData := ⟨box4,![exp4,exp2,exp0],![exp6,exp4,exp2],![exp5,exp3,exp1]⟩
theorem data4_lower_valid : ∀ j, (data4.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data4_upper_valid : ∀ j, (data4.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data4_center_valid : ∀ j, (data4.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp5_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin4 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data4 25 := by decide +kernel
theorem positive4 {q : EdgeTriple} (hq : q ∈ box4.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data4 25
    data4_lower_valid data4_upper_valid data4_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin4 hq

def box5 : LogBox := ⟨![(1607/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(4821/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data5 : S1TaylorBoxData := ⟨box5,![exp4,exp2,exp2],![exp6,exp4,exp4],![exp5,exp3,exp3]⟩
theorem data5_lower_valid : ∀ j, (data5.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data5_upper_valid : ∀ j, (data5.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data5_center_valid : ∀ j, (data5.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp5_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin5 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data5 25 := by decide +kernel
theorem positive5 {q : EdgeTriple} (hq : q ∈ box5.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data5 25
    data5_lower_valid data5_upper_valid data5_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin5 hq

def box6 : LogBox := ⟨![(4821/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/2048 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data6 : S1TaylorBoxData := ⟨box6,![exp6,exp0,exp0],![exp10,exp2,exp2],![exp8,exp1,exp1]⟩
theorem data6_lower_valid : ∀ j, (data6.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data6_upper_valid : ∀ j, (data6.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data6_center_valid : ∀ j, (data6.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin6 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data6 25 := by decide +kernel
theorem positive6 {q : EdgeTriple} (hq : q ∈ box6.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data6 25
    data6_lower_valid data6_upper_valid data6_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin6 hq

def box7 : LogBox := ⟨![(4821/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(1607/2048 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data7 : S1TaylorBoxData := ⟨box7,![exp6,exp2,exp0],![exp10,exp4,exp2],![exp8,exp3,exp1]⟩
theorem data7_lower_valid : ∀ j, (data7.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data7_upper_valid : ∀ j, (data7.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data7_center_valid : ∀ j, (data7.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin7 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data7 25 := by decide +kernel
theorem positive7 {q : EdgeTriple} (hq : q ∈ box7.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data7 25
    data7_lower_valid data7_upper_valid data7_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin7 hq

def box8 : LogBox := ⟨![(4821/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(1607/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data8 : S1TaylorBoxData := ⟨box8,![exp6,exp2,exp2],![exp10,exp4,exp4],![exp8,exp3,exp3]⟩
theorem data8_lower_valid : ∀ j, (data8.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data8_upper_valid : ∀ j, (data8.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data8_center_valid : ∀ j, (data8.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin8 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data8 25 := by decide +kernel
theorem positive8 {q : EdgeTriple} (hq : q ∈ box8.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data8 25
    data8_lower_valid data8_upper_valid data8_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin8 hq

def box9 : LogBox := ⟨![(1607/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(4821/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data9 : S1TaylorBoxData := ⟨box9,![exp4,exp4,exp0],![exp6,exp6,exp2],![exp5,exp5,exp1]⟩
theorem data9_lower_valid : ∀ j, (data9.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data9_upper_valid : ∀ j, (data9.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data9_center_valid : ∀ j, (data9.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp5_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin9 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data9 25 := by decide +kernel
theorem positive9 {q : EdgeTriple} (hq : q ∈ box9.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data9 25
    data9_lower_valid data9_upper_valid data9_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin9 hq

def box10 : LogBox := ⟨![(1607/4096 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(4821/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data10 : S1TaylorBoxData := ⟨box10,![exp4,exp4,exp2],![exp6,exp6,exp4],![exp5,exp5,exp3]⟩
theorem data10_lower_valid : ∀ j, (data10.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data10_upper_valid : ∀ j, (data10.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data10_center_valid : ∀ j, (data10.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp5_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin10 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data10 25 := by decide +kernel
theorem positive10 {q : EdgeTriple} (hq : q ∈ box10.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data10 25
    data10_lower_valid data10_upper_valid data10_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin10 hq

def box11 : LogBox := ⟨![(4821/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(1607/2048 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data11 : S1TaylorBoxData := ⟨box11,![exp6,exp4,exp0],![exp10,exp6,exp2],![exp8,exp5,exp1]⟩
theorem data11_lower_valid : ∀ j, (data11.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data11_upper_valid : ∀ j, (data11.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data11_center_valid : ∀ j, (data11.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin11 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data11 25 := by decide +kernel
theorem positive11 {q : EdgeTriple} (hq : q ∈ box11.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data11 25
    data11_lower_valid data11_upper_valid data11_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin11 hq

def box12 : LogBox := ⟨![(4821/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(1607/2048 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data12 : S1TaylorBoxData := ⟨box12,![exp6,exp4,exp2],![exp10,exp6,exp4],![exp8,exp5,exp3]⟩
theorem data12_lower_valid : ∀ j, (data12.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data12_upper_valid : ∀ j, (data12.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data12_center_valid : ∀ j, (data12.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin12 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data12 25 := by decide +kernel
theorem positive12 {q : EdgeTriple} (hq : q ∈ box12.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data12 25
    data12_lower_valid data12_upper_valid data12_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin12 hq

def box13 : LogBox := ⟨![(4821/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data13 : S1TaylorBoxData := ⟨box13,![exp6,exp6,exp0],![exp10,exp10,exp2],![exp8,exp8,exp1]⟩
theorem data13_lower_valid : ∀ j, (data13.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data13_upper_valid : ∀ j, (data13.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data13_center_valid : ∀ j, (data13.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin13 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data13 25 := by decide +kernel
theorem positive13 {q : EdgeTriple} (hq : q ∈ box13.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data13 25
    data13_lower_valid data13_upper_valid data13_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin13 hq

def box14 : LogBox := ⟨![(4821/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data14 : S1TaylorBoxData := ⟨box14,![exp6,exp6,exp2],![exp10,exp10,exp4],![exp8,exp8,exp3]⟩
theorem data14_lower_valid : ∀ j, (data14.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data14_upper_valid : ∀ j, (data14.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data14_center_valid : ∀ j, (data14.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin14 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data14 25 := by decide +kernel
theorem positive14 {q : EdgeTriple} (hq : q ∈ box14.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data14 25
    data14_lower_valid data14_upper_valid data14_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin14 hq

def box15 : LogBox := ⟨![(1607/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(4821/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data15 : S1TaylorBoxData := ⟨box15,![exp4,exp4,exp4],![exp6,exp6,exp6],![exp5,exp5,exp5]⟩
theorem data15_lower_valid : ∀ j, (data15.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp4_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data15_upper_valid : ∀ j, (data15.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data15_center_valid : ∀ j, (data15.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp5_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin15 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data15 25 := by decide +kernel
theorem positive15 {q : EdgeTriple} (hq : q ∈ box15.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data15 25
    data15_lower_valid data15_upper_valid data15_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin15 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

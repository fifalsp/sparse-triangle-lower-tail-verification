import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box16 : LogBox := ⟨![(4821/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(1607/2048 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data16 : S1TaylorBoxData := ⟨box16,![exp6,exp4,exp4],![exp10,exp6,exp6],![exp8,exp5,exp5]⟩
theorem data16_lower_valid : ∀ j, (data16.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data16_upper_valid : ∀ j, (data16.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data16_center_valid : ∀ j, (data16.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin16 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data16 25 := by decide +kernel
theorem positive16 {q : EdgeTriple} (hq : q ∈ box16.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data16 25
    data16_lower_valid data16_upper_valid data16_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16 hq

def box17 : LogBox := ⟨![(4821/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(1607/2048 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)]⟩
def data17 : S1TaylorBoxData := ⟨box17,![exp6,exp6,exp4],![exp10,exp10,exp6],![exp8,exp8,exp5]⟩
theorem data17_lower_valid : ∀ j, (data17.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data17_upper_valid : ∀ j, (data17.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data17_center_valid : ∀ j, (data17.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp8_valid
  · exact exp5_valid
theorem margin17 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data17 25 := by decide +kernel
theorem positive17 {q : EdgeTriple} (hq : q ∈ box17.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data17 25
    data17_lower_valid data17_upper_valid data17_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin17 hq

def box18 : LogBox := ⟨![(4821/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(11249/16384 : ℚ),(11249/16384 : ℚ),(11249/16384 : ℚ)]⟩
def data18 : S1TaylorBoxData := ⟨box18,![exp6,exp6,exp6],![exp8,exp8,exp8],![exp7,exp7,exp7]⟩
theorem data18_lower_valid : ∀ j, (data18.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp6_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data18_upper_valid : ∀ j, (data18.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp8_valid
  · exact exp8_valid
theorem data18_center_valid : ∀ j, (data18.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp7_valid
  · exact exp7_valid
  · exact exp7_valid
theorem margin18 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data18 25 := by decide +kernel
theorem positive18 {q : EdgeTriple} (hq : q ∈ box18.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data18 25
    data18_lower_valid data18_upper_valid data18_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin18 hq

def box19 : LogBox := ⟨![(11249/16384 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data19 : S1TaylorBoxData := ⟨box19,![exp8,exp6,exp6],![exp10,exp10,exp10],![exp9,exp8,exp8]⟩
theorem data19_lower_valid : ∀ j, (data19.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data19_upper_valid : ∀ j, (data19.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data19_center_valid : ∀ j, (data19.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp9_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin19 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data19 25 := by decide +kernel
theorem positive19 {q : EdgeTriple} (hq : q ∈ box19.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data19 25
    data19_lower_valid data19_upper_valid data19_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin19 hq

def box20 : LogBox := ⟨![(1607/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(8035/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data20 : S1TaylorBoxData := ⟨box20,![exp10,exp0,exp0],![exp14,exp2,exp2],![exp12,exp1,exp1]⟩
theorem data20_lower_valid : ∀ j, (data20.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data20_upper_valid : ∀ j, (data20.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data20_center_valid : ∀ j, (data20.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin20 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data20 25 := by decide +kernel
theorem positive20 {q : EdgeTriple} (hq : q ∈ box20.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data20 25
    data20_lower_valid data20_upper_valid data20_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin20 hq

def box21 : LogBox := ⟨![(1607/2048 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(8035/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data21 : S1TaylorBoxData := ⟨box21,![exp10,exp2,exp0],![exp14,exp4,exp2],![exp12,exp3,exp1]⟩
theorem data21_lower_valid : ∀ j, (data21.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data21_upper_valid : ∀ j, (data21.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data21_center_valid : ∀ j, (data21.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin21 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data21 25 := by decide +kernel
theorem positive21 {q : EdgeTriple} (hq : q ∈ box21.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data21 25
    data21_lower_valid data21_upper_valid data21_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin21 hq

def box22 : LogBox := ⟨![(1607/2048 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(8035/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data22 : S1TaylorBoxData := ⟨box22,![exp10,exp2,exp2],![exp14,exp4,exp4],![exp12,exp3,exp3]⟩
theorem data22_lower_valid : ∀ j, (data22.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data22_upper_valid : ∀ j, (data22.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data22_center_valid : ∀ j, (data22.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin22 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data22 25 := by decide +kernel
theorem positive22 {q : EdgeTriple} (hq : q ∈ box22.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data22 25
    data22_lower_valid data22_upper_valid data22_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin22 hq

def box23 : LogBox := ⟨![(8035/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data23 : S1TaylorBoxData := ⟨box23,![exp14,exp0,exp0],![exp18,exp2,exp2],![exp16,exp1,exp1]⟩
theorem data23_lower_valid : ∀ j, (data23.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data23_upper_valid : ∀ j, (data23.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data23_center_valid : ∀ j, (data23.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin23 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data23 25 := by decide +kernel
theorem positive23 {q : EdgeTriple} (hq : q ∈ box23.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data23 25
    data23_lower_valid data23_upper_valid data23_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin23 hq

def box24 : LogBox := ⟨![(8035/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data24 : S1TaylorBoxData := ⟨box24,![exp14,exp2,exp0],![exp18,exp4,exp2],![exp16,exp3,exp1]⟩
theorem data24_lower_valid : ∀ j, (data24.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data24_upper_valid : ∀ j, (data24.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data24_center_valid : ∀ j, (data24.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin24 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data24 25 := by decide +kernel
theorem positive24 {q : EdgeTriple} (hq : q ∈ box24.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data24 25
    data24_lower_valid data24_upper_valid data24_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin24 hq

def box25 : LogBox := ⟨![(8035/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(4821/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data25 : S1TaylorBoxData := ⟨box25,![exp14,exp2,exp2],![exp18,exp4,exp4],![exp16,exp3,exp3]⟩
theorem data25_lower_valid : ∀ j, (data25.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data25_upper_valid : ∀ j, (data25.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data25_center_valid : ∀ j, (data25.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin25 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data25 25 := by decide +kernel
theorem positive25 {q : EdgeTriple} (hq : q ∈ box25.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data25 25
    data25_lower_valid data25_upper_valid data25_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin25 hq

def box26 : LogBox := ⟨![(1607/2048 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(8035/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data26 : S1TaylorBoxData := ⟨box26,![exp10,exp4,exp0],![exp14,exp6,exp2],![exp12,exp5,exp1]⟩
theorem data26_lower_valid : ∀ j, (data26.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data26_upper_valid : ∀ j, (data26.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data26_center_valid : ∀ j, (data26.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin26 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data26 25 := by decide +kernel
theorem positive26 {q : EdgeTriple} (hq : q ∈ box26.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data26 25
    data26_lower_valid data26_upper_valid data26_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin26 hq

def box27 : LogBox := ⟨![(1607/2048 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(8035/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data27 : S1TaylorBoxData := ⟨box27,![exp10,exp4,exp2],![exp14,exp6,exp4],![exp12,exp5,exp3]⟩
theorem data27_lower_valid : ∀ j, (data27.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data27_upper_valid : ∀ j, (data27.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data27_center_valid : ∀ j, (data27.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin27 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data27 25 := by decide +kernel
theorem positive27 {q : EdgeTriple} (hq : q ∈ box27.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data27 25
    data27_lower_valid data27_upper_valid data27_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin27 hq

def box28 : LogBox := ⟨![(1607/2048 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(8035/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data28 : S1TaylorBoxData := ⟨box28,![exp10,exp6,exp0],![exp14,exp10,exp2],![exp12,exp8,exp1]⟩
theorem data28_lower_valid : ∀ j, (data28.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data28_upper_valid : ∀ j, (data28.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data28_center_valid : ∀ j, (data28.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin28 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data28 25 := by decide +kernel
theorem positive28 {q : EdgeTriple} (hq : q ∈ box28.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data28 25
    data28_lower_valid data28_upper_valid data28_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin28 hq

def box29 : LogBox := ⟨![(1607/2048 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(8035/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data29 : S1TaylorBoxData := ⟨box29,![exp10,exp6,exp2],![exp14,exp10,exp4],![exp12,exp8,exp3]⟩
theorem data29_lower_valid : ∀ j, (data29.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data29_upper_valid : ∀ j, (data29.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data29_center_valid : ∀ j, (data29.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin29 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data29 25 := by decide +kernel
theorem positive29 {q : EdgeTriple} (hq : q ∈ box29.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data29 25
    data29_lower_valid data29_upper_valid data29_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin29 hq

def box30 : LogBox := ⟨![(8035/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data30 : S1TaylorBoxData := ⟨box30,![exp14,exp4,exp0],![exp18,exp6,exp2],![exp16,exp5,exp1]⟩
theorem data30_lower_valid : ∀ j, (data30.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data30_upper_valid : ∀ j, (data30.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data30_center_valid : ∀ j, (data30.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin30 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data30 25 := by decide +kernel
theorem positive30 {q : EdgeTriple} (hq : q ∈ box30.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data30 25
    data30_lower_valid data30_upper_valid data30_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin30 hq

def box31 : LogBox := ⟨![(8035/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(4821/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data31 : S1TaylorBoxData := ⟨box31,![exp14,exp4,exp2],![exp18,exp6,exp4],![exp16,exp5,exp3]⟩
theorem data31_lower_valid : ∀ j, (data31.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data31_upper_valid : ∀ j, (data31.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data31_center_valid : ∀ j, (data31.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin31 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data31 25 := by decide +kernel
theorem positive31 {q : EdgeTriple} (hq : q ∈ box31.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data31 25
    data31_lower_valid data31_upper_valid data31_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

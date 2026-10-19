import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box32 : LogBox := ⟨![(8035/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data32 : S1TaylorBoxData := ⟨box32,![exp14,exp6,exp0],![exp18,exp10,exp2],![exp16,exp8,exp1]⟩
theorem data32_lower_valid : ∀ j, (data32.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data32_upper_valid : ∀ j, (data32.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data32_center_valid : ∀ j, (data32.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin32 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data32 25 := by decide +kernel
theorem positive32 {q : EdgeTriple} (hq : q ∈ box32.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data32 25
    data32_lower_valid data32_upper_valid data32_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin32 hq

def box33 : LogBox := ⟨![(8035/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(4821/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data33 : S1TaylorBoxData := ⟨box33,![exp14,exp6,exp2],![exp18,exp10,exp4],![exp16,exp8,exp3]⟩
theorem data33_lower_valid : ∀ j, (data33.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data33_upper_valid : ∀ j, (data33.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data33_center_valid : ∀ j, (data33.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin33 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data33 25 := by decide +kernel
theorem positive33 {q : EdgeTriple} (hq : q ∈ box33.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data33 25
    data33_lower_valid data33_upper_valid data33_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin33 hq

def box34 : LogBox := ⟨![(1607/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(8035/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data34 : S1TaylorBoxData := ⟨box34,![exp10,exp4,exp4],![exp14,exp6,exp6],![exp12,exp5,exp5]⟩
theorem data34_lower_valid : ∀ j, (data34.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data34_upper_valid : ∀ j, (data34.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data34_center_valid : ∀ j, (data34.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin34 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data34 25 := by decide +kernel
theorem positive34 {q : EdgeTriple} (hq : q ∈ box34.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data34 25
    data34_lower_valid data34_upper_valid data34_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin34 hq

def box35 : LogBox := ⟨![(1607/2048 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(8035/8192 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)]⟩
def data35 : S1TaylorBoxData := ⟨box35,![exp10,exp6,exp4],![exp14,exp10,exp6],![exp12,exp8,exp5]⟩
theorem data35_lower_valid : ∀ j, (data35.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data35_upper_valid : ∀ j, (data35.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data35_center_valid : ∀ j, (data35.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp8_valid
  · exact exp5_valid
theorem margin35 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data35 25 := by decide +kernel
theorem positive35 {q : EdgeTriple} (hq : q ∈ box35.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data35 25
    data35_lower_valid data35_upper_valid data35_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin35 hq

def box36 : LogBox := ⟨![(1607/2048 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(14463/16384 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data36 : S1TaylorBoxData := ⟨box36,![exp10,exp6,exp6],![exp12,exp10,exp10],![exp11,exp8,exp8]⟩
theorem data36_lower_valid : ∀ j, (data36.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data36_upper_valid : ∀ j, (data36.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data36_center_valid : ∀ j, (data36.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp11_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin36 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data36 25 := by decide +kernel
theorem positive36 {q : EdgeTriple} (hq : q ∈ box36.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data36 25
    data36_lower_valid data36_upper_valid data36_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin36 hq

def box37 : LogBox := ⟨![(14463/16384 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(8035/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data37 : S1TaylorBoxData := ⟨box37,![exp12,exp6,exp6],![exp14,exp10,exp10],![exp13,exp8,exp8]⟩
theorem data37_lower_valid : ∀ j, (data37.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data37_upper_valid : ∀ j, (data37.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data37_center_valid : ∀ j, (data37.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp13_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin37 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data37 25 := by decide +kernel
theorem positive37 {q : EdgeTriple} (hq : q ∈ box37.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data37 25
    data37_lower_valid data37_upper_valid data37_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin37 hq

def box38 : LogBox := ⟨![(8035/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(4821/4096 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data38 : S1TaylorBoxData := ⟨box38,![exp14,exp4,exp4],![exp18,exp6,exp6],![exp16,exp5,exp5]⟩
theorem data38_lower_valid : ∀ j, (data38.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data38_upper_valid : ∀ j, (data38.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data38_center_valid : ∀ j, (data38.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin38 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data38 25 := by decide +kernel
theorem positive38 {q : EdgeTriple} (hq : q ∈ box38.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data38 25
    data38_lower_valid data38_upper_valid data38_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin38 hq

def box39 : LogBox := ⟨![(8035/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(4821/4096 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)]⟩
def data39 : S1TaylorBoxData := ⟨box39,![exp14,exp6,exp4],![exp18,exp10,exp6],![exp16,exp8,exp5]⟩
theorem data39_lower_valid : ∀ j, (data39.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data39_upper_valid : ∀ j, (data39.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data39_center_valid : ∀ j, (data39.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp8_valid
  · exact exp5_valid
theorem margin39 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data39 25 := by decide +kernel
theorem positive39 {q : EdgeTriple} (hq : q ∈ box39.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data39 25
    data39_lower_valid data39_upper_valid data39_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin39 hq

def box40 : LogBox := ⟨![(8035/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(17677/16384 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data40 : S1TaylorBoxData := ⟨box40,![exp14,exp6,exp6],![exp16,exp10,exp10],![exp15,exp8,exp8]⟩
theorem data40_lower_valid : ∀ j, (data40.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data40_upper_valid : ∀ j, (data40.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data40_center_valid : ∀ j, (data40.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp15_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin40 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data40 25 := by decide +kernel
theorem positive40 {q : EdgeTriple} (hq : q ∈ box40.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data40 25
    data40_lower_valid data40_upper_valid data40_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin40 hq

def box41 : LogBox := ⟨![(17677/16384 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(4821/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data41 : S1TaylorBoxData := ⟨box41,![exp16,exp6,exp6],![exp18,exp10,exp10],![exp17,exp8,exp8]⟩
theorem data41_lower_valid : ∀ j, (data41.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data41_upper_valid : ∀ j, (data41.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data41_center_valid : ∀ j, (data41.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp17_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin41 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data41 25 := by decide +kernel
theorem positive41 {q : EdgeTriple} (hq : q ∈ box41.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data41 25
    data41_lower_valid data41_upper_valid data41_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin41 hq

def box42 : LogBox := ⟨![(4821/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(11249/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data42 : S1TaylorBoxData := ⟨box42,![exp18,exp0,exp0],![exp20,exp2,exp2],![exp19,exp1,exp1]⟩
theorem data42_lower_valid : ∀ j, (data42.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data42_upper_valid : ∀ j, (data42.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data42_center_valid : ∀ j, (data42.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin42 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data42 25 := by decide +kernel
theorem positive42 {q : EdgeTriple} (hq : q ∈ box42.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data42 25
    data42_lower_valid data42_upper_valid data42_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin42 hq

def box43 : LogBox := ⟨![(4821/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(11249/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data43 : S1TaylorBoxData := ⟨box43,![exp18,exp2,exp0],![exp20,exp4,exp2],![exp19,exp3,exp1]⟩
theorem data43_lower_valid : ∀ j, (data43.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data43_upper_valid : ∀ j, (data43.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data43_center_valid : ∀ j, (data43.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin43 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data43 25 := by decide +kernel
theorem positive43 {q : EdgeTriple} (hq : q ∈ box43.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data43 25
    data43_lower_valid data43_upper_valid data43_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin43 hq

def box44 : LogBox := ⟨![(4821/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(11249/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data44 : S1TaylorBoxData := ⟨box44,![exp18,exp2,exp2],![exp20,exp4,exp4],![exp19,exp3,exp3]⟩
theorem data44_lower_valid : ∀ j, (data44.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data44_upper_valid : ∀ j, (data44.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data44_center_valid : ∀ j, (data44.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin44 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data44 25 := by decide +kernel
theorem positive44 {q : EdgeTriple} (hq : q ∈ box44.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data44 25
    data44_lower_valid data44_upper_valid data44_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin44 hq

def box45 : LogBox := ⟨![(11249/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data45 : S1TaylorBoxData := ⟨box45,![exp20,exp0,exp0],![exp22,exp2,exp2],![exp21,exp1,exp1]⟩
theorem data45_lower_valid : ∀ j, (data45.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data45_upper_valid : ∀ j, (data45.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data45_center_valid : ∀ j, (data45.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin45 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data45 25 := by decide +kernel
theorem positive45 {q : EdgeTriple} (hq : q ∈ box45.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data45 25
    data45_lower_valid data45_upper_valid data45_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin45 hq

def box46 : LogBox := ⟨![(11249/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data46 : S1TaylorBoxData := ⟨box46,![exp20,exp2,exp0],![exp22,exp4,exp2],![exp21,exp3,exp1]⟩
theorem data46_lower_valid : ∀ j, (data46.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data46_upper_valid : ∀ j, (data46.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data46_center_valid : ∀ j, (data46.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin46 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data46 25 := by decide +kernel
theorem positive46 {q : EdgeTriple} (hq : q ∈ box46.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data46 25
    data46_lower_valid data46_upper_valid data46_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin46 hq

def box47 : LogBox := ⟨![(11249/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(1607/1024 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data47 : S1TaylorBoxData := ⟨box47,![exp20,exp2,exp2],![exp22,exp4,exp4],![exp21,exp3,exp3]⟩
theorem data47_lower_valid : ∀ j, (data47.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data47_upper_valid : ∀ j, (data47.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data47_center_valid : ∀ j, (data47.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin47 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data47 25 := by decide +kernel
theorem positive47 {q : EdgeTriple} (hq : q ∈ box47.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data47 25
    data47_lower_valid data47_upper_valid data47_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin47 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

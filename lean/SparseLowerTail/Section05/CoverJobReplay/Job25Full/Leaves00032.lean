import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box512 : LogBox := ⟨![(4821/1024 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data512 : S1TaylorBoxData := ⟨box512,![exp54,exp18,exp18],![exp58,exp22,exp22],![exp56,exp20,exp20]⟩
theorem data512_lower_valid : ∀ j, (data512.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data512_upper_valid : ∀ j, (data512.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data512_center_valid : ∀ j, (data512.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin512 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data512 25 := by decide +kernel
theorem positive512 {q : EdgeTriple} (hq : q ∈ box512.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data512 25
    data512_lower_valid data512_upper_valid data512_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin512 hq

def box513 : LogBox := ⟨![(20891/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data513 : S1TaylorBoxData := ⟨box513,![exp58,exp10,exp10],![exp62,exp18,exp18],![exp60,exp14,exp14]⟩
theorem data513_lower_valid : ∀ j, (data513.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data513_upper_valid : ∀ j, (data513.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data513_center_valid : ∀ j, (data513.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin513 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data513 25 := by decide +kernel
theorem positive513 {q : EdgeTriple} (hq : q ∈ box513.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data513 25
    data513_lower_valid data513_upper_valid data513_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin513 hq

def box514 : LogBox := ⟨![(20891/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data514 : S1TaylorBoxData := ⟨box514,![exp58,exp18,exp10],![exp62,exp22,exp18],![exp60,exp20,exp14]⟩
theorem data514_lower_valid : ∀ j, (data514.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data514_upper_valid : ∀ j, (data514.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data514_center_valid : ∀ j, (data514.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin514 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data514 25 := by decide +kernel
theorem positive514 {q : EdgeTriple} (hq : q ∈ box514.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data514 25
    data514_lower_valid data514_upper_valid data514_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin514 hq

def box515 : LogBox := ⟨![(20891/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data515 : S1TaylorBoxData := ⟨box515,![exp58,exp18,exp18],![exp62,exp22,exp22],![exp60,exp20,exp20]⟩
theorem data515_lower_valid : ∀ j, (data515.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data515_upper_valid : ∀ j, (data515.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data515_center_valid : ∀ j, (data515.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin515 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data515 25 := by decide +kernel
theorem positive515 {q : EdgeTriple} (hq : q ∈ box515.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data515 25
    data515_lower_valid data515_upper_valid data515_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin515 hq

def box516 : LogBox := ⟨![(11249/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(46603/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data516 : S1TaylorBoxData := ⟨box516,![exp62,exp0,exp0],![exp64,exp2,exp2],![exp63,exp1,exp1]⟩
theorem data516_lower_valid : ∀ j, (data516.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data516_upper_valid : ∀ j, (data516.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data516_center_valid : ∀ j, (data516.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp63_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin516 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data516 25 := by decide +kernel
theorem positive516 {q : EdgeTriple} (hq : q ∈ box516.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data516 25
    data516_lower_valid data516_upper_valid data516_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin516 hq

def box517 : LogBox := ⟨![(11249/2048 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(46603/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data517 : S1TaylorBoxData := ⟨box517,![exp62,exp2,exp0],![exp64,exp4,exp4],![exp63,exp3,exp2]⟩
theorem data517_lower_valid : ∀ j, (data517.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data517_upper_valid : ∀ j, (data517.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data517_center_valid : ∀ j, (data517.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp63_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin517 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data517 25 := by decide +kernel
theorem positive517 {q : EdgeTriple} (hq : q ∈ box517.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data517 25
    data517_lower_valid data517_upper_valid data517_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin517 hq

def box518 : LogBox := ⟨![(46603/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data518 : S1TaylorBoxData := ⟨box518,![exp64,exp0,exp0],![exp66,exp2,exp2],![exp65,exp1,exp1]⟩
theorem data518_lower_valid : ∀ j, (data518.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data518_upper_valid : ∀ j, (data518.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data518_center_valid : ∀ j, (data518.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp65_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin518 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data518 25 := by decide +kernel
theorem positive518 {q : EdgeTriple} (hq : q ∈ box518.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data518 25
    data518_lower_valid data518_upper_valid data518_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin518 hq

def box519 : LogBox := ⟨![(46603/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data519 : S1TaylorBoxData := ⟨box519,![exp64,exp2,exp0],![exp66,exp4,exp4],![exp65,exp3,exp2]⟩
theorem data519_lower_valid : ∀ j, (data519.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data519_upper_valid : ∀ j, (data519.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data519_center_valid : ∀ j, (data519.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp65_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin519 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data519 25 := by decide +kernel
theorem positive519 {q : EdgeTriple} (hq : q ∈ box519.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data519 25
    data519_lower_valid data519_upper_valid data519_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin519 hq

def box520 : LogBox := ⟨![(11249/2048 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(46603/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data520 : S1TaylorBoxData := ⟨box520,![exp62,exp4,exp0],![exp64,exp6,exp4],![exp63,exp5,exp2]⟩
theorem data520_lower_valid : ∀ j, (data520.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data520_upper_valid : ∀ j, (data520.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data520_center_valid : ∀ j, (data520.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp63_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin520 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data520 25 := by decide +kernel
theorem positive520 {q : EdgeTriple} (hq : q ∈ box520.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data520 25
    data520_lower_valid data520_upper_valid data520_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin520 hq

def box521 : LogBox := ⟨![(11249/2048 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(46603/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data521 : S1TaylorBoxData := ⟨box521,![exp62,exp6,exp0],![exp64,exp10,exp4],![exp63,exp8,exp2]⟩
theorem data521_lower_valid : ∀ j, (data521.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data521_upper_valid : ∀ j, (data521.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data521_center_valid : ∀ j, (data521.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp63_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin521 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data521 25 := by decide +kernel
theorem positive521 {q : EdgeTriple} (hq : q ∈ box521.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data521 25
    data521_lower_valid data521_upper_valid data521_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin521 hq

def box522 : LogBox := ⟨![(46603/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data522 : S1TaylorBoxData := ⟨box522,![exp64,exp4,exp0],![exp66,exp6,exp4],![exp65,exp5,exp2]⟩
theorem data522_lower_valid : ∀ j, (data522.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data522_upper_valid : ∀ j, (data522.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data522_center_valid : ∀ j, (data522.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp65_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin522 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data522 25 := by decide +kernel
theorem positive522 {q : EdgeTriple} (hq : q ∈ box522.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data522 25
    data522_lower_valid data522_upper_valid data522_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin522 hq

def box523 : LogBox := ⟨![(46603/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data523 : S1TaylorBoxData := ⟨box523,![exp64,exp6,exp0],![exp66,exp10,exp4],![exp65,exp8,exp2]⟩
theorem data523_lower_valid : ∀ j, (data523.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data523_upper_valid : ∀ j, (data523.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data523_center_valid : ∀ j, (data523.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp65_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin523 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data523 25 := by decide +kernel
theorem positive523 {q : EdgeTriple} (hq : q ∈ box523.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data523 25
    data523_lower_valid data523_upper_valid data523_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin523 hq

def box524 : LogBox := ⟨![(11249/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data524 : S1TaylorBoxData := ⟨box524,![exp62,exp4,exp4],![exp66,exp10,exp10],![exp64,exp6,exp6]⟩
theorem data524_lower_valid : ∀ j, (data524.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data524_upper_valid : ∀ j, (data524.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data524_center_valid : ∀ j, (data524.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin524 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data524 25 := by decide +kernel
theorem positive524 {q : EdgeTriple} (hq : q ∈ box524.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data524 25
    data524_lower_valid data524_upper_valid data524_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin524 hq

def box525 : LogBox := ⟨![(24105/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(49817/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data525 : S1TaylorBoxData := ⟨box525,![exp66,exp0,exp0],![exp68,exp2,exp2],![exp67,exp1,exp1]⟩
theorem data525_lower_valid : ∀ j, (data525.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data525_upper_valid : ∀ j, (data525.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data525_center_valid : ∀ j, (data525.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp67_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin525 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data525 25 := by decide +kernel
theorem positive525 {q : EdgeTriple} (hq : q ∈ box525.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data525 25
    data525_lower_valid data525_upper_valid data525_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin525 hq

def box526 : LogBox := ⟨![(24105/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(49817/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data526 : S1TaylorBoxData := ⟨box526,![exp66,exp2,exp0],![exp68,exp4,exp4],![exp67,exp3,exp2]⟩
theorem data526_lower_valid : ∀ j, (data526.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data526_upper_valid : ∀ j, (data526.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data526_center_valid : ∀ j, (data526.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp67_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin526 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data526 25 := by decide +kernel
theorem positive526 {q : EdgeTriple} (hq : q ∈ box526.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data526 25
    data526_lower_valid data526_upper_valid data526_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin526 hq

def box527 : LogBox := ⟨![(49817/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data527 : S1TaylorBoxData := ⟨box527,![exp68,exp0,exp0],![exp70,exp2,exp2],![exp69,exp1,exp1]⟩
theorem data527_lower_valid : ∀ j, (data527.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data527_upper_valid : ∀ j, (data527.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data527_center_valid : ∀ j, (data527.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp69_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin527 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data527 25 := by decide +kernel
theorem positive527 {q : EdgeTriple} (hq : q ∈ box527.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data527 25
    data527_lower_valid data527_upper_valid data527_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin527 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

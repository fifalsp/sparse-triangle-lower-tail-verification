import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box128 : LogBox := ⟨![(14463/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data128 : S1TaylorBoxData := ⟨box128,![exp24,exp6,exp0],![exp26,exp10,exp2],![exp25,exp8,exp1]⟩
theorem data128_lower_valid : ∀ j, (data128.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data128_upper_valid : ∀ j, (data128.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data128_center_valid : ∀ j, (data128.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin128 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data128 25 := by decide +kernel
theorem positive128 {q : EdgeTriple} (hq : q ∈ box128.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data128 25
    data128_lower_valid data128_upper_valid data128_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin128 hq

def box129 : LogBox := ⟨![(14463/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(8035/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data129 : S1TaylorBoxData := ⟨box129,![exp24,exp6,exp2],![exp26,exp10,exp4],![exp25,exp8,exp3]⟩
theorem data129_lower_valid : ∀ j, (data129.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data129_upper_valid : ∀ j, (data129.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data129_center_valid : ∀ j, (data129.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin129 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data129 25 := by decide +kernel
theorem positive129 {q : EdgeTriple} (hq : q ∈ box129.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data129 25
    data129_lower_valid data129_upper_valid data129_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin129 hq

def box130 : LogBox := ⟨![(1607/1024 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(14463/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data130 : S1TaylorBoxData := ⟨box130,![exp22,exp4,exp4],![exp24,exp6,exp6],![exp23,exp5,exp5]⟩
theorem data130_lower_valid : ∀ j, (data130.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data130_upper_valid : ∀ j, (data130.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data130_center_valid : ∀ j, (data130.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin130 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data130 25 := by decide +kernel
theorem positive130 {q : EdgeTriple} (hq : q ∈ box130.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data130 25
    data130_lower_valid data130_upper_valid data130_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin130 hq

def box131 : LogBox := ⟨![(1607/1024 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(14463/8192 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)]⟩
def data131 : S1TaylorBoxData := ⟨box131,![exp22,exp6,exp4],![exp24,exp10,exp6],![exp23,exp8,exp5]⟩
theorem data131_lower_valid : ∀ j, (data131.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data131_upper_valid : ∀ j, (data131.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data131_center_valid : ∀ j, (data131.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp8_valid
  · exact exp5_valid
theorem margin131 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data131 25 := by decide +kernel
theorem positive131 {q : EdgeTriple} (hq : q ∈ box131.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data131 25
    data131_lower_valid data131_upper_valid data131_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin131 hq

def box132 : LogBox := ⟨![(1607/1024 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(14463/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data132 : S1TaylorBoxData := ⟨box132,![exp22,exp6,exp6],![exp24,exp10,exp10],![exp23,exp8,exp8]⟩
theorem data132_lower_valid : ∀ j, (data132.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data132_upper_valid : ∀ j, (data132.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data132_center_valid : ∀ j, (data132.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin132 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data132 25 := by decide +kernel
theorem positive132 {q : EdgeTriple} (hq : q ∈ box132.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data132 25
    data132_lower_valid data132_upper_valid data132_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin132 hq

def box133 : LogBox := ⟨![(14463/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(8035/4096 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data133 : S1TaylorBoxData := ⟨box133,![exp24,exp4,exp4],![exp26,exp6,exp6],![exp25,exp5,exp5]⟩
theorem data133_lower_valid : ∀ j, (data133.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data133_upper_valid : ∀ j, (data133.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data133_center_valid : ∀ j, (data133.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin133 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data133 25 := by decide +kernel
theorem positive133 {q : EdgeTriple} (hq : q ∈ box133.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data133 25
    data133_lower_valid data133_upper_valid data133_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin133 hq

def box134 : LogBox := ⟨![(14463/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(8035/4096 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)]⟩
def data134 : S1TaylorBoxData := ⟨box134,![exp24,exp6,exp4],![exp26,exp10,exp6],![exp25,exp8,exp5]⟩
theorem data134_lower_valid : ∀ j, (data134.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data134_upper_valid : ∀ j, (data134.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data134_center_valid : ∀ j, (data134.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp8_valid
  · exact exp5_valid
theorem margin134 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data134 25 := by decide +kernel
theorem positive134 {q : EdgeTriple} (hq : q ∈ box134.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data134 25
    data134_lower_valid data134_upper_valid data134_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin134 hq

def box135 : LogBox := ⟨![(14463/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(8035/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data135 : S1TaylorBoxData := ⟨box135,![exp24,exp6,exp6],![exp26,exp10,exp10],![exp25,exp8,exp8]⟩
theorem data135_lower_valid : ∀ j, (data135.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data135_upper_valid : ∀ j, (data135.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data135_center_valid : ∀ j, (data135.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin135 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data135 25 := by decide +kernel
theorem positive135 {q : EdgeTriple} (hq : q ∈ box135.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data135 25
    data135_lower_valid data135_upper_valid data135_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin135 hq

def box136 : LogBox := ⟨![(8035/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(17677/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data136 : S1TaylorBoxData := ⟨box136,![exp26,exp0,exp0],![exp28,exp2,exp2],![exp27,exp1,exp1]⟩
theorem data136_lower_valid : ∀ j, (data136.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data136_upper_valid : ∀ j, (data136.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data136_center_valid : ∀ j, (data136.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin136 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data136 25 := by decide +kernel
theorem positive136 {q : EdgeTriple} (hq : q ∈ box136.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data136 25
    data136_lower_valid data136_upper_valid data136_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin136 hq

def box137 : LogBox := ⟨![(8035/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(17677/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data137 : S1TaylorBoxData := ⟨box137,![exp26,exp2,exp0],![exp28,exp4,exp2],![exp27,exp3,exp1]⟩
theorem data137_lower_valid : ∀ j, (data137.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data137_upper_valid : ∀ j, (data137.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data137_center_valid : ∀ j, (data137.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin137 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data137 25 := by decide +kernel
theorem positive137 {q : EdgeTriple} (hq : q ∈ box137.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data137 25
    data137_lower_valid data137_upper_valid data137_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin137 hq

def box138 : LogBox := ⟨![(8035/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(17677/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data138 : S1TaylorBoxData := ⟨box138,![exp26,exp2,exp2],![exp28,exp4,exp4],![exp27,exp3,exp3]⟩
theorem data138_lower_valid : ∀ j, (data138.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data138_upper_valid : ∀ j, (data138.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data138_center_valid : ∀ j, (data138.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin138 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data138 25 := by decide +kernel
theorem positive138 {q : EdgeTriple} (hq : q ∈ box138.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data138 25
    data138_lower_valid data138_upper_valid data138_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin138 hq

def box139 : LogBox := ⟨![(17677/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data139 : S1TaylorBoxData := ⟨box139,![exp28,exp0,exp0],![exp30,exp2,exp2],![exp29,exp1,exp1]⟩
theorem data139_lower_valid : ∀ j, (data139.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data139_upper_valid : ∀ j, (data139.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data139_center_valid : ∀ j, (data139.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin139 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data139 25 := by decide +kernel
theorem positive139 {q : EdgeTriple} (hq : q ∈ box139.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data139 25
    data139_lower_valid data139_upper_valid data139_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin139 hq

def box140 : LogBox := ⟨![(17677/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data140 : S1TaylorBoxData := ⟨box140,![exp28,exp2,exp0],![exp30,exp4,exp2],![exp29,exp3,exp1]⟩
theorem data140_lower_valid : ∀ j, (data140.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data140_upper_valid : ∀ j, (data140.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data140_center_valid : ∀ j, (data140.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin140 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data140 25 := by decide +kernel
theorem positive140 {q : EdgeTriple} (hq : q ∈ box140.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data140 25
    data140_lower_valid data140_upper_valid data140_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin140 hq

def box141 : LogBox := ⟨![(17677/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(4821/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data141 : S1TaylorBoxData := ⟨box141,![exp28,exp2,exp2],![exp30,exp4,exp4],![exp29,exp3,exp3]⟩
theorem data141_lower_valid : ∀ j, (data141.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data141_upper_valid : ∀ j, (data141.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data141_center_valid : ∀ j, (data141.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin141 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data141 25 := by decide +kernel
theorem positive141 {q : EdgeTriple} (hq : q ∈ box141.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data141 25
    data141_lower_valid data141_upper_valid data141_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin141 hq

def box142 : LogBox := ⟨![(8035/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(17677/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data142 : S1TaylorBoxData := ⟨box142,![exp26,exp4,exp0],![exp28,exp6,exp2],![exp27,exp5,exp1]⟩
theorem data142_lower_valid : ∀ j, (data142.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data142_upper_valid : ∀ j, (data142.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data142_center_valid : ∀ j, (data142.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin142 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data142 25 := by decide +kernel
theorem positive142 {q : EdgeTriple} (hq : q ∈ box142.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data142 25
    data142_lower_valid data142_upper_valid data142_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin142 hq

def box143 : LogBox := ⟨![(8035/4096 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(17677/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data143 : S1TaylorBoxData := ⟨box143,![exp26,exp4,exp2],![exp28,exp6,exp4],![exp27,exp5,exp3]⟩
theorem data143_lower_valid : ∀ j, (data143.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data143_upper_valid : ∀ j, (data143.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data143_center_valid : ∀ j, (data143.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin143 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data143 25 := by decide +kernel
theorem positive143 {q : EdgeTriple} (hq : q ∈ box143.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data143 25
    data143_lower_valid data143_upper_valid data143_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin143 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

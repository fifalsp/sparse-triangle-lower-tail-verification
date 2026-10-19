import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box208 : LogBox := ⟨![(4821/2048 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(20891/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data208 : S1TaylorBoxData := ⟨box208,![exp30,exp6,exp0],![exp32,exp10,exp2],![exp31,exp8,exp1]⟩
theorem data208_lower_valid : ∀ j, (data208.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data208_upper_valid : ∀ j, (data208.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data208_center_valid : ∀ j, (data208.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin208 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data208 25 := by decide +kernel
theorem positive208 {q : EdgeTriple} (hq : q ∈ box208.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data208 25
    data208_lower_valid data208_upper_valid data208_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin208 hq

def box209 : LogBox := ⟨![(4821/2048 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(20891/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data209 : S1TaylorBoxData := ⟨box209,![exp30,exp6,exp2],![exp32,exp10,exp4],![exp31,exp8,exp3]⟩
theorem data209_lower_valid : ∀ j, (data209.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data209_upper_valid : ∀ j, (data209.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data209_center_valid : ∀ j, (data209.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin209 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data209 25 := by decide +kernel
theorem positive209 {q : EdgeTriple} (hq : q ∈ box209.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data209 25
    data209_lower_valid data209_upper_valid data209_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin209 hq

def box210 : LogBox := ⟨![(20891/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data210 : S1TaylorBoxData := ⟨box210,![exp32,exp4,exp0],![exp34,exp6,exp2],![exp33,exp5,exp1]⟩
theorem data210_lower_valid : ∀ j, (data210.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data210_upper_valid : ∀ j, (data210.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data210_center_valid : ∀ j, (data210.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin210 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data210 25 := by decide +kernel
theorem positive210 {q : EdgeTriple} (hq : q ∈ box210.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data210 25
    data210_lower_valid data210_upper_valid data210_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin210 hq

def box211 : LogBox := ⟨![(20891/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(11249/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data211 : S1TaylorBoxData := ⟨box211,![exp32,exp4,exp2],![exp34,exp6,exp4],![exp33,exp5,exp3]⟩
theorem data211_lower_valid : ∀ j, (data211.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data211_upper_valid : ∀ j, (data211.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data211_center_valid : ∀ j, (data211.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin211 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data211 25 := by decide +kernel
theorem positive211 {q : EdgeTriple} (hq : q ∈ box211.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data211 25
    data211_lower_valid data211_upper_valid data211_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin211 hq

def box212 : LogBox := ⟨![(20891/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data212 : S1TaylorBoxData := ⟨box212,![exp32,exp6,exp0],![exp34,exp10,exp2],![exp33,exp8,exp1]⟩
theorem data212_lower_valid : ∀ j, (data212.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data212_upper_valid : ∀ j, (data212.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data212_center_valid : ∀ j, (data212.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin212 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data212 25 := by decide +kernel
theorem positive212 {q : EdgeTriple} (hq : q ∈ box212.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data212 25
    data212_lower_valid data212_upper_valid data212_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin212 hq

def box213 : LogBox := ⟨![(20891/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(11249/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data213 : S1TaylorBoxData := ⟨box213,![exp32,exp6,exp2],![exp34,exp10,exp4],![exp33,exp8,exp3]⟩
theorem data213_lower_valid : ∀ j, (data213.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data213_upper_valid : ∀ j, (data213.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data213_center_valid : ∀ j, (data213.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin213 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data213 25 := by decide +kernel
theorem positive213 {q : EdgeTriple} (hq : q ∈ box213.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data213 25
    data213_lower_valid data213_upper_valid data213_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin213 hq

def box214 : LogBox := ⟨![(4821/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(20891/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data214 : S1TaylorBoxData := ⟨box214,![exp30,exp4,exp4],![exp32,exp6,exp6],![exp31,exp5,exp5]⟩
theorem data214_lower_valid : ∀ j, (data214.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data214_upper_valid : ∀ j, (data214.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data214_center_valid : ∀ j, (data214.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin214 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data214 25 := by decide +kernel
theorem positive214 {q : EdgeTriple} (hq : q ∈ box214.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data214 25
    data214_lower_valid data214_upper_valid data214_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin214 hq

def box215 : LogBox := ⟨![(4821/2048 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(20891/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data215 : S1TaylorBoxData := ⟨box215,![exp30,exp6,exp4],![exp32,exp10,exp10],![exp31,exp8,exp6]⟩
theorem data215_lower_valid : ∀ j, (data215.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data215_upper_valid : ∀ j, (data215.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data215_center_valid : ∀ j, (data215.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp8_valid
  · exact exp6_valid
theorem margin215 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data215 25 := by decide +kernel
theorem positive215 {q : EdgeTriple} (hq : q ∈ box215.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data215 25
    data215_lower_valid data215_upper_valid data215_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin215 hq

def box216 : LogBox := ⟨![(20891/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data216 : S1TaylorBoxData := ⟨box216,![exp32,exp4,exp4],![exp34,exp6,exp6],![exp33,exp5,exp5]⟩
theorem data216_lower_valid : ∀ j, (data216.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data216_upper_valid : ∀ j, (data216.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data216_center_valid : ∀ j, (data216.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin216 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data216 25 := by decide +kernel
theorem positive216 {q : EdgeTriple} (hq : q ∈ box216.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data216 25
    data216_lower_valid data216_upper_valid data216_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin216 hq

def box217 : LogBox := ⟨![(20891/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data217 : S1TaylorBoxData := ⟨box217,![exp32,exp6,exp4],![exp34,exp10,exp10],![exp33,exp8,exp6]⟩
theorem data217_lower_valid : ∀ j, (data217.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data217_upper_valid : ∀ j, (data217.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data217_center_valid : ∀ j, (data217.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp8_valid
  · exact exp6_valid
theorem margin217 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data217 25 := by decide +kernel
theorem positive217 {q : EdgeTriple} (hq : q ∈ box217.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data217 25
    data217_lower_valid data217_upper_valid data217_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin217 hq

def box218 : LogBox := ⟨![(11249/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(24105/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data218 : S1TaylorBoxData := ⟨box218,![exp34,exp0,exp0],![exp36,exp2,exp2],![exp35,exp1,exp1]⟩
theorem data218_lower_valid : ∀ j, (data218.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data218_upper_valid : ∀ j, (data218.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data218_center_valid : ∀ j, (data218.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin218 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data218 25 := by decide +kernel
theorem positive218 {q : EdgeTriple} (hq : q ∈ box218.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data218 25
    data218_lower_valid data218_upper_valid data218_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin218 hq

def box219 : LogBox := ⟨![(11249/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(24105/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data219 : S1TaylorBoxData := ⟨box219,![exp34,exp2,exp0],![exp36,exp4,exp2],![exp35,exp3,exp1]⟩
theorem data219_lower_valid : ∀ j, (data219.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data219_upper_valid : ∀ j, (data219.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data219_center_valid : ∀ j, (data219.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin219 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data219 25 := by decide +kernel
theorem positive219 {q : EdgeTriple} (hq : q ∈ box219.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data219 25
    data219_lower_valid data219_upper_valid data219_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin219 hq

def box220 : LogBox := ⟨![(11249/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(24105/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data220 : S1TaylorBoxData := ⟨box220,![exp34,exp2,exp2],![exp36,exp4,exp4],![exp35,exp3,exp3]⟩
theorem data220_lower_valid : ∀ j, (data220.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data220_upper_valid : ∀ j, (data220.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data220_center_valid : ∀ j, (data220.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin220 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data220 25 := by decide +kernel
theorem positive220 {q : EdgeTriple} (hq : q ∈ box220.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data220 25
    data220_lower_valid data220_upper_valid data220_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin220 hq

def box221 : LogBox := ⟨![(24105/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data221 : S1TaylorBoxData := ⟨box221,![exp36,exp0,exp0],![exp38,exp2,exp2],![exp37,exp1,exp1]⟩
theorem data221_lower_valid : ∀ j, (data221.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data221_upper_valid : ∀ j, (data221.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data221_center_valid : ∀ j, (data221.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin221 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data221 25 := by decide +kernel
theorem positive221 {q : EdgeTriple} (hq : q ∈ box221.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data221 25
    data221_lower_valid data221_upper_valid data221_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin221 hq

def box222 : LogBox := ⟨![(24105/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data222 : S1TaylorBoxData := ⟨box222,![exp36,exp2,exp0],![exp38,exp4,exp2],![exp37,exp3,exp1]⟩
theorem data222_lower_valid : ∀ j, (data222.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data222_upper_valid : ∀ j, (data222.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data222_center_valid : ∀ j, (data222.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin222 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data222 25 := by decide +kernel
theorem positive222 {q : EdgeTriple} (hq : q ∈ box222.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data222 25
    data222_lower_valid data222_upper_valid data222_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin222 hq

def box223 : LogBox := ⟨![(24105/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(1607/512 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data223 : S1TaylorBoxData := ⟨box223,![exp36,exp2,exp2],![exp38,exp4,exp4],![exp37,exp3,exp3]⟩
theorem data223_lower_valid : ∀ j, (data223.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data223_upper_valid : ∀ j, (data223.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data223_center_valid : ∀ j, (data223.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin223 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data223 25 := by decide +kernel
theorem positive223 {q : EdgeTriple} (hq : q ∈ box223.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data223 25
    data223_lower_valid data223_upper_valid data223_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin223 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

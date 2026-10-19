import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box224 : LogBox := ⟨![(11249/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(24105/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data224 : S1TaylorBoxData := ⟨box224,![exp34,exp4,exp0],![exp36,exp6,exp2],![exp35,exp5,exp1]⟩
theorem data224_lower_valid : ∀ j, (data224.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data224_upper_valid : ∀ j, (data224.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data224_center_valid : ∀ j, (data224.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin224 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data224 25 := by decide +kernel
theorem positive224 {q : EdgeTriple} (hq : q ∈ box224.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data224 25
    data224_lower_valid data224_upper_valid data224_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin224 hq

def box225 : LogBox := ⟨![(11249/4096 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(24105/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data225 : S1TaylorBoxData := ⟨box225,![exp34,exp4,exp2],![exp36,exp6,exp4],![exp35,exp5,exp3]⟩
theorem data225_lower_valid : ∀ j, (data225.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data225_upper_valid : ∀ j, (data225.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data225_center_valid : ∀ j, (data225.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin225 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data225 25 := by decide +kernel
theorem positive225 {q : EdgeTriple} (hq : q ∈ box225.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data225 25
    data225_lower_valid data225_upper_valid data225_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin225 hq

def box226 : LogBox := ⟨![(11249/4096 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(24105/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data226 : S1TaylorBoxData := ⟨box226,![exp34,exp6,exp0],![exp36,exp10,exp2],![exp35,exp8,exp1]⟩
theorem data226_lower_valid : ∀ j, (data226.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data226_upper_valid : ∀ j, (data226.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data226_center_valid : ∀ j, (data226.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin226 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data226 25 := by decide +kernel
theorem positive226 {q : EdgeTriple} (hq : q ∈ box226.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data226 25
    data226_lower_valid data226_upper_valid data226_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin226 hq

def box227 : LogBox := ⟨![(11249/4096 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(24105/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data227 : S1TaylorBoxData := ⟨box227,![exp34,exp6,exp2],![exp36,exp10,exp4],![exp35,exp8,exp3]⟩
theorem data227_lower_valid : ∀ j, (data227.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data227_upper_valid : ∀ j, (data227.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data227_center_valid : ∀ j, (data227.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin227 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data227 25 := by decide +kernel
theorem positive227 {q : EdgeTriple} (hq : q ∈ box227.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data227 25
    data227_lower_valid data227_upper_valid data227_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin227 hq

def box228 : LogBox := ⟨![(24105/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data228 : S1TaylorBoxData := ⟨box228,![exp36,exp4,exp0],![exp38,exp6,exp2],![exp37,exp5,exp1]⟩
theorem data228_lower_valid : ∀ j, (data228.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data228_upper_valid : ∀ j, (data228.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data228_center_valid : ∀ j, (data228.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin228 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data228 25 := by decide +kernel
theorem positive228 {q : EdgeTriple} (hq : q ∈ box228.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data228 25
    data228_lower_valid data228_upper_valid data228_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin228 hq

def box229 : LogBox := ⟨![(24105/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(1607/512 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data229 : S1TaylorBoxData := ⟨box229,![exp36,exp4,exp2],![exp38,exp6,exp4],![exp37,exp5,exp3]⟩
theorem data229_lower_valid : ∀ j, (data229.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data229_upper_valid : ∀ j, (data229.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data229_center_valid : ∀ j, (data229.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin229 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data229 25 := by decide +kernel
theorem positive229 {q : EdgeTriple} (hq : q ∈ box229.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data229 25
    data229_lower_valid data229_upper_valid data229_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin229 hq

def box230 : LogBox := ⟨![(24105/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data230 : S1TaylorBoxData := ⟨box230,![exp36,exp6,exp0],![exp38,exp10,exp4],![exp37,exp8,exp2]⟩
theorem data230_lower_valid : ∀ j, (data230.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data230_upper_valid : ∀ j, (data230.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data230_center_valid : ∀ j, (data230.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin230 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data230 25 := by decide +kernel
theorem positive230 {q : EdgeTriple} (hq : q ∈ box230.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data230 25
    data230_lower_valid data230_upper_valid data230_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin230 hq

def box231 : LogBox := ⟨![(11249/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(24105/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data231 : S1TaylorBoxData := ⟨box231,![exp34,exp4,exp4],![exp36,exp6,exp6],![exp35,exp5,exp5]⟩
theorem data231_lower_valid : ∀ j, (data231.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data231_upper_valid : ∀ j, (data231.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data231_center_valid : ∀ j, (data231.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin231 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data231 25 := by decide +kernel
theorem positive231 {q : EdgeTriple} (hq : q ∈ box231.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data231 25
    data231_lower_valid data231_upper_valid data231_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin231 hq

def box232 : LogBox := ⟨![(11249/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(24105/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data232 : S1TaylorBoxData := ⟨box232,![exp34,exp6,exp4],![exp36,exp10,exp10],![exp35,exp8,exp6]⟩
theorem data232_lower_valid : ∀ j, (data232.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data232_upper_valid : ∀ j, (data232.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data232_center_valid : ∀ j, (data232.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp8_valid
  · exact exp6_valid
theorem margin232 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data232 25 := by decide +kernel
theorem positive232 {q : EdgeTriple} (hq : q ∈ box232.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data232 25
    data232_lower_valid data232_upper_valid data232_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin232 hq

def box233 : LogBox := ⟨![(24105/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data233 : S1TaylorBoxData := ⟨box233,![exp36,exp4,exp4],![exp38,exp6,exp6],![exp37,exp5,exp5]⟩
theorem data233_lower_valid : ∀ j, (data233.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data233_upper_valid : ∀ j, (data233.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data233_center_valid : ∀ j, (data233.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin233 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data233 25 := by decide +kernel
theorem positive233 {q : EdgeTriple} (hq : q ∈ box233.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data233 25
    data233_lower_valid data233_upper_valid data233_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin233 hq

def box234 : LogBox := ⟨![(24105/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data234 : S1TaylorBoxData := ⟨box234,![exp36,exp6,exp4],![exp38,exp10,exp10],![exp37,exp8,exp6]⟩
theorem data234_lower_valid : ∀ j, (data234.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data234_upper_valid : ∀ j, (data234.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data234_center_valid : ∀ j, (data234.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp8_valid
  · exact exp6_valid
theorem margin234 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data234 25 := by decide +kernel
theorem positive234 {q : EdgeTriple} (hq : q ∈ box234.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data234 25
    data234_lower_valid data234_upper_valid data234_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin234 hq

def box235 : LogBox := ⟨![(4821/2048 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(20891/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data235 : S1TaylorBoxData := ⟨box235,![exp30,exp10,exp0],![exp32,exp14,exp4],![exp31,exp12,exp2]⟩
theorem data235_lower_valid : ∀ j, (data235.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data235_upper_valid : ∀ j, (data235.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data235_center_valid : ∀ j, (data235.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin235 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data235 25 := by decide +kernel
theorem positive235 {q : EdgeTriple} (hq : q ∈ box235.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data235 25
    data235_lower_valid data235_upper_valid data235_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin235 hq

def box236 : LogBox := ⟨![(4821/2048 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(20891/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data236 : S1TaylorBoxData := ⟨box236,![exp30,exp14,exp0],![exp32,exp18,exp4],![exp31,exp16,exp2]⟩
theorem data236_lower_valid : ∀ j, (data236.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data236_upper_valid : ∀ j, (data236.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data236_center_valid : ∀ j, (data236.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin236 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data236 25 := by decide +kernel
theorem positive236 {q : EdgeTriple} (hq : q ∈ box236.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data236 25
    data236_lower_valid data236_upper_valid data236_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin236 hq

def box237 : LogBox := ⟨![(20891/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data237 : S1TaylorBoxData := ⟨box237,![exp32,exp10,exp0],![exp34,exp14,exp4],![exp33,exp12,exp2]⟩
theorem data237_lower_valid : ∀ j, (data237.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data237_upper_valid : ∀ j, (data237.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data237_center_valid : ∀ j, (data237.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin237 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data237 25 := by decide +kernel
theorem positive237 {q : EdgeTriple} (hq : q ∈ box237.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data237 25
    data237_lower_valid data237_upper_valid data237_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin237 hq

def box238 : LogBox := ⟨![(20891/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data238 : S1TaylorBoxData := ⟨box238,![exp32,exp14,exp0],![exp34,exp18,exp4],![exp33,exp16,exp2]⟩
theorem data238_lower_valid : ∀ j, (data238.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data238_upper_valid : ∀ j, (data238.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data238_center_valid : ∀ j, (data238.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin238 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data238 25 := by decide +kernel
theorem positive238 {q : EdgeTriple} (hq : q ∈ box238.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data238 25
    data238_lower_valid data238_upper_valid data238_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin238 hq

def box239 : LogBox := ⟨![(4821/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(20891/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data239 : S1TaylorBoxData := ⟨box239,![exp30,exp10,exp4],![exp32,exp14,exp10],![exp31,exp12,exp6]⟩
theorem data239_lower_valid : ∀ j, (data239.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data239_upper_valid : ∀ j, (data239.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data239_center_valid : ∀ j, (data239.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp12_valid
  · exact exp6_valid
theorem margin239 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data239 25 := by decide +kernel
theorem positive239 {q : EdgeTriple} (hq : q ∈ box239.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data239 25
    data239_lower_valid data239_upper_valid data239_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin239 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box192 : LogBox := ⟨![(1607/1024 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(14463/8192 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data192 : S1TaylorBoxData := ⟨box192,![exp22,exp18,exp10],![exp24,exp22,exp18],![exp23,exp20,exp14]⟩
theorem data192_lower_valid : ∀ j, (data192.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data192_upper_valid : ∀ j, (data192.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data192_center_valid : ∀ j, (data192.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin192 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data192 25 := by decide +kernel
theorem positive192 {q : EdgeTriple} (hq : q ∈ box192.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data192 25
    data192_lower_valid data192_upper_valid data192_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin192 hq

def box193 : LogBox := ⟨![(14463/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(8035/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data193 : S1TaylorBoxData := ⟨box193,![exp24,exp18,exp10],![exp26,exp22,exp18],![exp25,exp20,exp14]⟩
theorem data193_lower_valid : ∀ j, (data193.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data193_upper_valid : ∀ j, (data193.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data193_center_valid : ∀ j, (data193.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin193 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data193 25 := by decide +kernel
theorem positive193 {q : EdgeTriple} (hq : q ∈ box193.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data193 25
    data193_lower_valid data193_upper_valid data193_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin193 hq

def box194 : LogBox := ⟨![(1607/1024 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(8035/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data194 : S1TaylorBoxData := ⟨box194,![exp22,exp18,exp18],![exp26,exp22,exp22],![exp24,exp20,exp20]⟩
theorem data194_lower_valid : ∀ j, (data194.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data194_upper_valid : ∀ j, (data194.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data194_center_valid : ∀ j, (data194.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin194 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data194 25 := by decide +kernel
theorem positive194 {q : EdgeTriple} (hq : q ∈ box194.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data194 25
    data194_lower_valid data194_upper_valid data194_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin194 hq

def box195 : LogBox := ⟨![(8035/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(17677/8192 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data195 : S1TaylorBoxData := ⟨box195,![exp26,exp10,exp10],![exp28,exp14,exp14],![exp27,exp12,exp12]⟩
theorem data195_lower_valid : ∀ j, (data195.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data195_upper_valid : ∀ j, (data195.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data195_center_valid : ∀ j, (data195.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp12_valid
  · exact exp12_valid
theorem margin195 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data195 25 := by decide +kernel
theorem positive195 {q : EdgeTriple} (hq : q ∈ box195.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data195 25
    data195_lower_valid data195_upper_valid data195_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin195 hq

def box196 : LogBox := ⟨![(8035/4096 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)],![(17677/8192 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data196 : S1TaylorBoxData := ⟨box196,![exp26,exp14,exp10],![exp28,exp18,exp18],![exp27,exp16,exp14]⟩
theorem data196_lower_valid : ∀ j, (data196.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data196_upper_valid : ∀ j, (data196.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data196_center_valid : ∀ j, (data196.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp16_valid
  · exact exp14_valid
theorem margin196 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data196 25 := by decide +kernel
theorem positive196 {q : EdgeTriple} (hq : q ∈ box196.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data196 25
    data196_lower_valid data196_upper_valid data196_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin196 hq

def box197 : LogBox := ⟨![(17677/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(4821/2048 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data197 : S1TaylorBoxData := ⟨box197,![exp28,exp10,exp10],![exp30,exp18,exp18],![exp29,exp14,exp14]⟩
theorem data197_lower_valid : ∀ j, (data197.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data197_upper_valid : ∀ j, (data197.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data197_center_valid : ∀ j, (data197.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin197 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data197 25 := by decide +kernel
theorem positive197 {q : EdgeTriple} (hq : q ∈ box197.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data197 25
    data197_lower_valid data197_upper_valid data197_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin197 hq

def box198 : LogBox := ⟨![(8035/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(4821/2048 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data198 : S1TaylorBoxData := ⟨box198,![exp26,exp18,exp10],![exp30,exp22,exp18],![exp28,exp20,exp14]⟩
theorem data198_lower_valid : ∀ j, (data198.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data198_upper_valid : ∀ j, (data198.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data198_center_valid : ∀ j, (data198.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin198 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data198 25 := by decide +kernel
theorem positive198 {q : EdgeTriple} (hq : q ∈ box198.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data198 25
    data198_lower_valid data198_upper_valid data198_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin198 hq

def box199 : LogBox := ⟨![(8035/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data199 : S1TaylorBoxData := ⟨box199,![exp26,exp18,exp18],![exp30,exp22,exp22],![exp28,exp20,exp20]⟩
theorem data199_lower_valid : ∀ j, (data199.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data199_upper_valid : ∀ j, (data199.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data199_center_valid : ∀ j, (data199.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin199 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data199 25 := by decide +kernel
theorem positive199 {q : EdgeTriple} (hq : q ∈ box199.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data199 25
    data199_lower_valid data199_upper_valid data199_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin199 hq

def box200 : LogBox := ⟨![(4821/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(20891/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data200 : S1TaylorBoxData := ⟨box200,![exp30,exp0,exp0],![exp32,exp2,exp2],![exp31,exp1,exp1]⟩
theorem data200_lower_valid : ∀ j, (data200.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data200_upper_valid : ∀ j, (data200.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data200_center_valid : ∀ j, (data200.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin200 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data200 25 := by decide +kernel
theorem positive200 {q : EdgeTriple} (hq : q ∈ box200.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data200 25
    data200_lower_valid data200_upper_valid data200_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin200 hq

def box201 : LogBox := ⟨![(4821/2048 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(20891/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data201 : S1TaylorBoxData := ⟨box201,![exp30,exp2,exp0],![exp32,exp4,exp2],![exp31,exp3,exp1]⟩
theorem data201_lower_valid : ∀ j, (data201.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data201_upper_valid : ∀ j, (data201.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data201_center_valid : ∀ j, (data201.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin201 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data201 25 := by decide +kernel
theorem positive201 {q : EdgeTriple} (hq : q ∈ box201.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data201 25
    data201_lower_valid data201_upper_valid data201_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin201 hq

def box202 : LogBox := ⟨![(4821/2048 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(20891/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data202 : S1TaylorBoxData := ⟨box202,![exp30,exp2,exp2],![exp32,exp4,exp4],![exp31,exp3,exp3]⟩
theorem data202_lower_valid : ∀ j, (data202.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data202_upper_valid : ∀ j, (data202.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data202_center_valid : ∀ j, (data202.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin202 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data202 25 := by decide +kernel
theorem positive202 {q : EdgeTriple} (hq : q ∈ box202.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data202 25
    data202_lower_valid data202_upper_valid data202_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin202 hq

def box203 : LogBox := ⟨![(20891/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data203 : S1TaylorBoxData := ⟨box203,![exp32,exp0,exp0],![exp34,exp2,exp2],![exp33,exp1,exp1]⟩
theorem data203_lower_valid : ∀ j, (data203.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data203_upper_valid : ∀ j, (data203.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data203_center_valid : ∀ j, (data203.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin203 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data203 25 := by decide +kernel
theorem positive203 {q : EdgeTriple} (hq : q ∈ box203.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data203 25
    data203_lower_valid data203_upper_valid data203_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin203 hq

def box204 : LogBox := ⟨![(20891/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data204 : S1TaylorBoxData := ⟨box204,![exp32,exp2,exp0],![exp34,exp4,exp2],![exp33,exp3,exp1]⟩
theorem data204_lower_valid : ∀ j, (data204.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data204_upper_valid : ∀ j, (data204.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data204_center_valid : ∀ j, (data204.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin204 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data204 25 := by decide +kernel
theorem positive204 {q : EdgeTriple} (hq : q ∈ box204.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data204 25
    data204_lower_valid data204_upper_valid data204_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin204 hq

def box205 : LogBox := ⟨![(20891/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(11249/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data205 : S1TaylorBoxData := ⟨box205,![exp32,exp2,exp2],![exp34,exp4,exp4],![exp33,exp3,exp3]⟩
theorem data205_lower_valid : ∀ j, (data205.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data205_upper_valid : ∀ j, (data205.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data205_center_valid : ∀ j, (data205.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin205 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data205 25 := by decide +kernel
theorem positive205 {q : EdgeTriple} (hq : q ∈ box205.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data205 25
    data205_lower_valid data205_upper_valid data205_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin205 hq

def box206 : LogBox := ⟨![(4821/2048 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(20891/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data206 : S1TaylorBoxData := ⟨box206,![exp30,exp4,exp0],![exp32,exp6,exp2],![exp31,exp5,exp1]⟩
theorem data206_lower_valid : ∀ j, (data206.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data206_upper_valid : ∀ j, (data206.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data206_center_valid : ∀ j, (data206.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin206 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data206 25 := by decide +kernel
theorem positive206 {q : EdgeTriple} (hq : q ∈ box206.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data206 25
    data206_lower_valid data206_upper_valid data206_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin206 hq

def box207 : LogBox := ⟨![(4821/2048 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(20891/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data207 : S1TaylorBoxData := ⟨box207,![exp30,exp4,exp2],![exp32,exp6,exp4],![exp31,exp5,exp3]⟩
theorem data207_lower_valid : ∀ j, (data207.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data207_upper_valid : ∀ j, (data207.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data207_center_valid : ∀ j, (data207.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin207 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data207 25 := by decide +kernel
theorem positive207 {q : EdgeTriple} (hq : q ∈ box207.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data207 25
    data207_lower_valid data207_upper_valid data207_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin207 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

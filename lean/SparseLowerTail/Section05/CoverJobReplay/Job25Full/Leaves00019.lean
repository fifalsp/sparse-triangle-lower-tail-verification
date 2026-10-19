import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box304 : LogBox := ⟨![(8035/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(4821/2048 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data304 : S1TaylorBoxData := ⟨box304,![exp26,exp22,exp22],![exp30,exp26,exp26],![exp28,exp24,exp24]⟩
theorem data304_lower_valid : ∀ j, (data304.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data304_upper_valid : ∀ j, (data304.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data304_center_valid : ∀ j, (data304.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin304 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data304 25 := by decide +kernel
theorem positive304 {q : EdgeTriple} (hq : q ∈ box304.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data304 25
    data304_lower_valid data304_upper_valid data304_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin304 hq

def box305 : LogBox := ⟨![(8035/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(4821/2048 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data305 : S1TaylorBoxData := ⟨box305,![exp26,exp26,exp22],![exp30,exp30,exp30],![exp28,exp28,exp26]⟩
theorem data305_lower_valid : ∀ j, (data305.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data305_upper_valid : ∀ j, (data305.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data305_center_valid : ∀ j, (data305.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin305 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data305 25 := by decide +kernel
theorem positive305 {q : EdgeTriple} (hq : q ∈ box305.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data305 25
    data305_lower_valid data305_upper_valid data305_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin305 hq

def box306 : LogBox := ⟨![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(11249/4096 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data306 : S1TaylorBoxData := ⟨box306,![exp30,exp22,exp22],![exp34,exp26,exp26],![exp32,exp24,exp24]⟩
theorem data306_lower_valid : ∀ j, (data306.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data306_upper_valid : ∀ j, (data306.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data306_center_valid : ∀ j, (data306.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin306 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data306 25 := by decide +kernel
theorem positive306 {q : EdgeTriple} (hq : q ∈ box306.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data306 25
    data306_lower_valid data306_upper_valid data306_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin306 hq

def box307 : LogBox := ⟨![(4821/2048 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(11249/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data307 : S1TaylorBoxData := ⟨box307,![exp30,exp26,exp22],![exp34,exp30,exp30],![exp32,exp28,exp26]⟩
theorem data307_lower_valid : ∀ j, (data307.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data307_upper_valid : ∀ j, (data307.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data307_center_valid : ∀ j, (data307.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin307 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data307 25 := by decide +kernel
theorem positive307 {q : EdgeTriple} (hq : q ∈ box307.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data307 25
    data307_lower_valid data307_upper_valid data307_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin307 hq

def box308 : LogBox := ⟨![(11249/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(1607/512 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data308 : S1TaylorBoxData := ⟨box308,![exp34,exp22,exp22],![exp38,exp26,exp26],![exp36,exp24,exp24]⟩
theorem data308_lower_valid : ∀ j, (data308.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data308_upper_valid : ∀ j, (data308.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data308_center_valid : ∀ j, (data308.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin308 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data308 25 := by decide +kernel
theorem positive308 {q : EdgeTriple} (hq : q ∈ box308.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data308 25
    data308_lower_valid data308_upper_valid data308_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin308 hq

def box309 : LogBox := ⟨![(11249/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(1607/512 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data309 : S1TaylorBoxData := ⟨box309,![exp34,exp26,exp22],![exp38,exp30,exp30],![exp36,exp28,exp26]⟩
theorem data309_lower_valid : ∀ j, (data309.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data309_upper_valid : ∀ j, (data309.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data309_center_valid : ∀ j, (data309.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin309 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data309 25 := by decide +kernel
theorem positive309 {q : EdgeTriple} (hq : q ∈ box309.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data309 25
    data309_lower_valid data309_upper_valid data309_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin309 hq

def box310 : LogBox := ⟨![(4821/2048 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(11249/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data310 : S1TaylorBoxData := ⟨box310,![exp30,exp30,exp22],![exp34,exp34,exp30],![exp32,exp32,exp26]⟩
theorem data310_lower_valid : ∀ j, (data310.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data310_upper_valid : ∀ j, (data310.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data310_center_valid : ∀ j, (data310.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin310 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data310 25 := by decide +kernel
theorem positive310 {q : EdgeTriple} (hq : q ∈ box310.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data310 25
    data310_lower_valid data310_upper_valid data310_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin310 hq

def box311 : LogBox := ⟨![(11249/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(1607/512 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data311 : S1TaylorBoxData := ⟨box311,![exp34,exp30,exp22],![exp38,exp34,exp30],![exp36,exp32,exp26]⟩
theorem data311_lower_valid : ∀ j, (data311.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data311_upper_valid : ∀ j, (data311.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data311_center_valid : ∀ j, (data311.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin311 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data311 25 := by decide +kernel
theorem positive311 {q : EdgeTriple} (hq : q ∈ box311.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data311 25
    data311_lower_valid data311_upper_valid data311_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin311 hq

def box312 : LogBox := ⟨![(11249/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data312 : S1TaylorBoxData := ⟨box312,![exp34,exp34,exp22],![exp38,exp38,exp30],![exp36,exp36,exp26]⟩
theorem data312_lower_valid : ∀ j, (data312.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data312_upper_valid : ∀ j, (data312.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data312_center_valid : ∀ j, (data312.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin312 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data312 25 := by decide +kernel
theorem positive312 {q : EdgeTriple} (hq : q ∈ box312.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data312 25
    data312_lower_valid data312_upper_valid data312_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin312 hq

def box313 : LogBox := ⟨![(4821/2048 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(11249/4096 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data313 : S1TaylorBoxData := ⟨box313,![exp30,exp30,exp30],![exp34,exp34,exp34],![exp32,exp32,exp32]⟩
theorem data313_lower_valid : ∀ j, (data313.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data313_upper_valid : ∀ j, (data313.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data313_center_valid : ∀ j, (data313.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin313 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data313 25 := by decide +kernel
theorem positive313 {q : EdgeTriple} (hq : q ∈ box313.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data313 25
    data313_lower_valid data313_upper_valid data313_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin313 hq

def box314 : LogBox := ⟨![(11249/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(1607/512 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data314 : S1TaylorBoxData := ⟨box314,![exp34,exp30,exp30],![exp38,exp34,exp34],![exp36,exp32,exp32]⟩
theorem data314_lower_valid : ∀ j, (data314.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data314_upper_valid : ∀ j, (data314.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data314_center_valid : ∀ j, (data314.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin314 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data314 25 := by decide +kernel
theorem positive314 {q : EdgeTriple} (hq : q ∈ box314.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data314 25
    data314_lower_valid data314_upper_valid data314_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin314 hq

def box315 : LogBox := ⟨![(11249/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data315 : S1TaylorBoxData := ⟨box315,![exp34,exp34,exp30],![exp38,exp38,exp38],![exp36,exp36,exp34]⟩
theorem data315_lower_valid : ∀ j, (data315.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data315_upper_valid : ∀ j, (data315.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data315_center_valid : ∀ j, (data315.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin315 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data315 25 := by decide +kernel
theorem positive315 {q : EdgeTriple} (hq : q ∈ box315.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data315 25
    data315_lower_valid data315_upper_valid data315_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin315 hq

def box316 : LogBox := ⟨![(1607/512 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(27319/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data316 : S1TaylorBoxData := ⟨box316,![exp38,exp0,exp0],![exp40,exp2,exp2],![exp39,exp1,exp1]⟩
theorem data316_lower_valid : ∀ j, (data316.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data316_upper_valid : ∀ j, (data316.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data316_center_valid : ∀ j, (data316.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin316 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data316 25 := by decide +kernel
theorem positive316 {q : EdgeTriple} (hq : q ∈ box316.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data316 25
    data316_lower_valid data316_upper_valid data316_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin316 hq

def box317 : LogBox := ⟨![(1607/512 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(27319/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data317 : S1TaylorBoxData := ⟨box317,![exp38,exp2,exp0],![exp40,exp4,exp4],![exp39,exp3,exp2]⟩
theorem data317_lower_valid : ∀ j, (data317.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data317_upper_valid : ∀ j, (data317.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data317_center_valid : ∀ j, (data317.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin317 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data317 25 := by decide +kernel
theorem positive317 {q : EdgeTriple} (hq : q ∈ box317.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data317 25
    data317_lower_valid data317_upper_valid data317_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin317 hq

def box318 : LogBox := ⟨![(27319/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data318 : S1TaylorBoxData := ⟨box318,![exp40,exp0,exp0],![exp42,exp2,exp2],![exp41,exp1,exp1]⟩
theorem data318_lower_valid : ∀ j, (data318.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data318_upper_valid : ∀ j, (data318.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data318_center_valid : ∀ j, (data318.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin318 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data318 25 := by decide +kernel
theorem positive318 {q : EdgeTriple} (hq : q ∈ box318.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data318 25
    data318_lower_valid data318_upper_valid data318_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin318 hq

def box319 : LogBox := ⟨![(27319/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data319 : S1TaylorBoxData := ⟨box319,![exp40,exp2,exp0],![exp42,exp4,exp4],![exp41,exp3,exp2]⟩
theorem data319_lower_valid : ∀ j, (data319.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data319_upper_valid : ∀ j, (data319.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data319_center_valid : ∀ j, (data319.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin319 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data319 25 := by decide +kernel
theorem positive319 {q : EdgeTriple} (hq : q ∈ box319.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data319 25
    data319_lower_valid data319_upper_valid data319_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin319 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

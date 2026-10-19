import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box288 : LogBox := ⟨![(11249/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(1607/512 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data288 : S1TaylorBoxData := ⟨box288,![exp34,exp22,exp18],![exp38,exp26,exp22],![exp36,exp24,exp20]⟩
theorem data288_lower_valid : ∀ j, (data288.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data288_upper_valid : ∀ j, (data288.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data288_center_valid : ∀ j, (data288.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin288 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data288 25 := by decide +kernel
theorem positive288 {q : EdgeTriple} (hq : q ∈ box288.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data288 25
    data288_lower_valid data288_upper_valid data288_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin288 hq

def box289 : LogBox := ⟨![(11249/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(1607/512 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data289 : S1TaylorBoxData := ⟨box289,![exp34,exp26,exp10],![exp38,exp30,exp18],![exp36,exp28,exp14]⟩
theorem data289_lower_valid : ∀ j, (data289.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data289_upper_valid : ∀ j, (data289.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data289_center_valid : ∀ j, (data289.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin289 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data289 25 := by decide +kernel
theorem positive289 {q : EdgeTriple} (hq : q ∈ box289.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data289 25
    data289_lower_valid data289_upper_valid data289_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin289 hq

def box290 : LogBox := ⟨![(11249/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(1607/512 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data290 : S1TaylorBoxData := ⟨box290,![exp34,exp26,exp18],![exp38,exp30,exp22],![exp36,exp28,exp20]⟩
theorem data290_lower_valid : ∀ j, (data290.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data290_upper_valid : ∀ j, (data290.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data290_center_valid : ∀ j, (data290.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin290 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data290 25 := by decide +kernel
theorem positive290 {q : EdgeTriple} (hq : q ∈ box290.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data290 25
    data290_lower_valid data290_upper_valid data290_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin290 hq

def box291 : LogBox := ⟨![(4821/2048 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data291 : S1TaylorBoxData := ⟨box291,![exp30,exp30,exp0],![exp34,exp34,exp4],![exp32,exp32,exp2]⟩
theorem data291_lower_valid : ∀ j, (data291.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data291_upper_valid : ∀ j, (data291.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data291_center_valid : ∀ j, (data291.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin291 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data291 25 := by decide +kernel
theorem positive291 {q : EdgeTriple} (hq : q ∈ box291.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data291 25
    data291_lower_valid data291_upper_valid data291_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin291 hq

def box292 : LogBox := ⟨![(4821/2048 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data292 : S1TaylorBoxData := ⟨box292,![exp30,exp30,exp4],![exp34,exp34,exp10],![exp32,exp32,exp6]⟩
theorem data292_lower_valid : ∀ j, (data292.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data292_upper_valid : ∀ j, (data292.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data292_center_valid : ∀ j, (data292.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin292 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data292 25 := by decide +kernel
theorem positive292 {q : EdgeTriple} (hq : q ∈ box292.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data292 25
    data292_lower_valid data292_upper_valid data292_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin292 hq

def box293 : LogBox := ⟨![(11249/4096 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data293 : S1TaylorBoxData := ⟨box293,![exp34,exp30,exp0],![exp38,exp34,exp4],![exp36,exp32,exp2]⟩
theorem data293_lower_valid : ∀ j, (data293.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data293_upper_valid : ∀ j, (data293.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data293_center_valid : ∀ j, (data293.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin293 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data293 25 := by decide +kernel
theorem positive293 {q : EdgeTriple} (hq : q ∈ box293.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data293 25
    data293_lower_valid data293_upper_valid data293_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin293 hq

def box294 : LogBox := ⟨![(11249/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data294 : S1TaylorBoxData := ⟨box294,![exp34,exp30,exp4],![exp38,exp34,exp10],![exp36,exp32,exp6]⟩
theorem data294_lower_valid : ∀ j, (data294.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data294_upper_valid : ∀ j, (data294.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data294_center_valid : ∀ j, (data294.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin294 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data294 25 := by decide +kernel
theorem positive294 {q : EdgeTriple} (hq : q ∈ box294.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data294 25
    data294_lower_valid data294_upper_valid data294_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin294 hq

def box295 : LogBox := ⟨![(11249/4096 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data295 : S1TaylorBoxData := ⟨box295,![exp34,exp34,exp0],![exp38,exp38,exp4],![exp36,exp36,exp2]⟩
theorem data295_lower_valid : ∀ j, (data295.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data295_upper_valid : ∀ j, (data295.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data295_center_valid : ∀ j, (data295.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin295 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data295 25 := by decide +kernel
theorem positive295 {q : EdgeTriple} (hq : q ∈ box295.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data295 25
    data295_lower_valid data295_upper_valid data295_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin295 hq

def box296 : LogBox := ⟨![(11249/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data296 : S1TaylorBoxData := ⟨box296,![exp34,exp34,exp4],![exp38,exp38,exp10],![exp36,exp36,exp6]⟩
theorem data296_lower_valid : ∀ j, (data296.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data296_upper_valid : ∀ j, (data296.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data296_center_valid : ∀ j, (data296.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin296 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data296 25 := by decide +kernel
theorem positive296 {q : EdgeTriple} (hq : q ∈ box296.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data296 25
    data296_lower_valid data296_upper_valid data296_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin296 hq

def box297 : LogBox := ⟨![(4821/2048 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(11249/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data297 : S1TaylorBoxData := ⟨box297,![exp30,exp30,exp10],![exp34,exp34,exp18],![exp32,exp32,exp14]⟩
theorem data297_lower_valid : ∀ j, (data297.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data297_upper_valid : ∀ j, (data297.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data297_center_valid : ∀ j, (data297.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin297 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data297 25 := by decide +kernel
theorem positive297 {q : EdgeTriple} (hq : q ∈ box297.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data297 25
    data297_lower_valid data297_upper_valid data297_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin297 hq

def box298 : LogBox := ⟨![(4821/2048 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(11249/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data298 : S1TaylorBoxData := ⟨box298,![exp30,exp30,exp18],![exp34,exp34,exp22],![exp32,exp32,exp20]⟩
theorem data298_lower_valid : ∀ j, (data298.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data298_upper_valid : ∀ j, (data298.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data298_center_valid : ∀ j, (data298.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin298 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data298 25 := by decide +kernel
theorem positive298 {q : EdgeTriple} (hq : q ∈ box298.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data298 25
    data298_lower_valid data298_upper_valid data298_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin298 hq

def box299 : LogBox := ⟨![(11249/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(1607/512 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data299 : S1TaylorBoxData := ⟨box299,![exp34,exp30,exp10],![exp38,exp34,exp18],![exp36,exp32,exp14]⟩
theorem data299_lower_valid : ∀ j, (data299.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data299_upper_valid : ∀ j, (data299.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data299_center_valid : ∀ j, (data299.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin299 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data299 25 := by decide +kernel
theorem positive299 {q : EdgeTriple} (hq : q ∈ box299.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data299 25
    data299_lower_valid data299_upper_valid data299_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin299 hq

def box300 : LogBox := ⟨![(11249/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(1607/512 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data300 : S1TaylorBoxData := ⟨box300,![exp34,exp30,exp18],![exp38,exp34,exp22],![exp36,exp32,exp20]⟩
theorem data300_lower_valid : ∀ j, (data300.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data300_upper_valid : ∀ j, (data300.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data300_center_valid : ∀ j, (data300.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin300 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data300 25 := by decide +kernel
theorem positive300 {q : EdgeTriple} (hq : q ∈ box300.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data300 25
    data300_lower_valid data300_upper_valid data300_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin300 hq

def box301 : LogBox := ⟨![(11249/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data301 : S1TaylorBoxData := ⟨box301,![exp34,exp34,exp10],![exp38,exp38,exp18],![exp36,exp36,exp14]⟩
theorem data301_lower_valid : ∀ j, (data301.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data301_upper_valid : ∀ j, (data301.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data301_center_valid : ∀ j, (data301.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin301 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data301 25 := by decide +kernel
theorem positive301 {q : EdgeTriple} (hq : q ∈ box301.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data301 25
    data301_lower_valid data301_upper_valid data301_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin301 hq

def box302 : LogBox := ⟨![(11249/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(1607/512 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data302 : S1TaylorBoxData := ⟨box302,![exp34,exp34,exp18],![exp38,exp38,exp22],![exp36,exp36,exp20]⟩
theorem data302_lower_valid : ∀ j, (data302.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data302_upper_valid : ∀ j, (data302.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data302_center_valid : ∀ j, (data302.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin302 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data302 25 := by decide +kernel
theorem positive302 {q : EdgeTriple} (hq : q ∈ box302.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data302 25
    data302_lower_valid data302_upper_valid data302_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin302 hq

def box303 : LogBox := ⟨![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(8035/4096 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data303 : S1TaylorBoxData := ⟨box303,![exp22,exp22,exp22],![exp26,exp26,exp26],![exp24,exp24,exp24]⟩
theorem data303_lower_valid : ∀ j, (data303.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data303_upper_valid : ∀ j, (data303.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data303_center_valid : ∀ j, (data303.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin303 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data303 25 := by decide +kernel
theorem positive303 {q : EdgeTriple} (hq : q ∈ box303.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data303 25
    data303_lower_valid data303_upper_valid data303_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin303 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

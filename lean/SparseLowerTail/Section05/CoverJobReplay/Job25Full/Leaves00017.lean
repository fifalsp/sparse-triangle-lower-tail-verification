import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box272 : LogBox := ⟨![(8035/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(4821/2048 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data272 : S1TaylorBoxData := ⟨box272,![exp26,exp22,exp18],![exp30,exp26,exp22],![exp28,exp24,exp20]⟩
theorem data272_lower_valid : ∀ j, (data272.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data272_upper_valid : ∀ j, (data272.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data272_center_valid : ∀ j, (data272.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin272 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data272 25 := by decide +kernel
theorem positive272 {q : EdgeTriple} (hq : q ∈ box272.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data272 25
    data272_lower_valid data272_upper_valid data272_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin272 hq

def box273 : LogBox := ⟨![(8035/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(4821/2048 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data273 : S1TaylorBoxData := ⟨box273,![exp26,exp26,exp10],![exp30,exp30,exp18],![exp28,exp28,exp14]⟩
theorem data273_lower_valid : ∀ j, (data273.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data273_upper_valid : ∀ j, (data273.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data273_center_valid : ∀ j, (data273.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin273 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data273 25 := by decide +kernel
theorem positive273 {q : EdgeTriple} (hq : q ∈ box273.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data273 25
    data273_lower_valid data273_upper_valid data273_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin273 hq

def box274 : LogBox := ⟨![(8035/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(4821/2048 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data274 : S1TaylorBoxData := ⟨box274,![exp26,exp26,exp18],![exp30,exp30,exp22],![exp28,exp28,exp20]⟩
theorem data274_lower_valid : ∀ j, (data274.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data274_upper_valid : ∀ j, (data274.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data274_center_valid : ∀ j, (data274.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin274 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data274 25 := by decide +kernel
theorem positive274 {q : EdgeTriple} (hq : q ∈ box274.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data274 25
    data274_lower_valid data274_upper_valid data274_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin274 hq

def box275 : LogBox := ⟨![(4821/2048 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data275 : S1TaylorBoxData := ⟨box275,![exp30,exp22,exp0],![exp34,exp26,exp4],![exp32,exp24,exp2]⟩
theorem data275_lower_valid : ∀ j, (data275.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data275_upper_valid : ∀ j, (data275.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data275_center_valid : ∀ j, (data275.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin275 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data275 25 := by decide +kernel
theorem positive275 {q : EdgeTriple} (hq : q ∈ box275.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data275 25
    data275_lower_valid data275_upper_valid data275_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin275 hq

def box276 : LogBox := ⟨![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data276 : S1TaylorBoxData := ⟨box276,![exp30,exp22,exp4],![exp34,exp26,exp10],![exp32,exp24,exp6]⟩
theorem data276_lower_valid : ∀ j, (data276.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data276_upper_valid : ∀ j, (data276.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data276_center_valid : ∀ j, (data276.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin276 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data276 25 := by decide +kernel
theorem positive276 {q : EdgeTriple} (hq : q ∈ box276.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data276 25
    data276_lower_valid data276_upper_valid data276_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin276 hq

def box277 : LogBox := ⟨![(4821/2048 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data277 : S1TaylorBoxData := ⟨box277,![exp30,exp26,exp0],![exp34,exp30,exp4],![exp32,exp28,exp2]⟩
theorem data277_lower_valid : ∀ j, (data277.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data277_upper_valid : ∀ j, (data277.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data277_center_valid : ∀ j, (data277.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin277 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data277 25 := by decide +kernel
theorem positive277 {q : EdgeTriple} (hq : q ∈ box277.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data277 25
    data277_lower_valid data277_upper_valid data277_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin277 hq

def box278 : LogBox := ⟨![(4821/2048 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data278 : S1TaylorBoxData := ⟨box278,![exp30,exp26,exp4],![exp34,exp30,exp10],![exp32,exp28,exp6]⟩
theorem data278_lower_valid : ∀ j, (data278.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data278_upper_valid : ∀ j, (data278.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data278_center_valid : ∀ j, (data278.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin278 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data278 25 := by decide +kernel
theorem positive278 {q : EdgeTriple} (hq : q ∈ box278.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data278 25
    data278_lower_valid data278_upper_valid data278_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin278 hq

def box279 : LogBox := ⟨![(11249/4096 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data279 : S1TaylorBoxData := ⟨box279,![exp34,exp22,exp0],![exp38,exp26,exp4],![exp36,exp24,exp2]⟩
theorem data279_lower_valid : ∀ j, (data279.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data279_upper_valid : ∀ j, (data279.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data279_center_valid : ∀ j, (data279.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin279 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data279 25 := by decide +kernel
theorem positive279 {q : EdgeTriple} (hq : q ∈ box279.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data279 25
    data279_lower_valid data279_upper_valid data279_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin279 hq

def box280 : LogBox := ⟨![(11249/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data280 : S1TaylorBoxData := ⟨box280,![exp34,exp22,exp4],![exp38,exp26,exp10],![exp36,exp24,exp6]⟩
theorem data280_lower_valid : ∀ j, (data280.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data280_upper_valid : ∀ j, (data280.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data280_center_valid : ∀ j, (data280.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin280 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data280 25 := by decide +kernel
theorem positive280 {q : EdgeTriple} (hq : q ∈ box280.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data280 25
    data280_lower_valid data280_upper_valid data280_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin280 hq

def box281 : LogBox := ⟨![(11249/4096 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data281 : S1TaylorBoxData := ⟨box281,![exp34,exp26,exp0],![exp38,exp30,exp4],![exp36,exp28,exp2]⟩
theorem data281_lower_valid : ∀ j, (data281.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data281_upper_valid : ∀ j, (data281.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data281_center_valid : ∀ j, (data281.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin281 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data281 25 := by decide +kernel
theorem positive281 {q : EdgeTriple} (hq : q ∈ box281.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data281 25
    data281_lower_valid data281_upper_valid data281_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin281 hq

def box282 : LogBox := ⟨![(11249/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data282 : S1TaylorBoxData := ⟨box282,![exp34,exp26,exp4],![exp38,exp30,exp10],![exp36,exp28,exp6]⟩
theorem data282_lower_valid : ∀ j, (data282.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data282_upper_valid : ∀ j, (data282.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data282_center_valid : ∀ j, (data282.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin282 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data282 25 := by decide +kernel
theorem positive282 {q : EdgeTriple} (hq : q ∈ box282.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data282 25
    data282_lower_valid data282_upper_valid data282_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin282 hq

def box283 : LogBox := ⟨![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(11249/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data283 : S1TaylorBoxData := ⟨box283,![exp30,exp22,exp10],![exp34,exp26,exp18],![exp32,exp24,exp14]⟩
theorem data283_lower_valid : ∀ j, (data283.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data283_upper_valid : ∀ j, (data283.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data283_center_valid : ∀ j, (data283.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin283 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data283 25 := by decide +kernel
theorem positive283 {q : EdgeTriple} (hq : q ∈ box283.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data283 25
    data283_lower_valid data283_upper_valid data283_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin283 hq

def box284 : LogBox := ⟨![(4821/2048 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(11249/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data284 : S1TaylorBoxData := ⟨box284,![exp30,exp22,exp18],![exp34,exp26,exp22],![exp32,exp24,exp20]⟩
theorem data284_lower_valid : ∀ j, (data284.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data284_upper_valid : ∀ j, (data284.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data284_center_valid : ∀ j, (data284.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin284 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data284 25 := by decide +kernel
theorem positive284 {q : EdgeTriple} (hq : q ∈ box284.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data284 25
    data284_lower_valid data284_upper_valid data284_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin284 hq

def box285 : LogBox := ⟨![(4821/2048 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(11249/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data285 : S1TaylorBoxData := ⟨box285,![exp30,exp26,exp10],![exp34,exp30,exp18],![exp32,exp28,exp14]⟩
theorem data285_lower_valid : ∀ j, (data285.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data285_upper_valid : ∀ j, (data285.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data285_center_valid : ∀ j, (data285.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin285 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data285 25 := by decide +kernel
theorem positive285 {q : EdgeTriple} (hq : q ∈ box285.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data285 25
    data285_lower_valid data285_upper_valid data285_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin285 hq

def box286 : LogBox := ⟨![(4821/2048 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(11249/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data286 : S1TaylorBoxData := ⟨box286,![exp30,exp26,exp18],![exp34,exp30,exp22],![exp32,exp28,exp20]⟩
theorem data286_lower_valid : ∀ j, (data286.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data286_upper_valid : ∀ j, (data286.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data286_center_valid : ∀ j, (data286.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin286 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data286 25 := by decide +kernel
theorem positive286 {q : EdgeTriple} (hq : q ∈ box286.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data286 25
    data286_lower_valid data286_upper_valid data286_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin286 hq

def box287 : LogBox := ⟨![(11249/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(1607/512 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data287 : S1TaylorBoxData := ⟨box287,![exp34,exp22,exp10],![exp38,exp26,exp18],![exp36,exp24,exp14]⟩
theorem data287_lower_valid : ∀ j, (data287.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data287_upper_valid : ∀ j, (data287.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data287_center_valid : ∀ j, (data287.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin287 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data287 25 := by decide +kernel
theorem positive287 {q : EdgeTriple} (hq : q ∈ box287.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data287 25
    data287_lower_valid data287_upper_valid data287_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin287 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

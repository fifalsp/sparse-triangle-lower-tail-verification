import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box448 : LogBox := ⟨![(17677/4096 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data448 : S1TaylorBoxData := ⟨box448,![exp50,exp30,exp0],![exp54,exp34,exp4],![exp52,exp32,exp2]⟩
theorem data448_lower_valid : ∀ j, (data448.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data448_upper_valid : ∀ j, (data448.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data448_center_valid : ∀ j, (data448.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin448 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data448 25 := by decide +kernel
theorem positive448 {q : EdgeTriple} (hq : q ∈ box448.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data448 25
    data448_lower_valid data448_upper_valid data448_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin448 hq

def box449 : LogBox := ⟨![(17677/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data449 : S1TaylorBoxData := ⟨box449,![exp50,exp30,exp4],![exp54,exp34,exp10],![exp52,exp32,exp6]⟩
theorem data449_lower_valid : ∀ j, (data449.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data449_upper_valid : ∀ j, (data449.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data449_center_valid : ∀ j, (data449.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin449 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data449 25 := by decide +kernel
theorem positive449 {q : EdgeTriple} (hq : q ∈ box449.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data449 25
    data449_lower_valid data449_upper_valid data449_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin449 hq

def box450 : LogBox := ⟨![(17677/4096 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data450 : S1TaylorBoxData := ⟨box450,![exp50,exp34,exp0],![exp54,exp38,exp4],![exp52,exp36,exp2]⟩
theorem data450_lower_valid : ∀ j, (data450.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data450_upper_valid : ∀ j, (data450.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data450_center_valid : ∀ j, (data450.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin450 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data450 25 := by decide +kernel
theorem positive450 {q : EdgeTriple} (hq : q ∈ box450.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data450 25
    data450_lower_valid data450_upper_valid data450_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin450 hq

def box451 : LogBox := ⟨![(17677/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data451 : S1TaylorBoxData := ⟨box451,![exp50,exp34,exp4],![exp54,exp38,exp10],![exp52,exp36,exp6]⟩
theorem data451_lower_valid : ∀ j, (data451.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data451_upper_valid : ∀ j, (data451.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data451_center_valid : ∀ j, (data451.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin451 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data451 25 := by decide +kernel
theorem positive451 {q : EdgeTriple} (hq : q ∈ box451.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data451 25
    data451_lower_valid data451_upper_valid data451_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin451 hq

def box452 : LogBox := ⟨![(8035/2048 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data452 : S1TaylorBoxData := ⟨box452,![exp46,exp30,exp10],![exp50,exp34,exp18],![exp48,exp32,exp14]⟩
theorem data452_lower_valid : ∀ j, (data452.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data452_upper_valid : ∀ j, (data452.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data452_center_valid : ∀ j, (data452.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin452 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data452 25 := by decide +kernel
theorem positive452 {q : EdgeTriple} (hq : q ∈ box452.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data452 25
    data452_lower_valid data452_upper_valid data452_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin452 hq

def box453 : LogBox := ⟨![(8035/2048 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data453 : S1TaylorBoxData := ⟨box453,![exp46,exp30,exp18],![exp50,exp34,exp22],![exp48,exp32,exp20]⟩
theorem data453_lower_valid : ∀ j, (data453.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data453_upper_valid : ∀ j, (data453.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data453_center_valid : ∀ j, (data453.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin453 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data453 25 := by decide +kernel
theorem positive453 {q : EdgeTriple} (hq : q ∈ box453.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data453 25
    data453_lower_valid data453_upper_valid data453_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin453 hq

def box454 : LogBox := ⟨![(8035/2048 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data454 : S1TaylorBoxData := ⟨box454,![exp46,exp34,exp10],![exp50,exp38,exp18],![exp48,exp36,exp14]⟩
theorem data454_lower_valid : ∀ j, (data454.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data454_upper_valid : ∀ j, (data454.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data454_center_valid : ∀ j, (data454.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin454 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data454 25 := by decide +kernel
theorem positive454 {q : EdgeTriple} (hq : q ∈ box454.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data454 25
    data454_lower_valid data454_upper_valid data454_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin454 hq

def box455 : LogBox := ⟨![(8035/2048 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data455 : S1TaylorBoxData := ⟨box455,![exp46,exp34,exp18],![exp50,exp38,exp22],![exp48,exp36,exp20]⟩
theorem data455_lower_valid : ∀ j, (data455.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data455_upper_valid : ∀ j, (data455.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data455_center_valid : ∀ j, (data455.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin455 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data455 25 := by decide +kernel
theorem positive455 {q : EdgeTriple} (hq : q ∈ box455.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data455 25
    data455_lower_valid data455_upper_valid data455_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin455 hq

def box456 : LogBox := ⟨![(17677/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data456 : S1TaylorBoxData := ⟨box456,![exp50,exp30,exp10],![exp54,exp34,exp18],![exp52,exp32,exp14]⟩
theorem data456_lower_valid : ∀ j, (data456.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data456_upper_valid : ∀ j, (data456.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data456_center_valid : ∀ j, (data456.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin456 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data456 25 := by decide +kernel
theorem positive456 {q : EdgeTriple} (hq : q ∈ box456.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data456 25
    data456_lower_valid data456_upper_valid data456_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin456 hq

def box457 : LogBox := ⟨![(17677/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data457 : S1TaylorBoxData := ⟨box457,![exp50,exp30,exp18],![exp54,exp34,exp22],![exp52,exp32,exp20]⟩
theorem data457_lower_valid : ∀ j, (data457.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data457_upper_valid : ∀ j, (data457.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data457_center_valid : ∀ j, (data457.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin457 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data457 25 := by decide +kernel
theorem positive457 {q : EdgeTriple} (hq : q ∈ box457.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data457 25
    data457_lower_valid data457_upper_valid data457_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin457 hq

def box458 : LogBox := ⟨![(17677/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data458 : S1TaylorBoxData := ⟨box458,![exp50,exp34,exp10],![exp54,exp38,exp18],![exp52,exp36,exp14]⟩
theorem data458_lower_valid : ∀ j, (data458.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data458_upper_valid : ∀ j, (data458.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data458_center_valid : ∀ j, (data458.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin458 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data458 25 := by decide +kernel
theorem positive458 {q : EdgeTriple} (hq : q ∈ box458.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data458 25
    data458_lower_valid data458_upper_valid data458_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin458 hq

def box459 : LogBox := ⟨![(17677/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data459 : S1TaylorBoxData := ⟨box459,![exp50,exp34,exp18],![exp54,exp38,exp22],![exp52,exp36,exp20]⟩
theorem data459_lower_valid : ∀ j, (data459.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data459_upper_valid : ∀ j, (data459.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data459_center_valid : ∀ j, (data459.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin459 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data459 25 := by decide +kernel
theorem positive459 {q : EdgeTriple} (hq : q ∈ box459.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data459 25
    data459_lower_valid data459_upper_valid data459_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin459 hq

def box460 : LogBox := ⟨![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(14463/4096 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data460 : S1TaylorBoxData := ⟨box460,![exp38,exp22,exp22],![exp42,exp26,exp26],![exp40,exp24,exp24]⟩
theorem data460_lower_valid : ∀ j, (data460.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data460_upper_valid : ∀ j, (data460.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data460_center_valid : ∀ j, (data460.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin460 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data460 25 := by decide +kernel
theorem positive460 {q : EdgeTriple} (hq : q ∈ box460.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data460 25
    data460_lower_valid data460_upper_valid data460_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin460 hq

def box461 : LogBox := ⟨![(1607/512 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(14463/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data461 : S1TaylorBoxData := ⟨box461,![exp38,exp26,exp22],![exp42,exp30,exp30],![exp40,exp28,exp26]⟩
theorem data461_lower_valid : ∀ j, (data461.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data461_upper_valid : ∀ j, (data461.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data461_center_valid : ∀ j, (data461.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin461 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data461 25 := by decide +kernel
theorem positive461 {q : EdgeTriple} (hq : q ∈ box461.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data461 25
    data461_lower_valid data461_upper_valid data461_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin461 hq

def box462 : LogBox := ⟨![(14463/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(8035/2048 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data462 : S1TaylorBoxData := ⟨box462,![exp42,exp22,exp22],![exp46,exp26,exp26],![exp44,exp24,exp24]⟩
theorem data462_lower_valid : ∀ j, (data462.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data462_upper_valid : ∀ j, (data462.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data462_center_valid : ∀ j, (data462.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin462 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data462 25 := by decide +kernel
theorem positive462 {q : EdgeTriple} (hq : q ∈ box462.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data462 25
    data462_lower_valid data462_upper_valid data462_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin462 hq

def box463 : LogBox := ⟨![(14463/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(8035/2048 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data463 : S1TaylorBoxData := ⟨box463,![exp42,exp26,exp22],![exp46,exp30,exp30],![exp44,exp28,exp26]⟩
theorem data463_lower_valid : ∀ j, (data463.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data463_upper_valid : ∀ j, (data463.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data463_center_valid : ∀ j, (data463.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin463 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data463 25 := by decide +kernel
theorem positive463 {q : EdgeTriple} (hq : q ∈ box463.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data463 25
    data463_lower_valid data463_upper_valid data463_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin463 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box416 : LogBox := ⟨![(14463/4096 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data416 : S1TaylorBoxData := ⟨box416,![exp42,exp30,exp0],![exp46,exp34,exp4],![exp44,exp32,exp2]⟩
theorem data416_lower_valid : ∀ j, (data416.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data416_upper_valid : ∀ j, (data416.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data416_center_valid : ∀ j, (data416.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin416 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data416 25 := by decide +kernel
theorem positive416 {q : EdgeTriple} (hq : q ∈ box416.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data416 25
    data416_lower_valid data416_upper_valid data416_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin416 hq

def box417 : LogBox := ⟨![(14463/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data417 : S1TaylorBoxData := ⟨box417,![exp42,exp30,exp4],![exp46,exp34,exp10],![exp44,exp32,exp6]⟩
theorem data417_lower_valid : ∀ j, (data417.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data417_upper_valid : ∀ j, (data417.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data417_center_valid : ∀ j, (data417.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin417 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data417 25 := by decide +kernel
theorem positive417 {q : EdgeTriple} (hq : q ∈ box417.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data417 25
    data417_lower_valid data417_upper_valid data417_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin417 hq

def box418 : LogBox := ⟨![(14463/4096 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data418 : S1TaylorBoxData := ⟨box418,![exp42,exp34,exp0],![exp46,exp38,exp4],![exp44,exp36,exp2]⟩
theorem data418_lower_valid : ∀ j, (data418.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data418_upper_valid : ∀ j, (data418.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data418_center_valid : ∀ j, (data418.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin418 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data418 25 := by decide +kernel
theorem positive418 {q : EdgeTriple} (hq : q ∈ box418.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data418 25
    data418_lower_valid data418_upper_valid data418_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin418 hq

def box419 : LogBox := ⟨![(14463/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data419 : S1TaylorBoxData := ⟨box419,![exp42,exp34,exp4],![exp46,exp38,exp10],![exp44,exp36,exp6]⟩
theorem data419_lower_valid : ∀ j, (data419.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data419_upper_valid : ∀ j, (data419.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data419_center_valid : ∀ j, (data419.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin419 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data419 25 := by decide +kernel
theorem positive419 {q : EdgeTriple} (hq : q ∈ box419.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data419 25
    data419_lower_valid data419_upper_valid data419_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin419 hq

def box420 : LogBox := ⟨![(1607/512 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(14463/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data420 : S1TaylorBoxData := ⟨box420,![exp38,exp30,exp10],![exp42,exp34,exp18],![exp40,exp32,exp14]⟩
theorem data420_lower_valid : ∀ j, (data420.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data420_upper_valid : ∀ j, (data420.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data420_center_valid : ∀ j, (data420.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin420 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data420 25 := by decide +kernel
theorem positive420 {q : EdgeTriple} (hq : q ∈ box420.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data420 25
    data420_lower_valid data420_upper_valid data420_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin420 hq

def box421 : LogBox := ⟨![(1607/512 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(14463/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data421 : S1TaylorBoxData := ⟨box421,![exp38,exp30,exp18],![exp42,exp34,exp22],![exp40,exp32,exp20]⟩
theorem data421_lower_valid : ∀ j, (data421.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data421_upper_valid : ∀ j, (data421.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data421_center_valid : ∀ j, (data421.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin421 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data421 25 := by decide +kernel
theorem positive421 {q : EdgeTriple} (hq : q ∈ box421.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data421 25
    data421_lower_valid data421_upper_valid data421_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin421 hq

def box422 : LogBox := ⟨![(1607/512 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(14463/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data422 : S1TaylorBoxData := ⟨box422,![exp38,exp34,exp10],![exp42,exp38,exp18],![exp40,exp36,exp14]⟩
theorem data422_lower_valid : ∀ j, (data422.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data422_upper_valid : ∀ j, (data422.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data422_center_valid : ∀ j, (data422.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin422 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data422 25 := by decide +kernel
theorem positive422 {q : EdgeTriple} (hq : q ∈ box422.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data422 25
    data422_lower_valid data422_upper_valid data422_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin422 hq

def box423 : LogBox := ⟨![(1607/512 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data423 : S1TaylorBoxData := ⟨box423,![exp38,exp34,exp18],![exp42,exp38,exp22],![exp40,exp36,exp20]⟩
theorem data423_lower_valid : ∀ j, (data423.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data423_upper_valid : ∀ j, (data423.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data423_center_valid : ∀ j, (data423.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin423 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data423 25 := by decide +kernel
theorem positive423 {q : EdgeTriple} (hq : q ∈ box423.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data423 25
    data423_lower_valid data423_upper_valid data423_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin423 hq

def box424 : LogBox := ⟨![(14463/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data424 : S1TaylorBoxData := ⟨box424,![exp42,exp30,exp10],![exp46,exp34,exp18],![exp44,exp32,exp14]⟩
theorem data424_lower_valid : ∀ j, (data424.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data424_upper_valid : ∀ j, (data424.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data424_center_valid : ∀ j, (data424.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin424 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data424 25 := by decide +kernel
theorem positive424 {q : EdgeTriple} (hq : q ∈ box424.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data424 25
    data424_lower_valid data424_upper_valid data424_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin424 hq

def box425 : LogBox := ⟨![(14463/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(8035/2048 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data425 : S1TaylorBoxData := ⟨box425,![exp42,exp30,exp18],![exp46,exp34,exp22],![exp44,exp32,exp20]⟩
theorem data425_lower_valid : ∀ j, (data425.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data425_upper_valid : ∀ j, (data425.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data425_center_valid : ∀ j, (data425.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin425 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data425 25 := by decide +kernel
theorem positive425 {q : EdgeTriple} (hq : q ∈ box425.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data425 25
    data425_lower_valid data425_upper_valid data425_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin425 hq

def box426 : LogBox := ⟨![(14463/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data426 : S1TaylorBoxData := ⟨box426,![exp42,exp34,exp10],![exp46,exp38,exp18],![exp44,exp36,exp14]⟩
theorem data426_lower_valid : ∀ j, (data426.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data426_upper_valid : ∀ j, (data426.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data426_center_valid : ∀ j, (data426.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin426 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data426 25 := by decide +kernel
theorem positive426 {q : EdgeTriple} (hq : q ∈ box426.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data426 25
    data426_lower_valid data426_upper_valid data426_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin426 hq

def box427 : LogBox := ⟨![(14463/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data427 : S1TaylorBoxData := ⟨box427,![exp42,exp34,exp18],![exp46,exp38,exp22],![exp44,exp36,exp20]⟩
theorem data427_lower_valid : ∀ j, (data427.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data427_upper_valid : ∀ j, (data427.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data427_center_valid : ∀ j, (data427.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin427 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data427 25 := by decide +kernel
theorem positive427 {q : EdgeTriple} (hq : q ∈ box427.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data427 25
    data427_lower_valid data427_upper_valid data427_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin427 hq

def box428 : LogBox := ⟨![(8035/2048 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data428 : S1TaylorBoxData := ⟨box428,![exp46,exp22,exp0],![exp50,exp26,exp4],![exp48,exp24,exp2]⟩
theorem data428_lower_valid : ∀ j, (data428.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data428_upper_valid : ∀ j, (data428.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data428_center_valid : ∀ j, (data428.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin428 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data428 25 := by decide +kernel
theorem positive428 {q : EdgeTriple} (hq : q ∈ box428.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data428 25
    data428_lower_valid data428_upper_valid data428_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin428 hq

def box429 : LogBox := ⟨![(8035/2048 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data429 : S1TaylorBoxData := ⟨box429,![exp46,exp22,exp4],![exp50,exp26,exp10],![exp48,exp24,exp6]⟩
theorem data429_lower_valid : ∀ j, (data429.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data429_upper_valid : ∀ j, (data429.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data429_center_valid : ∀ j, (data429.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin429 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data429 25 := by decide +kernel
theorem positive429 {q : EdgeTriple} (hq : q ∈ box429.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data429 25
    data429_lower_valid data429_upper_valid data429_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin429 hq

def box430 : LogBox := ⟨![(8035/2048 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data430 : S1TaylorBoxData := ⟨box430,![exp46,exp26,exp0],![exp50,exp30,exp4],![exp48,exp28,exp2]⟩
theorem data430_lower_valid : ∀ j, (data430.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data430_upper_valid : ∀ j, (data430.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data430_center_valid : ∀ j, (data430.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin430 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data430 25 := by decide +kernel
theorem positive430 {q : EdgeTriple} (hq : q ∈ box430.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data430 25
    data430_lower_valid data430_upper_valid data430_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin430 hq

def box431 : LogBox := ⟨![(8035/2048 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data431 : S1TaylorBoxData := ⟨box431,![exp46,exp26,exp4],![exp50,exp30,exp10],![exp48,exp28,exp6]⟩
theorem data431_lower_valid : ∀ j, (data431.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data431_upper_valid : ∀ j, (data431.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data431_center_valid : ∀ j, (data431.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin431 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data431 25 := by decide +kernel
theorem positive431 {q : EdgeTriple} (hq : q ∈ box431.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data431 25
    data431_lower_valid data431_upper_valid data431_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin431 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box464 : LogBox := ⟨![(1607/512 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(14463/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data464 : S1TaylorBoxData := ⟨box464,![exp38,exp30,exp22],![exp42,exp34,exp30],![exp40,exp32,exp26]⟩
theorem data464_lower_valid : ∀ j, (data464.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data464_upper_valid : ∀ j, (data464.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data464_center_valid : ∀ j, (data464.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin464 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data464 25 := by decide +kernel
theorem positive464 {q : EdgeTriple} (hq : q ∈ box464.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data464 25
    data464_lower_valid data464_upper_valid data464_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin464 hq

def box465 : LogBox := ⟨![(1607/512 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(14463/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data465 : S1TaylorBoxData := ⟨box465,![exp38,exp34,exp22],![exp42,exp38,exp30],![exp40,exp36,exp26]⟩
theorem data465_lower_valid : ∀ j, (data465.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data465_upper_valid : ∀ j, (data465.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data465_center_valid : ∀ j, (data465.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin465 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data465 25 := by decide +kernel
theorem positive465 {q : EdgeTriple} (hq : q ∈ box465.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data465 25
    data465_lower_valid data465_upper_valid data465_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin465 hq

def box466 : LogBox := ⟨![(14463/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(8035/2048 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data466 : S1TaylorBoxData := ⟨box466,![exp42,exp30,exp22],![exp46,exp34,exp30],![exp44,exp32,exp26]⟩
theorem data466_lower_valid : ∀ j, (data466.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data466_upper_valid : ∀ j, (data466.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data466_center_valid : ∀ j, (data466.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin466 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data466 25 := by decide +kernel
theorem positive466 {q : EdgeTriple} (hq : q ∈ box466.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data466 25
    data466_lower_valid data466_upper_valid data466_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin466 hq

def box467 : LogBox := ⟨![(14463/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(8035/2048 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data467 : S1TaylorBoxData := ⟨box467,![exp42,exp34,exp22],![exp46,exp38,exp30],![exp44,exp36,exp26]⟩
theorem data467_lower_valid : ∀ j, (data467.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data467_upper_valid : ∀ j, (data467.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data467_center_valid : ∀ j, (data467.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin467 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data467 25 := by decide +kernel
theorem positive467 {q : EdgeTriple} (hq : q ∈ box467.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data467 25
    data467_lower_valid data467_upper_valid data467_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin467 hq

def box468 : LogBox := ⟨![(1607/512 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(14463/4096 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data468 : S1TaylorBoxData := ⟨box468,![exp38,exp30,exp30],![exp42,exp34,exp34],![exp40,exp32,exp32]⟩
theorem data468_lower_valid : ∀ j, (data468.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data468_upper_valid : ∀ j, (data468.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data468_center_valid : ∀ j, (data468.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin468 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data468 25 := by decide +kernel
theorem positive468 {q : EdgeTriple} (hq : q ∈ box468.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data468 25
    data468_lower_valid data468_upper_valid data468_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin468 hq

def box469 : LogBox := ⟨![(1607/512 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data469 : S1TaylorBoxData := ⟨box469,![exp38,exp34,exp30],![exp42,exp38,exp38],![exp40,exp36,exp34]⟩
theorem data469_lower_valid : ∀ j, (data469.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data469_upper_valid : ∀ j, (data469.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data469_center_valid : ∀ j, (data469.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin469 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data469 25 := by decide +kernel
theorem positive469 {q : EdgeTriple} (hq : q ∈ box469.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data469 25
    data469_lower_valid data469_upper_valid data469_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin469 hq

def box470 : LogBox := ⟨![(14463/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(8035/2048 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data470 : S1TaylorBoxData := ⟨box470,![exp42,exp30,exp30],![exp46,exp34,exp34],![exp44,exp32,exp32]⟩
theorem data470_lower_valid : ∀ j, (data470.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data470_upper_valid : ∀ j, (data470.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data470_center_valid : ∀ j, (data470.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin470 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data470 25 := by decide +kernel
theorem positive470 {q : EdgeTriple} (hq : q ∈ box470.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data470 25
    data470_lower_valid data470_upper_valid data470_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin470 hq

def box471 : LogBox := ⟨![(14463/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data471 : S1TaylorBoxData := ⟨box471,![exp42,exp34,exp30],![exp46,exp38,exp38],![exp44,exp36,exp34]⟩
theorem data471_lower_valid : ∀ j, (data471.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data471_upper_valid : ∀ j, (data471.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data471_center_valid : ∀ j, (data471.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin471 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data471 25 := by decide +kernel
theorem positive471 {q : EdgeTriple} (hq : q ∈ box471.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data471 25
    data471_lower_valid data471_upper_valid data471_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin471 hq

def box472 : LogBox := ⟨![(8035/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(17677/4096 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data472 : S1TaylorBoxData := ⟨box472,![exp46,exp22,exp22],![exp50,exp26,exp26],![exp48,exp24,exp24]⟩
theorem data472_lower_valid : ∀ j, (data472.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data472_upper_valid : ∀ j, (data472.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data472_center_valid : ∀ j, (data472.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin472 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data472 25 := by decide +kernel
theorem positive472 {q : EdgeTriple} (hq : q ∈ box472.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data472 25
    data472_lower_valid data472_upper_valid data472_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin472 hq

def box473 : LogBox := ⟨![(8035/2048 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(17677/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data473 : S1TaylorBoxData := ⟨box473,![exp46,exp26,exp22],![exp50,exp30,exp30],![exp48,exp28,exp26]⟩
theorem data473_lower_valid : ∀ j, (data473.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data473_upper_valid : ∀ j, (data473.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data473_center_valid : ∀ j, (data473.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin473 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data473 25 := by decide +kernel
theorem positive473 {q : EdgeTriple} (hq : q ∈ box473.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data473 25
    data473_lower_valid data473_upper_valid data473_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin473 hq

def box474 : LogBox := ⟨![(17677/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data474 : S1TaylorBoxData := ⟨box474,![exp50,exp22,exp22],![exp54,exp26,exp26],![exp52,exp24,exp24]⟩
theorem data474_lower_valid : ∀ j, (data474.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data474_upper_valid : ∀ j, (data474.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data474_center_valid : ∀ j, (data474.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin474 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data474 25 := by decide +kernel
theorem positive474 {q : EdgeTriple} (hq : q ∈ box474.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data474 25
    data474_lower_valid data474_upper_valid data474_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin474 hq

def box475 : LogBox := ⟨![(17677/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data475 : S1TaylorBoxData := ⟨box475,![exp50,exp26,exp22],![exp54,exp30,exp30],![exp52,exp28,exp26]⟩
theorem data475_lower_valid : ∀ j, (data475.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data475_upper_valid : ∀ j, (data475.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data475_center_valid : ∀ j, (data475.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin475 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data475 25 := by decide +kernel
theorem positive475 {q : EdgeTriple} (hq : q ∈ box475.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data475 25
    data475_lower_valid data475_upper_valid data475_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin475 hq

def box476 : LogBox := ⟨![(8035/2048 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(17677/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data476 : S1TaylorBoxData := ⟨box476,![exp46,exp30,exp22],![exp50,exp34,exp30],![exp48,exp32,exp26]⟩
theorem data476_lower_valid : ∀ j, (data476.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data476_upper_valid : ∀ j, (data476.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data476_center_valid : ∀ j, (data476.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin476 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data476 25 := by decide +kernel
theorem positive476 {q : EdgeTriple} (hq : q ∈ box476.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data476 25
    data476_lower_valid data476_upper_valid data476_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin476 hq

def box477 : LogBox := ⟨![(8035/2048 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(17677/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data477 : S1TaylorBoxData := ⟨box477,![exp46,exp34,exp22],![exp50,exp38,exp30],![exp48,exp36,exp26]⟩
theorem data477_lower_valid : ∀ j, (data477.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data477_upper_valid : ∀ j, (data477.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data477_center_valid : ∀ j, (data477.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin477 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data477 25 := by decide +kernel
theorem positive477 {q : EdgeTriple} (hq : q ∈ box477.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data477 25
    data477_lower_valid data477_upper_valid data477_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin477 hq

def box478 : LogBox := ⟨![(17677/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data478 : S1TaylorBoxData := ⟨box478,![exp50,exp30,exp22],![exp54,exp34,exp30],![exp52,exp32,exp26]⟩
theorem data478_lower_valid : ∀ j, (data478.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data478_upper_valid : ∀ j, (data478.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data478_center_valid : ∀ j, (data478.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin478 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data478 25 := by decide +kernel
theorem positive478 {q : EdgeTriple} (hq : q ∈ box478.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data478 25
    data478_lower_valid data478_upper_valid data478_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin478 hq

def box479 : LogBox := ⟨![(17677/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data479 : S1TaylorBoxData := ⟨box479,![exp50,exp34,exp22],![exp54,exp38,exp30],![exp52,exp36,exp26]⟩
theorem data479_lower_valid : ∀ j, (data479.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data479_upper_valid : ∀ j, (data479.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data479_center_valid : ∀ j, (data479.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin479 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data479 25 := by decide +kernel
theorem positive479 {q : EdgeTriple} (hq : q ∈ box479.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data479 25
    data479_lower_valid data479_upper_valid data479_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin479 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

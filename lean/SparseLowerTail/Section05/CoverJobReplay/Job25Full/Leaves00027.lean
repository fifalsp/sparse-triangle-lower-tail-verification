import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box432 : LogBox := ⟨![(17677/4096 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data432 : S1TaylorBoxData := ⟨box432,![exp50,exp22,exp0],![exp54,exp26,exp4],![exp52,exp24,exp2]⟩
theorem data432_lower_valid : ∀ j, (data432.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data432_upper_valid : ∀ j, (data432.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data432_center_valid : ∀ j, (data432.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin432 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data432 25 := by decide +kernel
theorem positive432 {q : EdgeTriple} (hq : q ∈ box432.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data432 25
    data432_lower_valid data432_upper_valid data432_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin432 hq

def box433 : LogBox := ⟨![(17677/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data433 : S1TaylorBoxData := ⟨box433,![exp50,exp22,exp4],![exp54,exp26,exp10],![exp52,exp24,exp6]⟩
theorem data433_lower_valid : ∀ j, (data433.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data433_upper_valid : ∀ j, (data433.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data433_center_valid : ∀ j, (data433.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin433 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data433 25 := by decide +kernel
theorem positive433 {q : EdgeTriple} (hq : q ∈ box433.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data433 25
    data433_lower_valid data433_upper_valid data433_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin433 hq

def box434 : LogBox := ⟨![(17677/4096 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data434 : S1TaylorBoxData := ⟨box434,![exp50,exp26,exp0],![exp54,exp30,exp4],![exp52,exp28,exp2]⟩
theorem data434_lower_valid : ∀ j, (data434.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data434_upper_valid : ∀ j, (data434.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data434_center_valid : ∀ j, (data434.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin434 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data434 25 := by decide +kernel
theorem positive434 {q : EdgeTriple} (hq : q ∈ box434.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data434 25
    data434_lower_valid data434_upper_valid data434_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin434 hq

def box435 : LogBox := ⟨![(17677/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data435 : S1TaylorBoxData := ⟨box435,![exp50,exp26,exp4],![exp54,exp30,exp10],![exp52,exp28,exp6]⟩
theorem data435_lower_valid : ∀ j, (data435.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data435_upper_valid : ∀ j, (data435.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data435_center_valid : ∀ j, (data435.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin435 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data435 25 := by decide +kernel
theorem positive435 {q : EdgeTriple} (hq : q ∈ box435.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data435 25
    data435_lower_valid data435_upper_valid data435_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin435 hq

def box436 : LogBox := ⟨![(8035/2048 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data436 : S1TaylorBoxData := ⟨box436,![exp46,exp22,exp10],![exp50,exp26,exp18],![exp48,exp24,exp14]⟩
theorem data436_lower_valid : ∀ j, (data436.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data436_upper_valid : ∀ j, (data436.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data436_center_valid : ∀ j, (data436.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin436 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data436 25 := by decide +kernel
theorem positive436 {q : EdgeTriple} (hq : q ∈ box436.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data436 25
    data436_lower_valid data436_upper_valid data436_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin436 hq

def box437 : LogBox := ⟨![(8035/2048 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data437 : S1TaylorBoxData := ⟨box437,![exp46,exp22,exp18],![exp50,exp26,exp22],![exp48,exp24,exp20]⟩
theorem data437_lower_valid : ∀ j, (data437.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data437_upper_valid : ∀ j, (data437.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data437_center_valid : ∀ j, (data437.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin437 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data437 25 := by decide +kernel
theorem positive437 {q : EdgeTriple} (hq : q ∈ box437.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data437 25
    data437_lower_valid data437_upper_valid data437_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin437 hq

def box438 : LogBox := ⟨![(8035/2048 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data438 : S1TaylorBoxData := ⟨box438,![exp46,exp26,exp10],![exp50,exp30,exp18],![exp48,exp28,exp14]⟩
theorem data438_lower_valid : ∀ j, (data438.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data438_upper_valid : ∀ j, (data438.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data438_center_valid : ∀ j, (data438.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin438 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data438 25 := by decide +kernel
theorem positive438 {q : EdgeTriple} (hq : q ∈ box438.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data438 25
    data438_lower_valid data438_upper_valid data438_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin438 hq

def box439 : LogBox := ⟨![(8035/2048 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data439 : S1TaylorBoxData := ⟨box439,![exp46,exp26,exp18],![exp50,exp30,exp22],![exp48,exp28,exp20]⟩
theorem data439_lower_valid : ∀ j, (data439.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data439_upper_valid : ∀ j, (data439.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data439_center_valid : ∀ j, (data439.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin439 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data439 25 := by decide +kernel
theorem positive439 {q : EdgeTriple} (hq : q ∈ box439.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data439 25
    data439_lower_valid data439_upper_valid data439_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin439 hq

def box440 : LogBox := ⟨![(17677/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data440 : S1TaylorBoxData := ⟨box440,![exp50,exp22,exp10],![exp54,exp26,exp18],![exp52,exp24,exp14]⟩
theorem data440_lower_valid : ∀ j, (data440.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data440_upper_valid : ∀ j, (data440.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data440_center_valid : ∀ j, (data440.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin440 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data440 25 := by decide +kernel
theorem positive440 {q : EdgeTriple} (hq : q ∈ box440.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data440 25
    data440_lower_valid data440_upper_valid data440_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin440 hq

def box441 : LogBox := ⟨![(17677/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data441 : S1TaylorBoxData := ⟨box441,![exp50,exp22,exp18],![exp54,exp26,exp22],![exp52,exp24,exp20]⟩
theorem data441_lower_valid : ∀ j, (data441.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data441_upper_valid : ∀ j, (data441.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data441_center_valid : ∀ j, (data441.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin441 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data441 25 := by decide +kernel
theorem positive441 {q : EdgeTriple} (hq : q ∈ box441.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data441 25
    data441_lower_valid data441_upper_valid data441_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin441 hq

def box442 : LogBox := ⟨![(17677/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data442 : S1TaylorBoxData := ⟨box442,![exp50,exp26,exp10],![exp54,exp30,exp18],![exp52,exp28,exp14]⟩
theorem data442_lower_valid : ∀ j, (data442.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data442_upper_valid : ∀ j, (data442.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data442_center_valid : ∀ j, (data442.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin442 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data442 25 := by decide +kernel
theorem positive442 {q : EdgeTriple} (hq : q ∈ box442.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data442 25
    data442_lower_valid data442_upper_valid data442_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin442 hq

def box443 : LogBox := ⟨![(17677/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data443 : S1TaylorBoxData := ⟨box443,![exp50,exp26,exp18],![exp54,exp30,exp22],![exp52,exp28,exp20]⟩
theorem data443_lower_valid : ∀ j, (data443.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data443_upper_valid : ∀ j, (data443.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data443_center_valid : ∀ j, (data443.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin443 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data443 25 := by decide +kernel
theorem positive443 {q : EdgeTriple} (hq : q ∈ box443.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data443 25
    data443_lower_valid data443_upper_valid data443_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin443 hq

def box444 : LogBox := ⟨![(8035/2048 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data444 : S1TaylorBoxData := ⟨box444,![exp46,exp30,exp0],![exp50,exp34,exp4],![exp48,exp32,exp2]⟩
theorem data444_lower_valid : ∀ j, (data444.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data444_upper_valid : ∀ j, (data444.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data444_center_valid : ∀ j, (data444.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin444 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data444 25 := by decide +kernel
theorem positive444 {q : EdgeTriple} (hq : q ∈ box444.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data444 25
    data444_lower_valid data444_upper_valid data444_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin444 hq

def box445 : LogBox := ⟨![(8035/2048 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data445 : S1TaylorBoxData := ⟨box445,![exp46,exp30,exp4],![exp50,exp34,exp10],![exp48,exp32,exp6]⟩
theorem data445_lower_valid : ∀ j, (data445.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data445_upper_valid : ∀ j, (data445.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data445_center_valid : ∀ j, (data445.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin445 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data445 25 := by decide +kernel
theorem positive445 {q : EdgeTriple} (hq : q ∈ box445.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data445 25
    data445_lower_valid data445_upper_valid data445_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin445 hq

def box446 : LogBox := ⟨![(8035/2048 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data446 : S1TaylorBoxData := ⟨box446,![exp46,exp34,exp0],![exp50,exp38,exp4],![exp48,exp36,exp2]⟩
theorem data446_lower_valid : ∀ j, (data446.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data446_upper_valid : ∀ j, (data446.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data446_center_valid : ∀ j, (data446.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin446 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data446 25 := by decide +kernel
theorem positive446 {q : EdgeTriple} (hq : q ∈ box446.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data446 25
    data446_lower_valid data446_upper_valid data446_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin446 hq

def box447 : LogBox := ⟨![(8035/2048 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data447 : S1TaylorBoxData := ⟨box447,![exp46,exp34,exp4],![exp50,exp38,exp10],![exp48,exp36,exp6]⟩
theorem data447_lower_valid : ∀ j, (data447.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data447_upper_valid : ∀ j, (data447.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data447_center_valid : ∀ j, (data447.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin447 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data447 25 := by decide +kernel
theorem positive447 {q : EdgeTriple} (hq : q ∈ box447.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data447 25
    data447_lower_valid data447_upper_valid data447_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin447 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

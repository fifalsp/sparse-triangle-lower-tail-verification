import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box688 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)]⟩
def data688 : S1TaylorBoxData := ⟨box688,![exp46,exp42,exp22],![exp50,exp46,exp26],![exp48,exp44,exp24]⟩
theorem data688_lower_valid : ∀ j, (data688.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data688_upper_valid : ∀ j, (data688.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data688_center_valid : ∀ j, (data688.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp24_valid
theorem margin688 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data688 25 := by decide +kernel
theorem positive688 {q : EdgeTriple} (hq : q ∈ box688.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data688 25
    data688_lower_valid data688_upper_valid data688_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin688 hq

def box689 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data689 : S1TaylorBoxData := ⟨box689,![exp46,exp42,exp26],![exp50,exp46,exp30],![exp48,exp44,exp28]⟩
theorem data689_lower_valid : ∀ j, (data689.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data689_upper_valid : ∀ j, (data689.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data689_center_valid : ∀ j, (data689.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp28_valid
theorem margin689 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data689 25 := by decide +kernel
theorem positive689 {q : EdgeTriple} (hq : q ∈ box689.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data689 25
    data689_lower_valid data689_upper_valid data689_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin689 hq

def box690 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data690 : S1TaylorBoxData := ⟨box690,![exp50,exp38,exp22],![exp54,exp42,exp26],![exp52,exp40,exp24]⟩
theorem data690_lower_valid : ∀ j, (data690.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data690_upper_valid : ∀ j, (data690.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data690_center_valid : ∀ j, (data690.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp24_valid
theorem margin690 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data690 25 := by decide +kernel
theorem positive690 {q : EdgeTriple} (hq : q ∈ box690.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data690 25
    data690_lower_valid data690_upper_valid data690_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin690 hq

def box691 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(8035/4096 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data691 : S1TaylorBoxData := ⟨box691,![exp50,exp38,exp26],![exp54,exp42,exp30],![exp52,exp40,exp28]⟩
theorem data691_lower_valid : ∀ j, (data691.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp26_valid
theorem data691_upper_valid : ∀ j, (data691.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data691_center_valid : ∀ j, (data691.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp28_valid
theorem margin691 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data691 25 := by decide +kernel
theorem positive691 {q : EdgeTriple} (hq : q ∈ box691.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data691 25
    data691_lower_valid data691_upper_valid data691_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin691 hq

def box692 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)]⟩
def data692 : S1TaylorBoxData := ⟨box692,![exp50,exp42,exp22],![exp54,exp46,exp26],![exp52,exp44,exp24]⟩
theorem data692_lower_valid : ∀ j, (data692.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data692_upper_valid : ∀ j, (data692.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data692_center_valid : ∀ j, (data692.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp24_valid
theorem margin692 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data692 25 := by decide +kernel
theorem positive692 {q : EdgeTriple} (hq : q ∈ box692.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data692 25
    data692_lower_valid data692_upper_valid data692_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin692 hq

def box693 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data693 : S1TaylorBoxData := ⟨box693,![exp50,exp42,exp26],![exp54,exp46,exp30],![exp52,exp44,exp28]⟩
theorem data693_lower_valid : ∀ j, (data693.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data693_upper_valid : ∀ j, (data693.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data693_center_valid : ∀ j, (data693.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp28_valid
theorem margin693 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data693 25 := by decide +kernel
theorem positive693 {q : EdgeTriple} (hq : q ∈ box693.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data693 25
    data693_lower_valid data693_upper_valid data693_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin693 hq

def box694 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data694 : S1TaylorBoxData := ⟨box694,![exp46,exp38,exp30],![exp50,exp42,exp34],![exp48,exp40,exp32]⟩
theorem data694_lower_valid : ∀ j, (data694.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data694_upper_valid : ∀ j, (data694.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data694_center_valid : ∀ j, (data694.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp32_valid
theorem margin694 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data694 25 := by decide +kernel
theorem positive694 {q : EdgeTriple} (hq : q ∈ box694.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data694 25
    data694_lower_valid data694_upper_valid data694_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin694 hq

def box695 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(11249/4096 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data695 : S1TaylorBoxData := ⟨box695,![exp46,exp38,exp34],![exp50,exp42,exp38],![exp48,exp40,exp36]⟩
theorem data695_lower_valid : ∀ j, (data695.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp34_valid
theorem data695_upper_valid : ∀ j, (data695.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data695_center_valid : ∀ j, (data695.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp36_valid
theorem margin695 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data695 25 := by decide +kernel
theorem positive695 {q : EdgeTriple} (hq : q ∈ box695.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data695 25
    data695_lower_valid data695_upper_valid data695_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin695 hq

def box696 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)]⟩
def data696 : S1TaylorBoxData := ⟨box696,![exp46,exp42,exp30],![exp50,exp46,exp34],![exp48,exp44,exp32]⟩
theorem data696_lower_valid : ∀ j, (data696.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data696_upper_valid : ∀ j, (data696.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data696_center_valid : ∀ j, (data696.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp32_valid
theorem margin696 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data696 25 := by decide +kernel
theorem positive696 {q : EdgeTriple} (hq : q ∈ box696.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data696 25
    data696_lower_valid data696_upper_valid data696_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin696 hq

def box697 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def data697 : S1TaylorBoxData := ⟨box697,![exp46,exp42,exp34],![exp50,exp46,exp38],![exp48,exp44,exp36]⟩
theorem data697_lower_valid : ∀ j, (data697.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data697_upper_valid : ∀ j, (data697.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data697_center_valid : ∀ j, (data697.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp36_valid
theorem margin697 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data697 25 := by decide +kernel
theorem positive697 {q : EdgeTriple} (hq : q ∈ box697.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data697 25
    data697_lower_valid data697_upper_valid data697_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin697 hq

def box698 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data698 : S1TaylorBoxData := ⟨box698,![exp50,exp38,exp30],![exp54,exp42,exp34],![exp52,exp40,exp32]⟩
theorem data698_lower_valid : ∀ j, (data698.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data698_upper_valid : ∀ j, (data698.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data698_center_valid : ∀ j, (data698.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp32_valid
theorem margin698 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data698 25 := by decide +kernel
theorem positive698 {q : EdgeTriple} (hq : q ∈ box698.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data698 25
    data698_lower_valid data698_upper_valid data698_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin698 hq

def box699 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(11249/4096 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data699 : S1TaylorBoxData := ⟨box699,![exp50,exp38,exp34],![exp54,exp42,exp38],![exp52,exp40,exp36]⟩
theorem data699_lower_valid : ∀ j, (data699.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp34_valid
theorem data699_upper_valid : ∀ j, (data699.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data699_center_valid : ∀ j, (data699.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp36_valid
theorem margin699 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data699 25 := by decide +kernel
theorem positive699 {q : EdgeTriple} (hq : q ∈ box699.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data699 25
    data699_lower_valid data699_upper_valid data699_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin699 hq

def box700 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)]⟩
def data700 : S1TaylorBoxData := ⟨box700,![exp50,exp42,exp30],![exp54,exp46,exp34],![exp52,exp44,exp32]⟩
theorem data700_lower_valid : ∀ j, (data700.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data700_upper_valid : ∀ j, (data700.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data700_center_valid : ∀ j, (data700.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp32_valid
theorem margin700 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data700 25 := by decide +kernel
theorem positive700 {q : EdgeTriple} (hq : q ∈ box700.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data700 25
    data700_lower_valid data700_upper_valid data700_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin700 hq

def box701 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def data701 : S1TaylorBoxData := ⟨box701,![exp50,exp42,exp34],![exp54,exp46,exp38],![exp52,exp44,exp36]⟩
theorem data701_lower_valid : ∀ j, (data701.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data701_upper_valid : ∀ j, (data701.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data701_center_valid : ∀ j, (data701.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp36_valid
theorem margin701 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data701 25 := by decide +kernel
theorem positive701 {q : EdgeTriple} (hq : q ∈ box701.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data701 25
    data701_lower_valid data701_upper_valid data701_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin701 hq

def box702 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data702 : S1TaylorBoxData := ⟨box702,![exp46,exp46,exp22],![exp50,exp50,exp26],![exp48,exp48,exp24]⟩
theorem data702_lower_valid : ∀ j, (data702.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data702_upper_valid : ∀ j, (data702.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp26_valid
theorem data702_center_valid : ∀ j, (data702.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp24_valid
theorem margin702 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data702 25 := by decide +kernel
theorem positive702 {q : EdgeTriple} (hq : q ∈ box702.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data702 25
    data702_lower_valid data702_upper_valid data702_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin702 hq

def box703 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data703 : S1TaylorBoxData := ⟨box703,![exp46,exp46,exp26],![exp50,exp50,exp30],![exp48,exp48,exp28]⟩
theorem data703_lower_valid : ∀ j, (data703.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data703_upper_valid : ∀ j, (data703.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data703_center_valid : ∀ j, (data703.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp28_valid
theorem margin703 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data703 25 := by decide +kernel
theorem positive703 {q : EdgeTriple} (hq : q ∈ box703.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data703 25
    data703_lower_valid data703_upper_valid data703_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin703 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

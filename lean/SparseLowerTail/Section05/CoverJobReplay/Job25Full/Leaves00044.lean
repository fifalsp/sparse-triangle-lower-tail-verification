import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box704 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data704 : S1TaylorBoxData := ⟨box704,![exp50,exp46,exp22],![exp54,exp50,exp26],![exp52,exp48,exp24]⟩
theorem data704_lower_valid : ∀ j, (data704.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data704_upper_valid : ∀ j, (data704.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp26_valid
theorem data704_center_valid : ∀ j, (data704.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp24_valid
theorem margin704 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data704 25 := by decide +kernel
theorem positive704 {q : EdgeTriple} (hq : q ∈ box704.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data704 25
    data704_lower_valid data704_upper_valid data704_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin704 hq

def box705 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data705 : S1TaylorBoxData := ⟨box705,![exp50,exp46,exp26],![exp54,exp50,exp30],![exp52,exp48,exp28]⟩
theorem data705_lower_valid : ∀ j, (data705.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data705_upper_valid : ∀ j, (data705.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data705_center_valid : ∀ j, (data705.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp28_valid
theorem margin705 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data705 25 := by decide +kernel
theorem positive705 {q : EdgeTriple} (hq : q ∈ box705.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data705 25
    data705_lower_valid data705_upper_valid data705_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin705 hq

def box706 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(8035/4096 : ℚ)]⟩
def data706 : S1TaylorBoxData := ⟨box706,![exp50,exp50,exp22],![exp54,exp54,exp26],![exp52,exp52,exp24]⟩
theorem data706_lower_valid : ∀ j, (data706.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data706_upper_valid : ∀ j, (data706.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp26_valid
theorem data706_center_valid : ∀ j, (data706.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp24_valid
theorem margin706 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data706 25 := by decide +kernel
theorem positive706 {q : EdgeTriple} (hq : q ∈ box706.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data706 25
    data706_lower_valid data706_upper_valid data706_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin706 hq

def box707 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(8035/4096 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)]⟩
def data707 : S1TaylorBoxData := ⟨box707,![exp50,exp50,exp26],![exp54,exp54,exp30],![exp52,exp52,exp28]⟩
theorem data707_lower_valid : ∀ j, (data707.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp26_valid
theorem data707_upper_valid : ∀ j, (data707.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data707_center_valid : ∀ j, (data707.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp28_valid
theorem margin707 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data707 25 := by decide +kernel
theorem positive707 {q : EdgeTriple} (hq : q ∈ box707.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data707 25
    data707_lower_valid data707_upper_valid data707_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin707 hq

def box708 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data708 : S1TaylorBoxData := ⟨box708,![exp46,exp46,exp30],![exp50,exp50,exp34],![exp48,exp48,exp32]⟩
theorem data708_lower_valid : ∀ j, (data708.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data708_upper_valid : ∀ j, (data708.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp34_valid
theorem data708_center_valid : ∀ j, (data708.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp32_valid
theorem margin708 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data708 25 := by decide +kernel
theorem positive708 {q : EdgeTriple} (hq : q ∈ box708.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data708 25
    data708_lower_valid data708_upper_valid data708_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin708 hq

def box709 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)]⟩
def data709 : S1TaylorBoxData := ⟨box709,![exp46,exp46,exp34],![exp50,exp50,exp38],![exp48,exp48,exp36]⟩
theorem data709_lower_valid : ∀ j, (data709.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data709_upper_valid : ∀ j, (data709.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data709_center_valid : ∀ j, (data709.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp36_valid
theorem margin709 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data709 25 := by decide +kernel
theorem positive709 {q : EdgeTriple} (hq : q ∈ box709.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data709 25
    data709_lower_valid data709_upper_valid data709_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin709 hq

def box710 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data710 : S1TaylorBoxData := ⟨box710,![exp50,exp46,exp30],![exp54,exp50,exp34],![exp52,exp48,exp32]⟩
theorem data710_lower_valid : ∀ j, (data710.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data710_upper_valid : ∀ j, (data710.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp34_valid
theorem data710_center_valid : ∀ j, (data710.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp32_valid
theorem margin710 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data710 25 := by decide +kernel
theorem positive710 {q : EdgeTriple} (hq : q ∈ box710.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data710 25
    data710_lower_valid data710_upper_valid data710_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin710 hq

def box711 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)]⟩
def data711 : S1TaylorBoxData := ⟨box711,![exp50,exp46,exp34],![exp54,exp50,exp38],![exp52,exp48,exp36]⟩
theorem data711_lower_valid : ∀ j, (data711.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data711_upper_valid : ∀ j, (data711.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data711_center_valid : ∀ j, (data711.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp36_valid
theorem margin711 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data711 25 := by decide +kernel
theorem positive711 {q : EdgeTriple} (hq : q ∈ box711.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data711 25
    data711_lower_valid data711_upper_valid data711_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin711 hq

def box712 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(11249/4096 : ℚ)]⟩
def data712 : S1TaylorBoxData := ⟨box712,![exp50,exp50,exp30],![exp54,exp54,exp34],![exp52,exp52,exp32]⟩
theorem data712_lower_valid : ∀ j, (data712.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data712_upper_valid : ∀ j, (data712.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp34_valid
theorem data712_center_valid : ∀ j, (data712.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp32_valid
theorem margin712 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data712 25 := by decide +kernel
theorem positive712 {q : EdgeTriple} (hq : q ∈ box712.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data712 25
    data712_lower_valid data712_upper_valid data712_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin712 hq

def box713 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(11249/4096 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def data713 : S1TaylorBoxData := ⟨box713,![exp50,exp50,exp34],![exp54,exp54,exp38],![exp52,exp52,exp36]⟩
theorem data713_lower_valid : ∀ j, (data713.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp34_valid
theorem data713_upper_valid : ∀ j, (data713.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data713_center_valid : ∀ j, (data713.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp36_valid
theorem margin713 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data713 25 := by decide +kernel
theorem positive713 {q : EdgeTriple} (hq : q ∈ box713.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data713 25
    data713_lower_valid data713_upper_valid data713_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin713 hq

def box714 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data714 : S1TaylorBoxData := ⟨box714,![exp54,exp38,exp0],![exp58,exp42,exp4],![exp56,exp40,exp2]⟩
theorem data714_lower_valid : ∀ j, (data714.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data714_upper_valid : ∀ j, (data714.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data714_center_valid : ∀ j, (data714.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin714 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data714 25 := by decide +kernel
theorem positive714 {q : EdgeTriple} (hq : q ∈ box714.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data714 25
    data714_lower_valid data714_upper_valid data714_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin714 hq

def box715 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data715 : S1TaylorBoxData := ⟨box715,![exp54,exp38,exp4],![exp58,exp42,exp10],![exp56,exp40,exp6]⟩
theorem data715_lower_valid : ∀ j, (data715.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data715_upper_valid : ∀ j, (data715.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data715_center_valid : ∀ j, (data715.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin715 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data715 25 := by decide +kernel
theorem positive715 {q : EdgeTriple} (hq : q ∈ box715.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data715 25
    data715_lower_valid data715_upper_valid data715_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin715 hq

def box716 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data716 : S1TaylorBoxData := ⟨box716,![exp54,exp42,exp0],![exp58,exp46,exp4],![exp56,exp44,exp2]⟩
theorem data716_lower_valid : ∀ j, (data716.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp0_valid
theorem data716_upper_valid : ∀ j, (data716.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data716_center_valid : ∀ j, (data716.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp2_valid
theorem margin716 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data716) 25)).lower := by
  decide +kernel
theorem positive716 {q : EdgeTriple} (hq : q ∈ box716.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data716)
    ⟨data716_lower_valid,data716_upper_valid⟩ 25 margin716 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box717 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data717 : S1TaylorBoxData := ⟨box717,![exp54,exp42,exp4],![exp58,exp46,exp10],![exp56,exp44,exp6]⟩
theorem data717_lower_valid : ∀ j, (data717.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data717_upper_valid : ∀ j, (data717.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data717_center_valid : ∀ j, (data717.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp6_valid
theorem margin717 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data717 25 := by decide +kernel
theorem positive717 {q : EdgeTriple} (hq : q ∈ box717.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data717 25
    data717_lower_valid data717_upper_valid data717_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin717 hq

def box718 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data718 : S1TaylorBoxData := ⟨box718,![exp58,exp38,exp0],![exp62,exp42,exp4],![exp60,exp40,exp2]⟩
theorem data718_lower_valid : ∀ j, (data718.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data718_upper_valid : ∀ j, (data718.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data718_center_valid : ∀ j, (data718.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin718 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data718 25 := by decide +kernel
theorem positive718 {q : EdgeTriple} (hq : q ∈ box718.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data718 25
    data718_lower_valid data718_upper_valid data718_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin718 hq

def box719 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data719 : S1TaylorBoxData := ⟨box719,![exp58,exp38,exp4],![exp62,exp42,exp10],![exp60,exp40,exp6]⟩
theorem data719_lower_valid : ∀ j, (data719.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data719_upper_valid : ∀ j, (data719.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data719_center_valid : ∀ j, (data719.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin719 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data719 25 := by decide +kernel
theorem positive719 {q : EdgeTriple} (hq : q ∈ box719.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data719 25
    data719_lower_valid data719_upper_valid data719_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin719 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

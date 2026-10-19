import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box864 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(8035/4096 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data864 : S1TaylorBoxData := ⟨box864,![exp54,exp54,exp26],![exp58,exp58,exp30],![exp56,exp56,exp28]⟩
theorem data864_lower_valid : ∀ j, (data864.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp26_valid
theorem data864_upper_valid : ∀ j, (data864.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp30_valid
theorem data864_center_valid : ∀ j, (data864.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp28_valid
theorem margin864 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data864 25 := by decide +kernel
theorem positive864 {q : EdgeTriple} (hq : q ∈ box864.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data864 25
    data864_lower_valid data864_upper_valid data864_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin864 hq

def box865 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data865 : S1TaylorBoxData := ⟨box865,![exp58,exp54,exp22],![exp62,exp58,exp26],![exp60,exp56,exp24]⟩
theorem data865_lower_valid : ∀ j, (data865.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data865_upper_valid : ∀ j, (data865.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp26_valid
theorem data865_center_valid : ∀ j, (data865.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp24_valid
theorem margin865 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data865 25 := by decide +kernel
theorem positive865 {q : EdgeTriple} (hq : q ∈ box865.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data865 25
    data865_lower_valid data865_upper_valid data865_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin865 hq

def box866 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(8035/4096 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data866 : S1TaylorBoxData := ⟨box866,![exp58,exp54,exp26],![exp62,exp58,exp30],![exp60,exp56,exp28]⟩
theorem data866_lower_valid : ∀ j, (data866.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp26_valid
theorem data866_upper_valid : ∀ j, (data866.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp30_valid
theorem data866_center_valid : ∀ j, (data866.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp28_valid
theorem margin866 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data866 25 := by decide +kernel
theorem positive866 {q : EdgeTriple} (hq : q ∈ box866.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data866 25
    data866_lower_valid data866_upper_valid data866_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin866 hq

def box867 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(8035/4096 : ℚ)]⟩
def data867 : S1TaylorBoxData := ⟨box867,![exp58,exp58,exp22],![exp62,exp62,exp26],![exp60,exp60,exp24]⟩
theorem data867_lower_valid : ∀ j, (data867.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp22_valid
theorem data867_upper_valid : ∀ j, (data867.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp26_valid
theorem data867_center_valid : ∀ j, (data867.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp24_valid
theorem margin867 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data867 25 := by decide +kernel
theorem positive867 {q : EdgeTriple} (hq : q ∈ box867.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data867 25
    data867_lower_valid data867_upper_valid data867_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin867 hq

def box868 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(8035/4096 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data868 : S1TaylorBoxData := ⟨box868,![exp58,exp58,exp26],![exp62,exp62,exp30],![exp60,exp60,exp28]⟩
theorem data868_lower_valid : ∀ j, (data868.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp26_valid
theorem data868_upper_valid : ∀ j, (data868.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp30_valid
theorem data868_center_valid : ∀ j, (data868.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp28_valid
theorem margin868 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data868 25 := by decide +kernel
theorem positive868 {q : EdgeTriple} (hq : q ∈ box868.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data868 25
    data868_lower_valid data868_upper_valid data868_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin868 hq

def box869 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data869 : S1TaylorBoxData := ⟨box869,![exp54,exp54,exp30],![exp58,exp58,exp34],![exp56,exp56,exp32]⟩
theorem data869_lower_valid : ∀ j, (data869.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data869_upper_valid : ∀ j, (data869.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp34_valid
theorem data869_center_valid : ∀ j, (data869.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp32_valid
theorem margin869 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data869 25 := by decide +kernel
theorem positive869 {q : EdgeTriple} (hq : q ∈ box869.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data869 25
    data869_lower_valid data869_upper_valid data869_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin869 hq

def box870 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(11249/4096 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/512 : ℚ)]⟩
def data870 : S1TaylorBoxData := ⟨box870,![exp54,exp54,exp34],![exp58,exp58,exp38],![exp56,exp56,exp36]⟩
theorem data870_lower_valid : ∀ j, (data870.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp34_valid
theorem data870_upper_valid : ∀ j, (data870.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp38_valid
theorem data870_center_valid : ∀ j, (data870.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp36_valid
theorem margin870 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data870 25 := by decide +kernel
theorem positive870 {q : EdgeTriple} (hq : q ∈ box870.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data870 25
    data870_lower_valid data870_upper_valid data870_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin870 hq

def box871 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data871 : S1TaylorBoxData := ⟨box871,![exp58,exp54,exp30],![exp62,exp58,exp34],![exp60,exp56,exp32]⟩
theorem data871_lower_valid : ∀ j, (data871.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data871_upper_valid : ∀ j, (data871.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp34_valid
theorem data871_center_valid : ∀ j, (data871.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp32_valid
theorem margin871 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data871 25 := by decide +kernel
theorem positive871 {q : EdgeTriple} (hq : q ∈ box871.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data871 25
    data871_lower_valid data871_upper_valid data871_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin871 hq

def box872 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(11249/4096 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/512 : ℚ)]⟩
def data872 : S1TaylorBoxData := ⟨box872,![exp58,exp54,exp34],![exp62,exp58,exp38],![exp60,exp56,exp36]⟩
theorem data872_lower_valid : ∀ j, (data872.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp34_valid
theorem data872_upper_valid : ∀ j, (data872.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp38_valid
theorem data872_center_valid : ∀ j, (data872.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp36_valid
theorem margin872 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data872 25 := by decide +kernel
theorem positive872 {q : EdgeTriple} (hq : q ∈ box872.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data872 25
    data872_lower_valid data872_upper_valid data872_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin872 hq

def box873 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/512 : ℚ)]⟩
def data873 : S1TaylorBoxData := ⟨box873,![exp58,exp58,exp30],![exp62,exp62,exp38],![exp60,exp60,exp34]⟩
theorem data873_lower_valid : ∀ j, (data873.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp30_valid
theorem data873_upper_valid : ∀ j, (data873.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp38_valid
theorem data873_center_valid : ∀ j, (data873.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp34_valid
theorem margin873 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data873 25 := by decide +kernel
theorem positive873 {q : EdgeTriple} (hq : q ∈ box873.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data873 25
    data873_lower_valid data873_upper_valid data873_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin873 hq

def box874 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(20891/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data874 : S1TaylorBoxData := ⟨box874,![exp62,exp54,exp22],![exp66,exp58,exp30],![exp64,exp56,exp26]⟩
theorem data874_lower_valid : ∀ j, (data874.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data874_upper_valid : ∀ j, (data874.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp30_valid
theorem data874_center_valid : ∀ j, (data874.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp56_valid
  · exact exp26_valid
theorem margin874 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data874 25 := by decide +kernel
theorem positive874 {q : EdgeTriple} (hq : q ∈ box874.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data874 25
    data874_lower_valid data874_upper_valid data874_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin874 hq

def box875 : LogBox := ⟨![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(11249/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data875 : S1TaylorBoxData := ⟨box875,![exp62,exp58,exp22],![exp66,exp62,exp30],![exp64,exp60,exp26]⟩
theorem data875_lower_valid : ∀ j, (data875.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp22_valid
theorem data875_upper_valid : ∀ j, (data875.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp30_valid
theorem data875_center_valid : ∀ j, (data875.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp60_valid
  · exact exp26_valid
theorem margin875 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data875 25 := by decide +kernel
theorem positive875 {q : EdgeTriple} (hq : q ∈ box875.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data875 25
    data875_lower_valid data875_upper_valid data875_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin875 hq

def box876 : LogBox := ⟨![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data876 : S1TaylorBoxData := ⟨box876,![exp66,exp54,exp22],![exp70,exp62,exp30],![exp68,exp58,exp26]⟩
theorem data876_lower_valid : ∀ j, (data876.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data876_upper_valid : ∀ j, (data876.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp30_valid
theorem data876_center_valid : ∀ j, (data876.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp58_valid
  · exact exp26_valid
theorem margin876 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data876 25 := by decide +kernel
theorem positive876 {q : EdgeTriple} (hq : q ∈ box876.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data876 25
    data876_lower_valid data876_upper_valid data876_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin876 hq

def box877 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(20891/4096 : ℚ),(1607/512 : ℚ)]⟩
def data877 : S1TaylorBoxData := ⟨box877,![exp62,exp54,exp30],![exp66,exp58,exp38],![exp64,exp56,exp34]⟩
theorem data877_lower_valid : ∀ j, (data877.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data877_upper_valid : ∀ j, (data877.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp38_valid
theorem data877_center_valid : ∀ j, (data877.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp56_valid
  · exact exp34_valid
theorem margin877 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data877 25 := by decide +kernel
theorem positive877 {q : EdgeTriple} (hq : q ∈ box877.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data877 25
    data877_lower_valid data877_upper_valid data877_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin877 hq

def box878 : LogBox := ⟨![(11249/2048 : ℚ),(20891/4096 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(11249/2048 : ℚ),(1607/512 : ℚ)]⟩
def data878 : S1TaylorBoxData := ⟨box878,![exp62,exp58,exp30],![exp66,exp62,exp38],![exp64,exp60,exp34]⟩
theorem data878_lower_valid : ∀ j, (data878.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp30_valid
theorem data878_upper_valid : ∀ j, (data878.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp38_valid
theorem data878_center_valid : ∀ j, (data878.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp60_valid
  · exact exp34_valid
theorem margin878 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data878 25 := by decide +kernel
theorem positive878 {q : EdgeTriple} (hq : q ∈ box878.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data878 25
    data878_lower_valid data878_upper_valid data878_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin878 hq

def box879 : LogBox := ⟨![(24105/4096 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(1607/512 : ℚ)]⟩
def data879 : S1TaylorBoxData := ⟨box879,![exp66,exp54,exp30],![exp70,exp62,exp38],![exp68,exp58,exp34]⟩
theorem data879_lower_valid : ∀ j, (data879.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data879_upper_valid : ∀ j, (data879.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp38_valid
theorem data879_center_valid : ∀ j, (data879.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp58_valid
  · exact exp34_valid
theorem margin879 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data879 25 := by decide +kernel
theorem positive879 {q : EdgeTriple} (hq : q ∈ box879.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data879 25
    data879_lower_valid data879_upper_valid data879_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin879 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

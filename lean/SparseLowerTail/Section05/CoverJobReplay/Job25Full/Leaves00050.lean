import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box800 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(8035/4096 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)]⟩
def data800 : S1TaylorBoxData := ⟨box800,![exp58,exp50,exp26],![exp62,exp54,exp30],![exp60,exp52,exp28]⟩
theorem data800_lower_valid : ∀ j, (data800.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp26_valid
theorem data800_upper_valid : ∀ j, (data800.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data800_center_valid : ∀ j, (data800.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp28_valid
theorem margin800 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data800 25 := by decide +kernel
theorem positive800 {q : EdgeTriple} (hq : q ∈ box800.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data800 25
    data800_lower_valid data800_upper_valid data800_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin800 hq

def box801 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data801 : S1TaylorBoxData := ⟨box801,![exp54,exp46,exp30],![exp58,exp50,exp34],![exp56,exp48,exp32]⟩
theorem data801_lower_valid : ∀ j, (data801.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data801_upper_valid : ∀ j, (data801.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp34_valid
theorem data801_center_valid : ∀ j, (data801.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp32_valid
theorem margin801 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data801 25 := by decide +kernel
theorem positive801 {q : EdgeTriple} (hq : q ∈ box801.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data801 25
    data801_lower_valid data801_upper_valid data801_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin801 hq

def box802 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)]⟩
def data802 : S1TaylorBoxData := ⟨box802,![exp54,exp46,exp34],![exp58,exp50,exp38],![exp56,exp48,exp36]⟩
theorem data802_lower_valid : ∀ j, (data802.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data802_upper_valid : ∀ j, (data802.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data802_center_valid : ∀ j, (data802.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp36_valid
theorem margin802 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data802 25 := by decide +kernel
theorem positive802 {q : EdgeTriple} (hq : q ∈ box802.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data802 25
    data802_lower_valid data802_upper_valid data802_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin802 hq

def box803 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(11249/4096 : ℚ)]⟩
def data803 : S1TaylorBoxData := ⟨box803,![exp54,exp50,exp30],![exp58,exp54,exp34],![exp56,exp52,exp32]⟩
theorem data803_lower_valid : ∀ j, (data803.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data803_upper_valid : ∀ j, (data803.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp34_valid
theorem data803_center_valid : ∀ j, (data803.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp32_valid
theorem margin803 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data803 25 := by decide +kernel
theorem positive803 {q : EdgeTriple} (hq : q ∈ box803.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data803 25
    data803_lower_valid data803_upper_valid data803_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin803 hq

def box804 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(11249/4096 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def data804 : S1TaylorBoxData := ⟨box804,![exp54,exp50,exp34],![exp58,exp54,exp38],![exp56,exp52,exp36]⟩
theorem data804_lower_valid : ∀ j, (data804.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp34_valid
theorem data804_upper_valid : ∀ j, (data804.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data804_center_valid : ∀ j, (data804.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp36_valid
theorem margin804 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data804 25 := by decide +kernel
theorem positive804 {q : EdgeTriple} (hq : q ∈ box804.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data804 25
    data804_lower_valid data804_upper_valid data804_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin804 hq

def box805 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data805 : S1TaylorBoxData := ⟨box805,![exp58,exp46,exp30],![exp62,exp50,exp34],![exp60,exp48,exp32]⟩
theorem data805_lower_valid : ∀ j, (data805.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data805_upper_valid : ∀ j, (data805.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp34_valid
theorem data805_center_valid : ∀ j, (data805.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp32_valid
theorem margin805 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data805 25 := by decide +kernel
theorem positive805 {q : EdgeTriple} (hq : q ∈ box805.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data805 25
    data805_lower_valid data805_upper_valid data805_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin805 hq

def box806 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)]⟩
def data806 : S1TaylorBoxData := ⟨box806,![exp58,exp46,exp34],![exp62,exp50,exp38],![exp60,exp48,exp36]⟩
theorem data806_lower_valid : ∀ j, (data806.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data806_upper_valid : ∀ j, (data806.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data806_center_valid : ∀ j, (data806.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp36_valid
theorem margin806 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data806 25 := by decide +kernel
theorem positive806 {q : EdgeTriple} (hq : q ∈ box806.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data806 25
    data806_lower_valid data806_upper_valid data806_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin806 hq

def box807 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(11249/4096 : ℚ)]⟩
def data807 : S1TaylorBoxData := ⟨box807,![exp58,exp50,exp30],![exp62,exp54,exp34],![exp60,exp52,exp32]⟩
theorem data807_lower_valid : ∀ j, (data807.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data807_upper_valid : ∀ j, (data807.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp34_valid
theorem data807_center_valid : ∀ j, (data807.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp32_valid
theorem margin807 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data807 25 := by decide +kernel
theorem positive807 {q : EdgeTriple} (hq : q ∈ box807.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data807 25
    data807_lower_valid data807_upper_valid data807_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin807 hq

def box808 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(11249/4096 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def data808 : S1TaylorBoxData := ⟨box808,![exp58,exp50,exp34],![exp62,exp54,exp38],![exp60,exp52,exp36]⟩
theorem data808_lower_valid : ∀ j, (data808.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp34_valid
theorem data808_upper_valid : ∀ j, (data808.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data808_center_valid : ∀ j, (data808.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp36_valid
theorem margin808 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data808 25 := by decide +kernel
theorem positive808 {q : EdgeTriple} (hq : q ∈ box808.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data808 25
    data808_lower_valid data808_upper_valid data808_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin808 hq

def box809 : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data809 : S1TaylorBoxData := ⟨box809,![exp62,exp38,exp22],![exp66,exp42,exp30],![exp64,exp40,exp26]⟩
theorem data809_lower_valid : ∀ j, (data809.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data809_upper_valid : ∀ j, (data809.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data809_center_valid : ∀ j, (data809.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp40_valid
  · exact exp26_valid
theorem margin809 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data809 25 := by decide +kernel
theorem positive809 {q : EdgeTriple} (hq : q ∈ box809.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data809 25
    data809_lower_valid data809_upper_valid data809_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin809 hq

def box810 : LogBox := ⟨![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data810 : S1TaylorBoxData := ⟨box810,![exp62,exp42,exp22],![exp66,exp46,exp30],![exp64,exp44,exp26]⟩
theorem data810_lower_valid : ∀ j, (data810.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data810_upper_valid : ∀ j, (data810.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data810_center_valid : ∀ j, (data810.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp44_valid
  · exact exp26_valid
theorem margin810 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data810 25 := by decide +kernel
theorem positive810 {q : EdgeTriple} (hq : q ∈ box810.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data810 25
    data810_lower_valid data810_upper_valid data810_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin810 hq

def box811 : LogBox := ⟨![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data811 : S1TaylorBoxData := ⟨box811,![exp66,exp38,exp22],![exp70,exp42,exp30],![exp68,exp40,exp26]⟩
theorem data811_lower_valid : ∀ j, (data811.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data811_upper_valid : ∀ j, (data811.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data811_center_valid : ∀ j, (data811.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp40_valid
  · exact exp26_valid
theorem margin811 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data811 25 := by decide +kernel
theorem positive811 {q : EdgeTriple} (hq : q ∈ box811.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data811 25
    data811_lower_valid data811_upper_valid data811_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin811 hq

def box812 : LogBox := ⟨![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data812 : S1TaylorBoxData := ⟨box812,![exp66,exp42,exp22],![exp70,exp46,exp30],![exp68,exp44,exp26]⟩
theorem data812_lower_valid : ∀ j, (data812.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data812_upper_valid : ∀ j, (data812.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data812_center_valid : ∀ j, (data812.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp44_valid
  · exact exp26_valid
theorem margin812 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data812 25 := by decide +kernel
theorem positive812 {q : EdgeTriple} (hq : q ∈ box812.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data812 25
    data812_lower_valid data812_upper_valid data812_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin812 hq

def box813 : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data813 : S1TaylorBoxData := ⟨box813,![exp62,exp38,exp30],![exp66,exp42,exp38],![exp64,exp40,exp34]⟩
theorem data813_lower_valid : ∀ j, (data813.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data813_upper_valid : ∀ j, (data813.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data813_center_valid : ∀ j, (data813.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp40_valid
  · exact exp34_valid
theorem margin813 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data813 25 := by decide +kernel
theorem positive813 {q : EdgeTriple} (hq : q ∈ box813.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data813 25
    data813_lower_valid data813_upper_valid data813_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin813 hq

def box814 : LogBox := ⟨![(11249/2048 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def data814 : S1TaylorBoxData := ⟨box814,![exp62,exp42,exp30],![exp66,exp46,exp38],![exp64,exp44,exp34]⟩
theorem data814_lower_valid : ∀ j, (data814.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data814_upper_valid : ∀ j, (data814.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data814_center_valid : ∀ j, (data814.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp44_valid
  · exact exp34_valid
theorem margin814 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data814 25 := by decide +kernel
theorem positive814 {q : EdgeTriple} (hq : q ∈ box814.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data814 25
    data814_lower_valid data814_upper_valid data814_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin814 hq

def box815 : LogBox := ⟨![(24105/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(1607/256 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data815 : S1TaylorBoxData := ⟨box815,![exp66,exp38,exp30],![exp70,exp42,exp38],![exp68,exp40,exp34]⟩
theorem data815_lower_valid : ∀ j, (data815.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data815_upper_valid : ∀ j, (data815.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data815_center_valid : ∀ j, (data815.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp40_valid
  · exact exp34_valid
theorem margin815 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data815 25 := by decide +kernel
theorem positive815 {q : EdgeTriple} (hq : q ∈ box815.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data815 25
    data815_lower_valid data815_upper_valid data815_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin815 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

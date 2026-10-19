import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box608 : LogBox := ⟨![(24105/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data608 : S1TaylorBoxData := ⟨box608,![exp66,exp30,exp10],![exp70,exp34,exp18],![exp68,exp32,exp14]⟩
theorem data608_lower_valid : ∀ j, (data608.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data608_upper_valid : ∀ j, (data608.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data608_center_valid : ∀ j, (data608.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin608 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data608 25 := by decide +kernel
theorem positive608 {q : EdgeTriple} (hq : q ∈ box608.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data608 25
    data608_lower_valid data608_upper_valid data608_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin608 hq

def box609 : LogBox := ⟨![(24105/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data609 : S1TaylorBoxData := ⟨box609,![exp66,exp30,exp18],![exp70,exp34,exp22],![exp68,exp32,exp20]⟩
theorem data609_lower_valid : ∀ j, (data609.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data609_upper_valid : ∀ j, (data609.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data609_center_valid : ∀ j, (data609.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin609 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data609 25 := by decide +kernel
theorem positive609 {q : EdgeTriple} (hq : q ∈ box609.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data609 25
    data609_lower_valid data609_upper_valid data609_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin609 hq

def box610 : LogBox := ⟨![(24105/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data610 : S1TaylorBoxData := ⟨box610,![exp66,exp34,exp10],![exp70,exp38,exp18],![exp68,exp36,exp14]⟩
theorem data610_lower_valid : ∀ j, (data610.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data610_upper_valid : ∀ j, (data610.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data610_center_valid : ∀ j, (data610.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin610 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data610 25 := by decide +kernel
theorem positive610 {q : EdgeTriple} (hq : q ∈ box610.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data610 25
    data610_lower_valid data610_upper_valid data610_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin610 hq

def box611 : LogBox := ⟨![(24105/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data611 : S1TaylorBoxData := ⟨box611,![exp66,exp34,exp18],![exp70,exp38,exp22],![exp68,exp36,exp20]⟩
theorem data611_lower_valid : ∀ j, (data611.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data611_upper_valid : ∀ j, (data611.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data611_center_valid : ∀ j, (data611.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin611 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data611 25 := by decide +kernel
theorem positive611 {q : EdgeTriple} (hq : q ∈ box611.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data611 25
    data611_lower_valid data611_upper_valid data611_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin611 hq

def box612 : LogBox := ⟨![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data612 : S1TaylorBoxData := ⟨box612,![exp54,exp22,exp22],![exp58,exp26,exp26],![exp56,exp24,exp24]⟩
theorem data612_lower_valid : ∀ j, (data612.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data612_upper_valid : ∀ j, (data612.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data612_center_valid : ∀ j, (data612.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin612 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data612 25 := by decide +kernel
theorem positive612 {q : EdgeTriple} (hq : q ∈ box612.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data612 25
    data612_lower_valid data612_upper_valid data612_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin612 hq

def box613 : LogBox := ⟨![(4821/1024 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data613 : S1TaylorBoxData := ⟨box613,![exp54,exp26,exp22],![exp58,exp30,exp30],![exp56,exp28,exp26]⟩
theorem data613_lower_valid : ∀ j, (data613.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data613_upper_valid : ∀ j, (data613.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data613_center_valid : ∀ j, (data613.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin613 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data613 25 := by decide +kernel
theorem positive613 {q : EdgeTriple} (hq : q ∈ box613.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data613 25
    data613_lower_valid data613_upper_valid data613_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin613 hq

def box614 : LogBox := ⟨![(20891/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data614 : S1TaylorBoxData := ⟨box614,![exp58,exp22,exp22],![exp62,exp26,exp26],![exp60,exp24,exp24]⟩
theorem data614_lower_valid : ∀ j, (data614.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data614_upper_valid : ∀ j, (data614.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data614_center_valid : ∀ j, (data614.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin614 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data614 25 := by decide +kernel
theorem positive614 {q : EdgeTriple} (hq : q ∈ box614.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data614 25
    data614_lower_valid data614_upper_valid data614_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin614 hq

def box615 : LogBox := ⟨![(20891/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data615 : S1TaylorBoxData := ⟨box615,![exp58,exp26,exp22],![exp62,exp30,exp30],![exp60,exp28,exp26]⟩
theorem data615_lower_valid : ∀ j, (data615.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data615_upper_valid : ∀ j, (data615.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data615_center_valid : ∀ j, (data615.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin615 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data615 25 := by decide +kernel
theorem positive615 {q : EdgeTriple} (hq : q ∈ box615.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data615 25
    data615_lower_valid data615_upper_valid data615_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin615 hq

def box616 : LogBox := ⟨![(4821/1024 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data616 : S1TaylorBoxData := ⟨box616,![exp54,exp30,exp22],![exp58,exp34,exp30],![exp56,exp32,exp26]⟩
theorem data616_lower_valid : ∀ j, (data616.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data616_upper_valid : ∀ j, (data616.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data616_center_valid : ∀ j, (data616.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin616 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data616 25 := by decide +kernel
theorem positive616 {q : EdgeTriple} (hq : q ∈ box616.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data616 25
    data616_lower_valid data616_upper_valid data616_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin616 hq

def box617 : LogBox := ⟨![(4821/1024 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data617 : S1TaylorBoxData := ⟨box617,![exp54,exp34,exp22],![exp58,exp38,exp30],![exp56,exp36,exp26]⟩
theorem data617_lower_valid : ∀ j, (data617.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data617_upper_valid : ∀ j, (data617.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data617_center_valid : ∀ j, (data617.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin617 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data617 25 := by decide +kernel
theorem positive617 {q : EdgeTriple} (hq : q ∈ box617.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data617 25
    data617_lower_valid data617_upper_valid data617_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin617 hq

def box618 : LogBox := ⟨![(20891/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data618 : S1TaylorBoxData := ⟨box618,![exp58,exp30,exp22],![exp62,exp34,exp30],![exp60,exp32,exp26]⟩
theorem data618_lower_valid : ∀ j, (data618.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data618_upper_valid : ∀ j, (data618.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data618_center_valid : ∀ j, (data618.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin618 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data618 25 := by decide +kernel
theorem positive618 {q : EdgeTriple} (hq : q ∈ box618.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data618 25
    data618_lower_valid data618_upper_valid data618_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin618 hq

def box619 : LogBox := ⟨![(20891/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data619 : S1TaylorBoxData := ⟨box619,![exp58,exp34,exp22],![exp62,exp38,exp30],![exp60,exp36,exp26]⟩
theorem data619_lower_valid : ∀ j, (data619.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data619_upper_valid : ∀ j, (data619.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data619_center_valid : ∀ j, (data619.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin619 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data619 25 := by decide +kernel
theorem positive619 {q : EdgeTriple} (hq : q ∈ box619.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data619 25
    data619_lower_valid data619_upper_valid data619_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin619 hq

def box620 : LogBox := ⟨![(4821/1024 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(20891/4096 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data620 : S1TaylorBoxData := ⟨box620,![exp54,exp30,exp30],![exp58,exp34,exp34],![exp56,exp32,exp32]⟩
theorem data620_lower_valid : ∀ j, (data620.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data620_upper_valid : ∀ j, (data620.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data620_center_valid : ∀ j, (data620.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin620 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data620 25 := by decide +kernel
theorem positive620 {q : EdgeTriple} (hq : q ∈ box620.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data620 25
    data620_lower_valid data620_upper_valid data620_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin620 hq

def box621 : LogBox := ⟨![(4821/1024 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data621 : S1TaylorBoxData := ⟨box621,![exp54,exp34,exp30],![exp58,exp38,exp38],![exp56,exp36,exp34]⟩
theorem data621_lower_valid : ∀ j, (data621.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data621_upper_valid : ∀ j, (data621.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data621_center_valid : ∀ j, (data621.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin621 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data621 25 := by decide +kernel
theorem positive621 {q : EdgeTriple} (hq : q ∈ box621.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data621 25
    data621_lower_valid data621_upper_valid data621_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin621 hq

def box622 : LogBox := ⟨![(20891/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data622 : S1TaylorBoxData := ⟨box622,![exp58,exp30,exp30],![exp62,exp34,exp34],![exp60,exp32,exp32]⟩
theorem data622_lower_valid : ∀ j, (data622.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data622_upper_valid : ∀ j, (data622.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data622_center_valid : ∀ j, (data622.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin622 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data622 25 := by decide +kernel
theorem positive622 {q : EdgeTriple} (hq : q ∈ box622.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data622 25
    data622_lower_valid data622_upper_valid data622_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin622 hq

def box623 : LogBox := ⟨![(20891/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data623 : S1TaylorBoxData := ⟨box623,![exp58,exp34,exp30],![exp62,exp38,exp38],![exp60,exp36,exp34]⟩
theorem data623_lower_valid : ∀ j, (data623.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data623_upper_valid : ∀ j, (data623.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data623_center_valid : ∀ j, (data623.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin623 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data623 25 := by decide +kernel
theorem positive623 {q : EdgeTriple} (hq : q ∈ box623.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data623 25
    data623_lower_valid data623_upper_valid data623_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin623 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

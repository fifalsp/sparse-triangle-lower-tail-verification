import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box672 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data672 : S1TaylorBoxData := ⟨box672,![exp50,exp46,exp10],![exp54,exp50,exp18],![exp52,exp48,exp14]⟩
theorem data672_lower_valid : ∀ j, (data672.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data672_upper_valid : ∀ j, (data672.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data672_center_valid : ∀ j, (data672.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp14_valid
theorem margin672 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data672 25 := by decide +kernel
theorem positive672 {q : EdgeTriple} (hq : q ∈ box672.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data672 25
    data672_lower_valid data672_upper_valid data672_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin672 hq

def box673 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data673 : S1TaylorBoxData := ⟨box673,![exp50,exp46,exp18],![exp54,exp50,exp22],![exp52,exp48,exp20]⟩
theorem data673_lower_valid : ∀ j, (data673.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data673_upper_valid : ∀ j, (data673.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data673_center_valid : ∀ j, (data673.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp20_valid
theorem margin673 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data673 25 := by decide +kernel
theorem positive673 {q : EdgeTriple} (hq : q ∈ box673.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data673 25
    data673_lower_valid data673_upper_valid data673_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin673 hq

def box674 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data674 : S1TaylorBoxData := ⟨box674,![exp50,exp50,exp10],![exp54,exp54,exp18],![exp52,exp52,exp14]⟩
theorem data674_lower_valid : ∀ j, (data674.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data674_upper_valid : ∀ j, (data674.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data674_center_valid : ∀ j, (data674.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp14_valid
theorem margin674 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data674 25 := by decide +kernel
theorem positive674 {q : EdgeTriple} (hq : q ∈ box674.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data674 25
    data674_lower_valid data674_upper_valid data674_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin674 hq

def box675 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data675 : S1TaylorBoxData := ⟨box675,![exp50,exp50,exp18],![exp54,exp54,exp22],![exp52,exp52,exp20]⟩
theorem data675_lower_valid : ∀ j, (data675.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data675_upper_valid : ∀ j, (data675.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data675_center_valid : ∀ j, (data675.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp20_valid
theorem margin675 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data675 25 := by decide +kernel
theorem positive675 {q : EdgeTriple} (hq : q ∈ box675.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data675 25
    data675_lower_valid data675_upper_valid data675_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin675 hq

def box676 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data676 : S1TaylorBoxData := ⟨box676,![exp38,exp38,exp22],![exp42,exp42,exp26],![exp40,exp40,exp24]⟩
theorem data676_lower_valid : ∀ j, (data676.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data676_upper_valid : ∀ j, (data676.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data676_center_valid : ∀ j, (data676.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp24_valid
theorem margin676 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data676 25 := by decide +kernel
theorem positive676 {q : EdgeTriple} (hq : q ∈ box676.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data676 25
    data676_lower_valid data676_upper_valid data676_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin676 hq

def box677 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(8035/4096 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data677 : S1TaylorBoxData := ⟨box677,![exp38,exp38,exp26],![exp42,exp42,exp30],![exp40,exp40,exp28]⟩
theorem data677_lower_valid : ∀ j, (data677.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp26_valid
theorem data677_upper_valid : ∀ j, (data677.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data677_center_valid : ∀ j, (data677.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp28_valid
theorem margin677 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data677 25 := by decide +kernel
theorem positive677 {q : EdgeTriple} (hq : q ∈ box677.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data677 25
    data677_lower_valid data677_upper_valid data677_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin677 hq

def box678 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data678 : S1TaylorBoxData := ⟨box678,![exp42,exp38,exp22],![exp46,exp42,exp26],![exp44,exp40,exp24]⟩
theorem data678_lower_valid : ∀ j, (data678.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data678_upper_valid : ∀ j, (data678.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data678_center_valid : ∀ j, (data678.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp24_valid
theorem margin678 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data678 25 := by decide +kernel
theorem positive678 {q : EdgeTriple} (hq : q ∈ box678.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data678 25
    data678_lower_valid data678_upper_valid data678_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin678 hq

def box679 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(8035/4096 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data679 : S1TaylorBoxData := ⟨box679,![exp42,exp38,exp26],![exp46,exp42,exp30],![exp44,exp40,exp28]⟩
theorem data679_lower_valid : ∀ j, (data679.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp26_valid
theorem data679_upper_valid : ∀ j, (data679.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data679_center_valid : ∀ j, (data679.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp28_valid
theorem margin679 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data679 25 := by decide +kernel
theorem positive679 {q : EdgeTriple} (hq : q ∈ box679.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data679 25
    data679_lower_valid data679_upper_valid data679_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin679 hq

def box680 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)]⟩
def data680 : S1TaylorBoxData := ⟨box680,![exp42,exp42,exp22],![exp46,exp46,exp26],![exp44,exp44,exp24]⟩
theorem data680_lower_valid : ∀ j, (data680.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data680_upper_valid : ∀ j, (data680.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data680_center_valid : ∀ j, (data680.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp24_valid
theorem margin680 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data680 25 := by decide +kernel
theorem positive680 {q : EdgeTriple} (hq : q ∈ box680.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data680 25
    data680_lower_valid data680_upper_valid data680_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin680 hq

def box681 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data681 : S1TaylorBoxData := ⟨box681,![exp42,exp42,exp26],![exp46,exp46,exp30],![exp44,exp44,exp28]⟩
theorem data681_lower_valid : ∀ j, (data681.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data681_upper_valid : ∀ j, (data681.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data681_center_valid : ∀ j, (data681.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp28_valid
theorem margin681 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data681 25 := by decide +kernel
theorem positive681 {q : EdgeTriple} (hq : q ∈ box681.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data681 25
    data681_lower_valid data681_upper_valid data681_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin681 hq

def box682 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data682 : S1TaylorBoxData := ⟨box682,![exp38,exp38,exp30],![exp42,exp42,exp38],![exp40,exp40,exp34]⟩
theorem data682_lower_valid : ∀ j, (data682.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data682_upper_valid : ∀ j, (data682.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data682_center_valid : ∀ j, (data682.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp34_valid
theorem margin682 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data682 25 := by decide +kernel
theorem positive682 {q : EdgeTriple} (hq : q ∈ box682.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data682 25
    data682_lower_valid data682_upper_valid data682_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin682 hq

def box683 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data683 : S1TaylorBoxData := ⟨box683,![exp42,exp38,exp30],![exp46,exp42,exp38],![exp44,exp40,exp34]⟩
theorem data683_lower_valid : ∀ j, (data683.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data683_upper_valid : ∀ j, (data683.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data683_center_valid : ∀ j, (data683.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp34_valid
theorem margin683 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data683 25 := by decide +kernel
theorem positive683 {q : EdgeTriple} (hq : q ∈ box683.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data683 25
    data683_lower_valid data683_upper_valid data683_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin683 hq

def box684 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)]⟩
def data684 : S1TaylorBoxData := ⟨box684,![exp42,exp42,exp30],![exp46,exp46,exp34],![exp44,exp44,exp32]⟩
theorem data684_lower_valid : ∀ j, (data684.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data684_upper_valid : ∀ j, (data684.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data684_center_valid : ∀ j, (data684.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp32_valid
theorem margin684 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data684 25 := by decide +kernel
theorem positive684 {q : EdgeTriple} (hq : q ∈ box684.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data684 25
    data684_lower_valid data684_upper_valid data684_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin684 hq

def box685 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def data685 : S1TaylorBoxData := ⟨box685,![exp42,exp42,exp34],![exp46,exp46,exp38],![exp44,exp44,exp36]⟩
theorem data685_lower_valid : ∀ j, (data685.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data685_upper_valid : ∀ j, (data685.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data685_center_valid : ∀ j, (data685.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp36_valid
theorem margin685 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data685 25 := by decide +kernel
theorem positive685 {q : EdgeTriple} (hq : q ∈ box685.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data685 25
    data685_lower_valid data685_upper_valid data685_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin685 hq

def box686 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data686 : S1TaylorBoxData := ⟨box686,![exp46,exp38,exp22],![exp50,exp42,exp26],![exp48,exp40,exp24]⟩
theorem data686_lower_valid : ∀ j, (data686.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data686_upper_valid : ∀ j, (data686.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data686_center_valid : ∀ j, (data686.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp24_valid
theorem margin686 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data686 25 := by decide +kernel
theorem positive686 {q : EdgeTriple} (hq : q ∈ box686.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data686 25
    data686_lower_valid data686_upper_valid data686_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin686 hq

def box687 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(8035/4096 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data687 : S1TaylorBoxData := ⟨box687,![exp46,exp38,exp26],![exp50,exp42,exp30],![exp48,exp40,exp28]⟩
theorem data687_lower_valid : ∀ j, (data687.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp26_valid
theorem data687_upper_valid : ∀ j, (data687.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data687_center_valid : ∀ j, (data687.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp28_valid
theorem margin687 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data687 25 := by decide +kernel
theorem positive687 {q : EdgeTriple} (hq : q ∈ box687.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data687 25
    data687_lower_valid data687_upper_valid data687_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin687 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

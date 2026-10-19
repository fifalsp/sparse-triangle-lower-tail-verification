import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box640 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data640 : S1TaylorBoxData := ⟨box640,![exp42,exp42,exp0],![exp46,exp46,exp4],![exp44,exp44,exp2]⟩
theorem data640_lower_valid : ∀ j, (data640.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp0_valid
theorem data640_upper_valid : ∀ j, (data640.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data640_center_valid : ∀ j, (data640.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp2_valid
theorem margin640 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data640 25 := by decide +kernel
theorem positive640 {q : EdgeTriple} (hq : q ∈ box640.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data640 25
    data640_lower_valid data640_upper_valid data640_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin640 hq

def box641 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data641 : S1TaylorBoxData := ⟨box641,![exp42,exp42,exp4],![exp46,exp46,exp10],![exp44,exp44,exp6]⟩
theorem data641_lower_valid : ∀ j, (data641.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data641_upper_valid : ∀ j, (data641.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data641_center_valid : ∀ j, (data641.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp6_valid
theorem margin641 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data641 25 := by decide +kernel
theorem positive641 {q : EdgeTriple} (hq : q ∈ box641.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data641 25
    data641_lower_valid data641_upper_valid data641_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin641 hq

def box642 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data642 : S1TaylorBoxData := ⟨box642,![exp38,exp38,exp10],![exp42,exp42,exp18],![exp40,exp40,exp14]⟩
theorem data642_lower_valid : ∀ j, (data642.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data642_upper_valid : ∀ j, (data642.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data642_center_valid : ∀ j, (data642.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin642 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data642 25 := by decide +kernel
theorem positive642 {q : EdgeTriple} (hq : q ∈ box642.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data642 25
    data642_lower_valid data642_upper_valid data642_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin642 hq

def box643 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data643 : S1TaylorBoxData := ⟨box643,![exp38,exp38,exp18],![exp42,exp42,exp22],![exp40,exp40,exp20]⟩
theorem data643_lower_valid : ∀ j, (data643.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data643_upper_valid : ∀ j, (data643.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data643_center_valid : ∀ j, (data643.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin643 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data643 25 := by decide +kernel
theorem positive643 {q : EdgeTriple} (hq : q ∈ box643.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data643 25
    data643_lower_valid data643_upper_valid data643_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin643 hq

def box644 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data644 : S1TaylorBoxData := ⟨box644,![exp42,exp38,exp10],![exp46,exp42,exp18],![exp44,exp40,exp14]⟩
theorem data644_lower_valid : ∀ j, (data644.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data644_upper_valid : ∀ j, (data644.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data644_center_valid : ∀ j, (data644.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin644 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data644 25 := by decide +kernel
theorem positive644 {q : EdgeTriple} (hq : q ∈ box644.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data644 25
    data644_lower_valid data644_upper_valid data644_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin644 hq

def box645 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data645 : S1TaylorBoxData := ⟨box645,![exp42,exp38,exp18],![exp46,exp42,exp22],![exp44,exp40,exp20]⟩
theorem data645_lower_valid : ∀ j, (data645.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data645_upper_valid : ∀ j, (data645.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data645_center_valid : ∀ j, (data645.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin645 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data645 25 := by decide +kernel
theorem positive645 {q : EdgeTriple} (hq : q ∈ box645.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data645 25
    data645_lower_valid data645_upper_valid data645_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin645 hq

def box646 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data646 : S1TaylorBoxData := ⟨box646,![exp42,exp42,exp10],![exp46,exp46,exp18],![exp44,exp44,exp14]⟩
theorem data646_lower_valid : ∀ j, (data646.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data646_upper_valid : ∀ j, (data646.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data646_center_valid : ∀ j, (data646.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp14_valid
theorem margin646 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data646 25 := by decide +kernel
theorem positive646 {q : EdgeTriple} (hq : q ∈ box646.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data646 25
    data646_lower_valid data646_upper_valid data646_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin646 hq

def box647 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data647 : S1TaylorBoxData := ⟨box647,![exp42,exp42,exp18],![exp46,exp46,exp22],![exp44,exp44,exp20]⟩
theorem data647_lower_valid : ∀ j, (data647.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data647_upper_valid : ∀ j, (data647.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data647_center_valid : ∀ j, (data647.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp20_valid
theorem margin647 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data647 25 := by decide +kernel
theorem positive647 {q : EdgeTriple} (hq : q ∈ box647.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data647 25
    data647_lower_valid data647_upper_valid data647_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin647 hq

def box648 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data648 : S1TaylorBoxData := ⟨box648,![exp46,exp38,exp0],![exp50,exp42,exp4],![exp48,exp40,exp2]⟩
theorem data648_lower_valid : ∀ j, (data648.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data648_upper_valid : ∀ j, (data648.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data648_center_valid : ∀ j, (data648.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin648 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data648 25 := by decide +kernel
theorem positive648 {q : EdgeTriple} (hq : q ∈ box648.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data648 25
    data648_lower_valid data648_upper_valid data648_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin648 hq

def box649 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data649 : S1TaylorBoxData := ⟨box649,![exp46,exp38,exp4],![exp50,exp42,exp10],![exp48,exp40,exp6]⟩
theorem data649_lower_valid : ∀ j, (data649.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data649_upper_valid : ∀ j, (data649.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data649_center_valid : ∀ j, (data649.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin649 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data649 25 := by decide +kernel
theorem positive649 {q : EdgeTriple} (hq : q ∈ box649.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data649 25
    data649_lower_valid data649_upper_valid data649_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin649 hq

def box650 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data650 : S1TaylorBoxData := ⟨box650,![exp46,exp42,exp0],![exp50,exp46,exp4],![exp48,exp44,exp2]⟩
theorem data650_lower_valid : ∀ j, (data650.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp0_valid
theorem data650_upper_valid : ∀ j, (data650.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data650_center_valid : ∀ j, (data650.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp2_valid
theorem margin650 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data650 25 := by decide +kernel
theorem positive650 {q : EdgeTriple} (hq : q ∈ box650.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data650 25
    data650_lower_valid data650_upper_valid data650_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin650 hq

def box651 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data651 : S1TaylorBoxData := ⟨box651,![exp46,exp42,exp4],![exp50,exp46,exp10],![exp48,exp44,exp6]⟩
theorem data651_lower_valid : ∀ j, (data651.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data651_upper_valid : ∀ j, (data651.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data651_center_valid : ∀ j, (data651.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp6_valid
theorem margin651 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data651 25 := by decide +kernel
theorem positive651 {q : EdgeTriple} (hq : q ∈ box651.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data651 25
    data651_lower_valid data651_upper_valid data651_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin651 hq

def box652 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data652 : S1TaylorBoxData := ⟨box652,![exp50,exp38,exp0],![exp54,exp42,exp4],![exp52,exp40,exp2]⟩
theorem data652_lower_valid : ∀ j, (data652.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data652_upper_valid : ∀ j, (data652.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data652_center_valid : ∀ j, (data652.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin652 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data652 25 := by decide +kernel
theorem positive652 {q : EdgeTriple} (hq : q ∈ box652.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data652 25
    data652_lower_valid data652_upper_valid data652_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin652 hq

def box653 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data653 : S1TaylorBoxData := ⟨box653,![exp50,exp38,exp4],![exp54,exp42,exp10],![exp52,exp40,exp6]⟩
theorem data653_lower_valid : ∀ j, (data653.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data653_upper_valid : ∀ j, (data653.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data653_center_valid : ∀ j, (data653.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin653 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data653 25 := by decide +kernel
theorem positive653 {q : EdgeTriple} (hq : q ∈ box653.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data653 25
    data653_lower_valid data653_upper_valid data653_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin653 hq

def box654 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data654 : S1TaylorBoxData := ⟨box654,![exp50,exp42,exp0],![exp54,exp46,exp4],![exp52,exp44,exp2]⟩
theorem data654_lower_valid : ∀ j, (data654.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp0_valid
theorem data654_upper_valid : ∀ j, (data654.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data654_center_valid : ∀ j, (data654.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp2_valid
theorem margin654 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data654 25 := by decide +kernel
theorem positive654 {q : EdgeTriple} (hq : q ∈ box654.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data654 25
    data654_lower_valid data654_upper_valid data654_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin654 hq

def box655 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data655 : S1TaylorBoxData := ⟨box655,![exp50,exp42,exp4],![exp54,exp46,exp10],![exp52,exp44,exp6]⟩
theorem data655_lower_valid : ∀ j, (data655.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data655_upper_valid : ∀ j, (data655.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data655_center_valid : ∀ j, (data655.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp6_valid
theorem margin655 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data655 25 := by decide +kernel
theorem positive655 {q : EdgeTriple} (hq : q ∈ box655.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data655 25
    data655_lower_valid data655_upper_valid data655_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin655 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

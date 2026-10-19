import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box784 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)]⟩
def data784 : S1TaylorBoxData := ⟨box784,![exp58,exp42,exp22],![exp62,exp46,exp26],![exp60,exp44,exp24]⟩
theorem data784_lower_valid : ∀ j, (data784.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data784_upper_valid : ∀ j, (data784.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data784_center_valid : ∀ j, (data784.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp24_valid
theorem margin784 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data784 25 := by decide +kernel
theorem positive784 {q : EdgeTriple} (hq : q ∈ box784.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data784 25
    data784_lower_valid data784_upper_valid data784_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin784 hq

def box785 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data785 : S1TaylorBoxData := ⟨box785,![exp58,exp42,exp26],![exp62,exp46,exp30],![exp60,exp44,exp28]⟩
theorem data785_lower_valid : ∀ j, (data785.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data785_upper_valid : ∀ j, (data785.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data785_center_valid : ∀ j, (data785.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp28_valid
theorem margin785 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data785 25 := by decide +kernel
theorem positive785 {q : EdgeTriple} (hq : q ∈ box785.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data785 25
    data785_lower_valid data785_upper_valid data785_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin785 hq

def box786 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data786 : S1TaylorBoxData := ⟨box786,![exp54,exp38,exp30],![exp58,exp42,exp34],![exp56,exp40,exp32]⟩
theorem data786_lower_valid : ∀ j, (data786.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data786_upper_valid : ∀ j, (data786.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data786_center_valid : ∀ j, (data786.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp32_valid
theorem margin786 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data786 25 := by decide +kernel
theorem positive786 {q : EdgeTriple} (hq : q ∈ box786.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data786 25
    data786_lower_valid data786_upper_valid data786_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin786 hq

def box787 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(11249/4096 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data787 : S1TaylorBoxData := ⟨box787,![exp54,exp38,exp34],![exp58,exp42,exp38],![exp56,exp40,exp36]⟩
theorem data787_lower_valid : ∀ j, (data787.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp34_valid
theorem data787_upper_valid : ∀ j, (data787.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data787_center_valid : ∀ j, (data787.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp36_valid
theorem margin787 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data787 25 := by decide +kernel
theorem positive787 {q : EdgeTriple} (hq : q ∈ box787.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data787 25
    data787_lower_valid data787_upper_valid data787_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin787 hq

def box788 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)]⟩
def data788 : S1TaylorBoxData := ⟨box788,![exp54,exp42,exp30],![exp58,exp46,exp34],![exp56,exp44,exp32]⟩
theorem data788_lower_valid : ∀ j, (data788.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data788_upper_valid : ∀ j, (data788.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data788_center_valid : ∀ j, (data788.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp32_valid
theorem margin788 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data788 25 := by decide +kernel
theorem positive788 {q : EdgeTriple} (hq : q ∈ box788.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data788 25
    data788_lower_valid data788_upper_valid data788_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin788 hq

def box789 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def data789 : S1TaylorBoxData := ⟨box789,![exp54,exp42,exp34],![exp58,exp46,exp38],![exp56,exp44,exp36]⟩
theorem data789_lower_valid : ∀ j, (data789.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data789_upper_valid : ∀ j, (data789.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data789_center_valid : ∀ j, (data789.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp36_valid
theorem margin789 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data789 25 := by decide +kernel
theorem positive789 {q : EdgeTriple} (hq : q ∈ box789.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data789 25
    data789_lower_valid data789_upper_valid data789_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin789 hq

def box790 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)]⟩
def data790 : S1TaylorBoxData := ⟨box790,![exp58,exp38,exp30],![exp62,exp42,exp38],![exp60,exp40,exp34]⟩
theorem data790_lower_valid : ∀ j, (data790.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data790_upper_valid : ∀ j, (data790.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data790_center_valid : ∀ j, (data790.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp34_valid
theorem margin790 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data790 25 := by decide +kernel
theorem positive790 {q : EdgeTriple} (hq : q ∈ box790.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data790 25
    data790_lower_valid data790_upper_valid data790_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin790 hq

def box791 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(11249/4096 : ℚ)]⟩
def data791 : S1TaylorBoxData := ⟨box791,![exp58,exp42,exp30],![exp62,exp46,exp34],![exp60,exp44,exp32]⟩
theorem data791_lower_valid : ∀ j, (data791.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data791_upper_valid : ∀ j, (data791.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp34_valid
theorem data791_center_valid : ∀ j, (data791.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp32_valid
theorem margin791 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data791 25 := by decide +kernel
theorem positive791 {q : EdgeTriple} (hq : q ∈ box791.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data791 25
    data791_lower_valid data791_upper_valid data791_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin791 hq

def box792 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(11249/4096 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def data792 : S1TaylorBoxData := ⟨box792,![exp58,exp42,exp34],![exp62,exp46,exp38],![exp60,exp44,exp36]⟩
theorem data792_lower_valid : ∀ j, (data792.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp34_valid
theorem data792_upper_valid : ∀ j, (data792.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data792_center_valid : ∀ j, (data792.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp36_valid
theorem margin792 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data792 25 := by decide +kernel
theorem positive792 {q : EdgeTriple} (hq : q ∈ box792.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data792 25
    data792_lower_valid data792_upper_valid data792_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin792 hq

def box793 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data793 : S1TaylorBoxData := ⟨box793,![exp54,exp46,exp22],![exp58,exp50,exp26],![exp56,exp48,exp24]⟩
theorem data793_lower_valid : ∀ j, (data793.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data793_upper_valid : ∀ j, (data793.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp26_valid
theorem data793_center_valid : ∀ j, (data793.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp24_valid
theorem margin793 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data793 25 := by decide +kernel
theorem positive793 {q : EdgeTriple} (hq : q ∈ box793.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data793 25
    data793_lower_valid data793_upper_valid data793_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin793 hq

def box794 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data794 : S1TaylorBoxData := ⟨box794,![exp54,exp46,exp26],![exp58,exp50,exp30],![exp56,exp48,exp28]⟩
theorem data794_lower_valid : ∀ j, (data794.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data794_upper_valid : ∀ j, (data794.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data794_center_valid : ∀ j, (data794.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp28_valid
theorem margin794 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data794 25 := by decide +kernel
theorem positive794 {q : EdgeTriple} (hq : q ∈ box794.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data794 25
    data794_lower_valid data794_upper_valid data794_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin794 hq

def box795 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(8035/4096 : ℚ)]⟩
def data795 : S1TaylorBoxData := ⟨box795,![exp54,exp50,exp22],![exp58,exp54,exp26],![exp56,exp52,exp24]⟩
theorem data795_lower_valid : ∀ j, (data795.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data795_upper_valid : ∀ j, (data795.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp26_valid
theorem data795_center_valid : ∀ j, (data795.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp24_valid
theorem margin795 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data795 25 := by decide +kernel
theorem positive795 {q : EdgeTriple} (hq : q ∈ box795.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data795 25
    data795_lower_valid data795_upper_valid data795_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin795 hq

def box796 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(8035/4096 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)]⟩
def data796 : S1TaylorBoxData := ⟨box796,![exp54,exp50,exp26],![exp58,exp54,exp30],![exp56,exp52,exp28]⟩
theorem data796_lower_valid : ∀ j, (data796.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp26_valid
theorem data796_upper_valid : ∀ j, (data796.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data796_center_valid : ∀ j, (data796.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp28_valid
theorem margin796 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data796 25 := by decide +kernel
theorem positive796 {q : EdgeTriple} (hq : q ∈ box796.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data796 25
    data796_lower_valid data796_upper_valid data796_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin796 hq

def box797 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data797 : S1TaylorBoxData := ⟨box797,![exp58,exp46,exp22],![exp62,exp50,exp26],![exp60,exp48,exp24]⟩
theorem data797_lower_valid : ∀ j, (data797.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data797_upper_valid : ∀ j, (data797.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp26_valid
theorem data797_center_valid : ∀ j, (data797.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp24_valid
theorem margin797 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data797 25 := by decide +kernel
theorem positive797 {q : EdgeTriple} (hq : q ∈ box797.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data797 25
    data797_lower_valid data797_upper_valid data797_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin797 hq

def box798 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data798 : S1TaylorBoxData := ⟨box798,![exp58,exp46,exp26],![exp62,exp50,exp30],![exp60,exp48,exp28]⟩
theorem data798_lower_valid : ∀ j, (data798.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data798_upper_valid : ∀ j, (data798.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data798_center_valid : ∀ j, (data798.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp28_valid
theorem margin798 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data798 25 := by decide +kernel
theorem positive798 {q : EdgeTriple} (hq : q ∈ box798.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data798 25
    data798_lower_valid data798_upper_valid data798_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin798 hq

def box799 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(8035/4096 : ℚ)]⟩
def data799 : S1TaylorBoxData := ⟨box799,![exp58,exp50,exp22],![exp62,exp54,exp26],![exp60,exp52,exp24]⟩
theorem data799_lower_valid : ∀ j, (data799.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data799_upper_valid : ∀ j, (data799.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp26_valid
theorem data799_center_valid : ∀ j, (data799.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp24_valid
theorem margin799 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data799 25 := by decide +kernel
theorem positive799 {q : EdgeTriple} (hq : q ∈ box799.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data799 25
    data799_lower_valid data799_upper_valid data799_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin799 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

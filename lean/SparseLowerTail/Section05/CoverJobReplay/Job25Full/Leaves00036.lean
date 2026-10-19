import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box576 : LogBox := ⟨![(20891/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data576 : S1TaylorBoxData := ⟨box576,![exp58,exp30,exp10],![exp62,exp34,exp18],![exp60,exp32,exp14]⟩
theorem data576_lower_valid : ∀ j, (data576.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data576_upper_valid : ∀ j, (data576.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data576_center_valid : ∀ j, (data576.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin576 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data576 25 := by decide +kernel
theorem positive576 {q : EdgeTriple} (hq : q ∈ box576.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data576 25
    data576_lower_valid data576_upper_valid data576_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin576 hq

def box577 : LogBox := ⟨![(20891/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data577 : S1TaylorBoxData := ⟨box577,![exp58,exp30,exp18],![exp62,exp34,exp22],![exp60,exp32,exp20]⟩
theorem data577_lower_valid : ∀ j, (data577.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data577_upper_valid : ∀ j, (data577.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data577_center_valid : ∀ j, (data577.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin577 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data577 25 := by decide +kernel
theorem positive577 {q : EdgeTriple} (hq : q ∈ box577.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data577 25
    data577_lower_valid data577_upper_valid data577_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin577 hq

def box578 : LogBox := ⟨![(20891/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data578 : S1TaylorBoxData := ⟨box578,![exp58,exp34,exp10],![exp62,exp38,exp18],![exp60,exp36,exp14]⟩
theorem data578_lower_valid : ∀ j, (data578.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data578_upper_valid : ∀ j, (data578.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data578_center_valid : ∀ j, (data578.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin578 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data578 25 := by decide +kernel
theorem positive578 {q : EdgeTriple} (hq : q ∈ box578.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data578 25
    data578_lower_valid data578_upper_valid data578_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin578 hq

def box579 : LogBox := ⟨![(20891/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data579 : S1TaylorBoxData := ⟨box579,![exp58,exp34,exp18],![exp62,exp38,exp22],![exp60,exp36,exp20]⟩
theorem data579_lower_valid : ∀ j, (data579.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data579_upper_valid : ∀ j, (data579.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data579_center_valid : ∀ j, (data579.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin579 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data579 25 := by decide +kernel
theorem positive579 {q : EdgeTriple} (hq : q ∈ box579.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data579 25
    data579_lower_valid data579_upper_valid data579_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin579 hq

def box580 : LogBox := ⟨![(11249/2048 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data580 : S1TaylorBoxData := ⟨box580,![exp62,exp22,exp0],![exp66,exp26,exp4],![exp64,exp24,exp2]⟩
theorem data580_lower_valid : ∀ j, (data580.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data580_upper_valid : ∀ j, (data580.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data580_center_valid : ∀ j, (data580.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin580 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data580 25 := by decide +kernel
theorem positive580 {q : EdgeTriple} (hq : q ∈ box580.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data580 25
    data580_lower_valid data580_upper_valid data580_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin580 hq

def box581 : LogBox := ⟨![(11249/2048 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data581 : S1TaylorBoxData := ⟨box581,![exp62,exp22,exp4],![exp66,exp26,exp10],![exp64,exp24,exp6]⟩
theorem data581_lower_valid : ∀ j, (data581.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data581_upper_valid : ∀ j, (data581.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data581_center_valid : ∀ j, (data581.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin581 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data581 25 := by decide +kernel
theorem positive581 {q : EdgeTriple} (hq : q ∈ box581.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data581 25
    data581_lower_valid data581_upper_valid data581_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin581 hq

def box582 : LogBox := ⟨![(11249/2048 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data582 : S1TaylorBoxData := ⟨box582,![exp62,exp26,exp0],![exp66,exp30,exp4],![exp64,exp28,exp2]⟩
theorem data582_lower_valid : ∀ j, (data582.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data582_upper_valid : ∀ j, (data582.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data582_center_valid : ∀ j, (data582.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin582 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data582 25 := by decide +kernel
theorem positive582 {q : EdgeTriple} (hq : q ∈ box582.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data582 25
    data582_lower_valid data582_upper_valid data582_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin582 hq

def box583 : LogBox := ⟨![(11249/2048 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data583 : S1TaylorBoxData := ⟨box583,![exp62,exp26,exp4],![exp66,exp30,exp10],![exp64,exp28,exp6]⟩
theorem data583_lower_valid : ∀ j, (data583.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data583_upper_valid : ∀ j, (data583.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data583_center_valid : ∀ j, (data583.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin583 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data583 25 := by decide +kernel
theorem positive583 {q : EdgeTriple} (hq : q ∈ box583.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data583 25
    data583_lower_valid data583_upper_valid data583_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin583 hq

def box584 : LogBox := ⟨![(24105/4096 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data584 : S1TaylorBoxData := ⟨box584,![exp66,exp22,exp0],![exp70,exp26,exp4],![exp68,exp24,exp2]⟩
theorem data584_lower_valid : ∀ j, (data584.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data584_upper_valid : ∀ j, (data584.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data584_center_valid : ∀ j, (data584.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin584 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data584 25 := by decide +kernel
theorem positive584 {q : EdgeTriple} (hq : q ∈ box584.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data584 25
    data584_lower_valid data584_upper_valid data584_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin584 hq

def box585 : LogBox := ⟨![(24105/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data585 : S1TaylorBoxData := ⟨box585,![exp66,exp22,exp4],![exp70,exp26,exp10],![exp68,exp24,exp6]⟩
theorem data585_lower_valid : ∀ j, (data585.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data585_upper_valid : ∀ j, (data585.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data585_center_valid : ∀ j, (data585.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin585 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data585 25 := by decide +kernel
theorem positive585 {q : EdgeTriple} (hq : q ∈ box585.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data585 25
    data585_lower_valid data585_upper_valid data585_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin585 hq

def box586 : LogBox := ⟨![(24105/4096 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data586 : S1TaylorBoxData := ⟨box586,![exp66,exp26,exp0],![exp70,exp30,exp4],![exp68,exp28,exp2]⟩
theorem data586_lower_valid : ∀ j, (data586.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data586_upper_valid : ∀ j, (data586.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data586_center_valid : ∀ j, (data586.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin586 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data586 25 := by decide +kernel
theorem positive586 {q : EdgeTriple} (hq : q ∈ box586.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data586 25
    data586_lower_valid data586_upper_valid data586_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin586 hq

def box587 : LogBox := ⟨![(24105/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data587 : S1TaylorBoxData := ⟨box587,![exp66,exp26,exp4],![exp70,exp30,exp10],![exp68,exp28,exp6]⟩
theorem data587_lower_valid : ∀ j, (data587.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data587_upper_valid : ∀ j, (data587.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data587_center_valid : ∀ j, (data587.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin587 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data587 25 := by decide +kernel
theorem positive587 {q : EdgeTriple} (hq : q ∈ box587.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data587 25
    data587_lower_valid data587_upper_valid data587_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin587 hq

def box588 : LogBox := ⟨![(11249/2048 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data588 : S1TaylorBoxData := ⟨box588,![exp62,exp22,exp10],![exp66,exp26,exp18],![exp64,exp24,exp14]⟩
theorem data588_lower_valid : ∀ j, (data588.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data588_upper_valid : ∀ j, (data588.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data588_center_valid : ∀ j, (data588.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin588 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data588 25 := by decide +kernel
theorem positive588 {q : EdgeTriple} (hq : q ∈ box588.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data588 25
    data588_lower_valid data588_upper_valid data588_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin588 hq

def box589 : LogBox := ⟨![(11249/2048 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data589 : S1TaylorBoxData := ⟨box589,![exp62,exp22,exp18],![exp66,exp26,exp22],![exp64,exp24,exp20]⟩
theorem data589_lower_valid : ∀ j, (data589.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data589_upper_valid : ∀ j, (data589.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data589_center_valid : ∀ j, (data589.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin589 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data589 25 := by decide +kernel
theorem positive589 {q : EdgeTriple} (hq : q ∈ box589.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data589 25
    data589_lower_valid data589_upper_valid data589_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin589 hq

def box590 : LogBox := ⟨![(11249/2048 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data590 : S1TaylorBoxData := ⟨box590,![exp62,exp26,exp10],![exp66,exp30,exp18],![exp64,exp28,exp14]⟩
theorem data590_lower_valid : ∀ j, (data590.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data590_upper_valid : ∀ j, (data590.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data590_center_valid : ∀ j, (data590.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin590 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data590 25 := by decide +kernel
theorem positive590 {q : EdgeTriple} (hq : q ∈ box590.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data590 25
    data590_lower_valid data590_upper_valid data590_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin590 hq

def box591 : LogBox := ⟨![(11249/2048 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data591 : S1TaylorBoxData := ⟨box591,![exp62,exp26,exp18],![exp66,exp30,exp22],![exp64,exp28,exp20]⟩
theorem data591_lower_valid : ∀ j, (data591.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data591_upper_valid : ∀ j, (data591.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data591_center_valid : ∀ j, (data591.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin591 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data591 25 := by decide +kernel
theorem positive591 {q : EdgeTriple} (hq : q ∈ box591.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data591 25
    data591_lower_valid data591_upper_valid data591_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin591 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

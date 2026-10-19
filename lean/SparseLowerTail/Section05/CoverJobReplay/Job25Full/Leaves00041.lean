import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box656 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data656 : S1TaylorBoxData := ⟨box656,![exp46,exp38,exp10],![exp50,exp42,exp18],![exp48,exp40,exp14]⟩
theorem data656_lower_valid : ∀ j, (data656.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data656_upper_valid : ∀ j, (data656.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data656_center_valid : ∀ j, (data656.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin656 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data656 25 := by decide +kernel
theorem positive656 {q : EdgeTriple} (hq : q ∈ box656.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data656 25
    data656_lower_valid data656_upper_valid data656_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin656 hq

def box657 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data657 : S1TaylorBoxData := ⟨box657,![exp46,exp38,exp18],![exp50,exp42,exp22],![exp48,exp40,exp20]⟩
theorem data657_lower_valid : ∀ j, (data657.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data657_upper_valid : ∀ j, (data657.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data657_center_valid : ∀ j, (data657.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin657 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data657 25 := by decide +kernel
theorem positive657 {q : EdgeTriple} (hq : q ∈ box657.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data657 25
    data657_lower_valid data657_upper_valid data657_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin657 hq

def box658 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data658 : S1TaylorBoxData := ⟨box658,![exp46,exp42,exp10],![exp50,exp46,exp18],![exp48,exp44,exp14]⟩
theorem data658_lower_valid : ∀ j, (data658.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data658_upper_valid : ∀ j, (data658.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data658_center_valid : ∀ j, (data658.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp14_valid
theorem margin658 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data658 25 := by decide +kernel
theorem positive658 {q : EdgeTriple} (hq : q ∈ box658.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data658 25
    data658_lower_valid data658_upper_valid data658_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin658 hq

def box659 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data659 : S1TaylorBoxData := ⟨box659,![exp46,exp42,exp18],![exp50,exp46,exp22],![exp48,exp44,exp20]⟩
theorem data659_lower_valid : ∀ j, (data659.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data659_upper_valid : ∀ j, (data659.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data659_center_valid : ∀ j, (data659.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp20_valid
theorem margin659 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data659 25 := by decide +kernel
theorem positive659 {q : EdgeTriple} (hq : q ∈ box659.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data659 25
    data659_lower_valid data659_upper_valid data659_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin659 hq

def box660 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data660 : S1TaylorBoxData := ⟨box660,![exp50,exp38,exp10],![exp54,exp42,exp18],![exp52,exp40,exp14]⟩
theorem data660_lower_valid : ∀ j, (data660.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data660_upper_valid : ∀ j, (data660.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data660_center_valid : ∀ j, (data660.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin660 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data660 25 := by decide +kernel
theorem positive660 {q : EdgeTriple} (hq : q ∈ box660.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data660 25
    data660_lower_valid data660_upper_valid data660_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin660 hq

def box661 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data661 : S1TaylorBoxData := ⟨box661,![exp50,exp38,exp18],![exp54,exp42,exp22],![exp52,exp40,exp20]⟩
theorem data661_lower_valid : ∀ j, (data661.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data661_upper_valid : ∀ j, (data661.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data661_center_valid : ∀ j, (data661.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin661 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data661 25 := by decide +kernel
theorem positive661 {q : EdgeTriple} (hq : q ∈ box661.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data661 25
    data661_lower_valid data661_upper_valid data661_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin661 hq

def box662 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data662 : S1TaylorBoxData := ⟨box662,![exp50,exp42,exp10],![exp54,exp46,exp18],![exp52,exp44,exp14]⟩
theorem data662_lower_valid : ∀ j, (data662.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data662_upper_valid : ∀ j, (data662.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data662_center_valid : ∀ j, (data662.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp14_valid
theorem margin662 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data662 25 := by decide +kernel
theorem positive662 {q : EdgeTriple} (hq : q ∈ box662.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data662 25
    data662_lower_valid data662_upper_valid data662_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin662 hq

def box663 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data663 : S1TaylorBoxData := ⟨box663,![exp50,exp42,exp18],![exp54,exp46,exp22],![exp52,exp44,exp20]⟩
theorem data663_lower_valid : ∀ j, (data663.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data663_upper_valid : ∀ j, (data663.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data663_center_valid : ∀ j, (data663.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp20_valid
theorem margin663 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data663 25 := by decide +kernel
theorem positive663 {q : EdgeTriple} (hq : q ∈ box663.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data663 25
    data663_lower_valid data663_upper_valid data663_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin663 hq

def box664 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data664 : S1TaylorBoxData := ⟨box664,![exp46,exp46,exp0],![exp50,exp50,exp4],![exp48,exp48,exp2]⟩
theorem data664_lower_valid : ∀ j, (data664.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp0_valid
theorem data664_upper_valid : ∀ j, (data664.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data664_center_valid : ∀ j, (data664.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp2_valid
theorem margin664 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data664 25 := by decide +kernel
theorem positive664 {q : EdgeTriple} (hq : q ∈ box664.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data664 25
    data664_lower_valid data664_upper_valid data664_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin664 hq

def box665 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data665 : S1TaylorBoxData := ⟨box665,![exp46,exp46,exp4],![exp50,exp50,exp10],![exp48,exp48,exp6]⟩
theorem data665_lower_valid : ∀ j, (data665.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data665_upper_valid : ∀ j, (data665.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data665_center_valid : ∀ j, (data665.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp6_valid
theorem margin665 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data665 25 := by decide +kernel
theorem positive665 {q : EdgeTriple} (hq : q ∈ box665.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data665 25
    data665_lower_valid data665_upper_valid data665_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin665 hq

def box666 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data666 : S1TaylorBoxData := ⟨box666,![exp50,exp46,exp0],![exp54,exp50,exp4],![exp52,exp48,exp2]⟩
theorem data666_lower_valid : ∀ j, (data666.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp0_valid
theorem data666_upper_valid : ∀ j, (data666.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data666_center_valid : ∀ j, (data666.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp2_valid
theorem margin666 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data666) 25)).lower := by
  decide +kernel
theorem positive666 {q : EdgeTriple} (hq : q ∈ box666.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data666)
    ⟨data666_lower_valid,data666_upper_valid⟩ 25 margin666 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box667 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data667 : S1TaylorBoxData := ⟨box667,![exp50,exp46,exp4],![exp54,exp50,exp10],![exp52,exp48,exp6]⟩
theorem data667_lower_valid : ∀ j, (data667.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data667_upper_valid : ∀ j, (data667.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data667_center_valid : ∀ j, (data667.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp6_valid
theorem margin667 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data667 25 := by decide +kernel
theorem positive667 {q : EdgeTriple} (hq : q ∈ box667.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data667 25
    data667_lower_valid data667_upper_valid data667_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin667 hq

def box668 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data668 : S1TaylorBoxData := ⟨box668,![exp50,exp50,exp0],![exp54,exp54,exp4],![exp52,exp52,exp2]⟩
theorem data668_lower_valid : ∀ j, (data668.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp0_valid
theorem data668_upper_valid : ∀ j, (data668.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data668_center_valid : ∀ j, (data668.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp2_valid
theorem margin668 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data668) 25)).lower := by
  decide +kernel
theorem positive668 {q : EdgeTriple} (hq : q ∈ box668.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data668)
    ⟨data668_lower_valid,data668_upper_valid⟩ 25 margin668 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box669 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data669 : S1TaylorBoxData := ⟨box669,![exp50,exp50,exp4],![exp54,exp54,exp10],![exp52,exp52,exp6]⟩
theorem data669_lower_valid : ∀ j, (data669.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data669_upper_valid : ∀ j, (data669.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data669_center_valid : ∀ j, (data669.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp6_valid
theorem margin669 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data669 25 := by decide +kernel
theorem positive669 {q : EdgeTriple} (hq : q ∈ box669.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data669 25
    data669_lower_valid data669_upper_valid data669_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin669 hq

def box670 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data670 : S1TaylorBoxData := ⟨box670,![exp46,exp46,exp10],![exp50,exp50,exp18],![exp48,exp48,exp14]⟩
theorem data670_lower_valid : ∀ j, (data670.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data670_upper_valid : ∀ j, (data670.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data670_center_valid : ∀ j, (data670.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp14_valid
theorem margin670 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data670 25 := by decide +kernel
theorem positive670 {q : EdgeTriple} (hq : q ∈ box670.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data670 25
    data670_lower_valid data670_upper_valid data670_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin670 hq

def box671 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data671 : S1TaylorBoxData := ⟨box671,![exp46,exp46,exp18],![exp50,exp50,exp22],![exp48,exp48,exp20]⟩
theorem data671_lower_valid : ∀ j, (data671.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data671_upper_valid : ∀ j, (data671.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data671_center_valid : ∀ j, (data671.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp20_valid
theorem margin671 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data671 25 := by decide +kernel
theorem positive671 {q : EdgeTriple} (hq : q ∈ box671.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data671 25
    data671_lower_valid data671_upper_valid data671_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin671 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

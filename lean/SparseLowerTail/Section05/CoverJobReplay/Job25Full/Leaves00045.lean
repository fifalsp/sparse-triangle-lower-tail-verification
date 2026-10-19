import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box720 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data720 : S1TaylorBoxData := ⟨box720,![exp58,exp42,exp0],![exp62,exp46,exp4],![exp60,exp44,exp2]⟩
theorem data720_lower_valid : ∀ j, (data720.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp0_valid
theorem data720_upper_valid : ∀ j, (data720.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data720_center_valid : ∀ j, (data720.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp2_valid
theorem margin720 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data720) 25)).lower := by
  decide +kernel
theorem positive720 {q : EdgeTriple} (hq : q ∈ box720.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data720)
    ⟨data720_lower_valid,data720_upper_valid⟩ 25 margin720 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box721 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data721 : S1TaylorBoxData := ⟨box721,![exp58,exp42,exp4],![exp62,exp46,exp10],![exp60,exp44,exp6]⟩
theorem data721_lower_valid : ∀ j, (data721.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data721_upper_valid : ∀ j, (data721.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data721_center_valid : ∀ j, (data721.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp6_valid
theorem margin721 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data721 25 := by decide +kernel
theorem positive721 {q : EdgeTriple} (hq : q ∈ box721.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data721 25
    data721_lower_valid data721_upper_valid data721_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin721 hq

def box722 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data722 : S1TaylorBoxData := ⟨box722,![exp54,exp38,exp10],![exp58,exp42,exp18],![exp56,exp40,exp14]⟩
theorem data722_lower_valid : ∀ j, (data722.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data722_upper_valid : ∀ j, (data722.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data722_center_valid : ∀ j, (data722.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin722 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data722 25 := by decide +kernel
theorem positive722 {q : EdgeTriple} (hq : q ∈ box722.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data722 25
    data722_lower_valid data722_upper_valid data722_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin722 hq

def box723 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data723 : S1TaylorBoxData := ⟨box723,![exp54,exp38,exp18],![exp58,exp42,exp22],![exp56,exp40,exp20]⟩
theorem data723_lower_valid : ∀ j, (data723.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data723_upper_valid : ∀ j, (data723.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data723_center_valid : ∀ j, (data723.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin723 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data723 25 := by decide +kernel
theorem positive723 {q : EdgeTriple} (hq : q ∈ box723.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data723 25
    data723_lower_valid data723_upper_valid data723_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin723 hq

def box724 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data724 : S1TaylorBoxData := ⟨box724,![exp54,exp42,exp10],![exp58,exp46,exp18],![exp56,exp44,exp14]⟩
theorem data724_lower_valid : ∀ j, (data724.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data724_upper_valid : ∀ j, (data724.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data724_center_valid : ∀ j, (data724.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp14_valid
theorem margin724 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data724 25 := by decide +kernel
theorem positive724 {q : EdgeTriple} (hq : q ∈ box724.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data724 25
    data724_lower_valid data724_upper_valid data724_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin724 hq

def box725 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data725 : S1TaylorBoxData := ⟨box725,![exp54,exp42,exp18],![exp58,exp46,exp22],![exp56,exp44,exp20]⟩
theorem data725_lower_valid : ∀ j, (data725.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data725_upper_valid : ∀ j, (data725.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data725_center_valid : ∀ j, (data725.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp20_valid
theorem margin725 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data725 25 := by decide +kernel
theorem positive725 {q : EdgeTriple} (hq : q ∈ box725.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data725 25
    data725_lower_valid data725_upper_valid data725_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin725 hq

def box726 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data726 : S1TaylorBoxData := ⟨box726,![exp58,exp38,exp10],![exp62,exp42,exp18],![exp60,exp40,exp14]⟩
theorem data726_lower_valid : ∀ j, (data726.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data726_upper_valid : ∀ j, (data726.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data726_center_valid : ∀ j, (data726.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin726 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data726 25 := by decide +kernel
theorem positive726 {q : EdgeTriple} (hq : q ∈ box726.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data726 25
    data726_lower_valid data726_upper_valid data726_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin726 hq

def box727 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data727 : S1TaylorBoxData := ⟨box727,![exp58,exp38,exp18],![exp62,exp42,exp22],![exp60,exp40,exp20]⟩
theorem data727_lower_valid : ∀ j, (data727.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data727_upper_valid : ∀ j, (data727.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data727_center_valid : ∀ j, (data727.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin727 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data727 25 := by decide +kernel
theorem positive727 {q : EdgeTriple} (hq : q ∈ box727.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data727 25
    data727_lower_valid data727_upper_valid data727_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin727 hq

def box728 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data728 : S1TaylorBoxData := ⟨box728,![exp58,exp42,exp10],![exp62,exp46,exp18],![exp60,exp44,exp14]⟩
theorem data728_lower_valid : ∀ j, (data728.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data728_upper_valid : ∀ j, (data728.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data728_center_valid : ∀ j, (data728.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp14_valid
theorem margin728 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data728 25 := by decide +kernel
theorem positive728 {q : EdgeTriple} (hq : q ∈ box728.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data728 25
    data728_lower_valid data728_upper_valid data728_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin728 hq

def box729 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data729 : S1TaylorBoxData := ⟨box729,![exp58,exp42,exp18],![exp62,exp46,exp22],![exp60,exp44,exp20]⟩
theorem data729_lower_valid : ∀ j, (data729.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data729_upper_valid : ∀ j, (data729.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data729_center_valid : ∀ j, (data729.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp20_valid
theorem margin729 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data729 25 := by decide +kernel
theorem positive729 {q : EdgeTriple} (hq : q ∈ box729.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data729 25
    data729_lower_valid data729_upper_valid data729_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin729 hq

def box730 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data730 : S1TaylorBoxData := ⟨box730,![exp54,exp46,exp0],![exp58,exp50,exp4],![exp56,exp48,exp2]⟩
theorem data730_lower_valid : ∀ j, (data730.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp0_valid
theorem data730_upper_valid : ∀ j, (data730.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data730_center_valid : ∀ j, (data730.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp2_valid
theorem margin730 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data730) 25)).lower := by
  decide +kernel
theorem positive730 {q : EdgeTriple} (hq : q ∈ box730.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data730)
    ⟨data730_lower_valid,data730_upper_valid⟩ 25 margin730 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box731 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data731 : S1TaylorBoxData := ⟨box731,![exp54,exp46,exp4],![exp58,exp50,exp10],![exp56,exp48,exp6]⟩
theorem data731_lower_valid : ∀ j, (data731.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data731_upper_valid : ∀ j, (data731.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data731_center_valid : ∀ j, (data731.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp6_valid
theorem margin731 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data731 25 := by decide +kernel
theorem positive731 {q : EdgeTriple} (hq : q ∈ box731.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data731 25
    data731_lower_valid data731_upper_valid data731_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin731 hq

def box732 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data732 : S1TaylorBoxData := ⟨box732,![exp54,exp50,exp0],![exp58,exp54,exp4],![exp56,exp52,exp2]⟩
theorem data732_lower_valid : ∀ j, (data732.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp0_valid
theorem data732_upper_valid : ∀ j, (data732.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data732_center_valid : ∀ j, (data732.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp2_valid
theorem margin732 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data732) 25)).lower := by
  decide +kernel
theorem positive732 {q : EdgeTriple} (hq : q ∈ box732.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data732)
    ⟨data732_lower_valid,data732_upper_valid⟩ 25 margin732 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box733 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data733 : S1TaylorBoxData := ⟨box733,![exp54,exp50,exp4],![exp58,exp54,exp10],![exp56,exp52,exp6]⟩
theorem data733_lower_valid : ∀ j, (data733.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data733_upper_valid : ∀ j, (data733.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data733_center_valid : ∀ j, (data733.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp6_valid
theorem margin733 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data733 25 := by decide +kernel
theorem positive733 {q : EdgeTriple} (hq : q ∈ box733.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data733 25
    data733_lower_valid data733_upper_valid data733_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin733 hq

def box734 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data734 : S1TaylorBoxData := ⟨box734,![exp58,exp46,exp0],![exp62,exp50,exp4],![exp60,exp48,exp2]⟩
theorem data734_lower_valid : ∀ j, (data734.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp0_valid
theorem data734_upper_valid : ∀ j, (data734.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data734_center_valid : ∀ j, (data734.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp2_valid
theorem margin734 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data734) 25)).lower := by
  decide +kernel
theorem positive734 {q : EdgeTriple} (hq : q ∈ box734.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data734)
    ⟨data734_lower_valid,data734_upper_valid⟩ 25 margin734 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box735 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data735 : S1TaylorBoxData := ⟨box735,![exp58,exp46,exp4],![exp62,exp50,exp10],![exp60,exp48,exp6]⟩
theorem data735_lower_valid : ∀ j, (data735.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data735_upper_valid : ∀ j, (data735.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data735_center_valid : ∀ j, (data735.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp6_valid
theorem margin735 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data735 25 := by decide +kernel
theorem positive735 {q : EdgeTriple} (hq : q ∈ box735.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data735 25
    data735_lower_valid data735_upper_valid data735_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin735 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

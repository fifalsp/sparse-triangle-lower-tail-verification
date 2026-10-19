import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box832 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data832 : S1TaylorBoxData := ⟨box832,![exp58,exp54,exp18],![exp62,exp58,exp22],![exp60,exp56,exp20]⟩
theorem data832_lower_valid : ∀ j, (data832.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data832_upper_valid : ∀ j, (data832.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp22_valid
theorem data832_center_valid : ∀ j, (data832.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp20_valid
theorem margin832 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data832 25 := by decide +kernel
theorem positive832 {q : EdgeTriple} (hq : q ∈ box832.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data832 25
    data832_lower_valid data832_upper_valid data832_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin832 hq

def box833 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data833 : S1TaylorBoxData := ⟨box833,![exp58,exp58,exp10],![exp62,exp62,exp18],![exp60,exp60,exp14]⟩
theorem data833_lower_valid : ∀ j, (data833.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp10_valid
theorem data833_upper_valid : ∀ j, (data833.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp18_valid
theorem data833_center_valid : ∀ j, (data833.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp14_valid
theorem margin833 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data833 25 := by decide +kernel
theorem positive833 {q : EdgeTriple} (hq : q ∈ box833.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data833 25
    data833_lower_valid data833_upper_valid data833_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin833 hq

def box834 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data834 : S1TaylorBoxData := ⟨box834,![exp58,exp58,exp18],![exp62,exp62,exp22],![exp60,exp60,exp20]⟩
theorem data834_lower_valid : ∀ j, (data834.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp18_valid
theorem data834_upper_valid : ∀ j, (data834.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp22_valid
theorem data834_center_valid : ∀ j, (data834.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp20_valid
theorem margin834 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data834 25 := by decide +kernel
theorem positive834 {q : EdgeTriple} (hq : q ∈ box834.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data834 25
    data834_lower_valid data834_upper_valid data834_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin834 hq

def box835 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(20891/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data835 : S1TaylorBoxData := ⟨box835,![exp62,exp54,exp0],![exp66,exp58,exp4],![exp64,exp56,exp2]⟩
theorem data835_lower_valid : ∀ j, (data835.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp0_valid
theorem data835_upper_valid : ∀ j, (data835.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp4_valid
theorem data835_center_valid : ∀ j, (data835.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp56_valid
  · exact exp2_valid
theorem margin835 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data835) 25)).lower := by
  decide +kernel
theorem positive835 {q : EdgeTriple} (hq : q ∈ box835.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data835)
    ⟨data835_lower_valid,data835_upper_valid⟩ 25 margin835 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box836 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(20891/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data836 : S1TaylorBoxData := ⟨box836,![exp62,exp54,exp4],![exp66,exp58,exp10],![exp64,exp56,exp6]⟩
theorem data836_lower_valid : ∀ j, (data836.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data836_upper_valid : ∀ j, (data836.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp10_valid
theorem data836_center_valid : ∀ j, (data836.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp56_valid
  · exact exp6_valid
theorem margin836 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data836 25 := by decide +kernel
theorem positive836 {q : EdgeTriple} (hq : q ∈ box836.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data836 25
    data836_lower_valid data836_upper_valid data836_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin836 hq

def box837 : LogBox := ⟨![(11249/2048 : ℚ),(20891/4096 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(11249/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data837 : S1TaylorBoxData := ⟨box837,![exp62,exp58,exp0],![exp66,exp62,exp4],![exp64,exp60,exp2]⟩
theorem data837_lower_valid : ∀ j, (data837.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp0_valid
theorem data837_upper_valid : ∀ j, (data837.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp4_valid
theorem data837_center_valid : ∀ j, (data837.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp60_valid
  · exact exp2_valid
theorem margin837 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data837) 25)).lower := by
  decide +kernel
theorem positive837 {q : EdgeTriple} (hq : q ∈ box837.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data837)
    ⟨data837_lower_valid,data837_upper_valid⟩ 25 margin837 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box838 : LogBox := ⟨![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(11249/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data838 : S1TaylorBoxData := ⟨box838,![exp62,exp58,exp4],![exp66,exp62,exp10],![exp64,exp60,exp6]⟩
theorem data838_lower_valid : ∀ j, (data838.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp4_valid
theorem data838_upper_valid : ∀ j, (data838.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp10_valid
theorem data838_center_valid : ∀ j, (data838.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp60_valid
  · exact exp6_valid
theorem margin838 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data838 25 := by decide +kernel
theorem positive838 {q : EdgeTriple} (hq : q ∈ box838.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data838 25
    data838_lower_valid data838_upper_valid data838_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin838 hq

def box839 : LogBox := ⟨![(24105/4096 : ℚ),(4821/1024 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(20891/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data839 : S1TaylorBoxData := ⟨box839,![exp66,exp54,exp0],![exp70,exp58,exp4],![exp68,exp56,exp2]⟩
theorem data839_lower_valid : ∀ j, (data839.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp0_valid
theorem data839_upper_valid : ∀ j, (data839.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp58_valid
  · exact exp4_valid
theorem data839_center_valid : ∀ j, (data839.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp56_valid
  · exact exp2_valid
theorem margin839 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data839) 25)).lower := by
  decide +kernel
theorem positive839 {q : EdgeTriple} (hq : q ∈ box839.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data839)
    ⟨data839_lower_valid,data839_upper_valid⟩ 25 margin839 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box840 : LogBox := ⟨![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(20891/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data840 : S1TaylorBoxData := ⟨box840,![exp66,exp54,exp4],![exp70,exp58,exp10],![exp68,exp56,exp6]⟩
theorem data840_lower_valid : ∀ j, (data840.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data840_upper_valid : ∀ j, (data840.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp58_valid
  · exact exp10_valid
theorem data840_center_valid : ∀ j, (data840.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp56_valid
  · exact exp6_valid
theorem margin840 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data840 25 := by decide +kernel
theorem positive840 {q : EdgeTriple} (hq : q ∈ box840.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data840 25
    data840_lower_valid data840_upper_valid data840_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin840 hq

def box841 : LogBox := ⟨![(24105/4096 : ℚ),(20891/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data841 : S1TaylorBoxData := ⟨box841,![exp66,exp58,exp0],![exp70,exp62,exp4],![exp68,exp60,exp2]⟩
theorem data841_lower_valid : ∀ j, (data841.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp0_valid
theorem data841_upper_valid : ∀ j, (data841.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp4_valid
theorem data841_center_valid : ∀ j, (data841.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp60_valid
  · exact exp2_valid
theorem margin841 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data841) 25)).lower := by
  decide +kernel
theorem positive841 {q : EdgeTriple} (hq : q ∈ box841.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data841)
    ⟨data841_lower_valid,data841_upper_valid⟩ 25 margin841 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box842 : LogBox := ⟨![(24105/4096 : ℚ),(20891/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data842 : S1TaylorBoxData := ⟨box842,![exp66,exp58,exp4],![exp70,exp62,exp10],![exp68,exp60,exp6]⟩
theorem data842_lower_valid : ∀ j, (data842.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp4_valid
theorem data842_upper_valid : ∀ j, (data842.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp10_valid
theorem data842_center_valid : ∀ j, (data842.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp60_valid
  · exact exp6_valid
theorem margin842 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data842 25 := by decide +kernel
theorem positive842 {q : EdgeTriple} (hq : q ∈ box842.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data842 25
    data842_lower_valid data842_upper_valid data842_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin842 hq

def box843 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(20891/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data843 : S1TaylorBoxData := ⟨box843,![exp62,exp54,exp10],![exp66,exp58,exp18],![exp64,exp56,exp14]⟩
theorem data843_lower_valid : ∀ j, (data843.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data843_upper_valid : ∀ j, (data843.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp18_valid
theorem data843_center_valid : ∀ j, (data843.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp56_valid
  · exact exp14_valid
theorem margin843 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data843 25 := by decide +kernel
theorem positive843 {q : EdgeTriple} (hq : q ∈ box843.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data843 25
    data843_lower_valid data843_upper_valid data843_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin843 hq

def box844 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(20891/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data844 : S1TaylorBoxData := ⟨box844,![exp62,exp54,exp18],![exp66,exp58,exp22],![exp64,exp56,exp20]⟩
theorem data844_lower_valid : ∀ j, (data844.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data844_upper_valid : ∀ j, (data844.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp22_valid
theorem data844_center_valid : ∀ j, (data844.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp56_valid
  · exact exp20_valid
theorem margin844 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data844 25 := by decide +kernel
theorem positive844 {q : EdgeTriple} (hq : q ∈ box844.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data844 25
    data844_lower_valid data844_upper_valid data844_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin844 hq

def box845 : LogBox := ⟨![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(11249/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data845 : S1TaylorBoxData := ⟨box845,![exp62,exp58,exp10],![exp66,exp62,exp18],![exp64,exp60,exp14]⟩
theorem data845_lower_valid : ∀ j, (data845.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp10_valid
theorem data845_upper_valid : ∀ j, (data845.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp18_valid
theorem data845_center_valid : ∀ j, (data845.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp60_valid
  · exact exp14_valid
theorem margin845 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data845 25 := by decide +kernel
theorem positive845 {q : EdgeTriple} (hq : q ∈ box845.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data845 25
    data845_lower_valid data845_upper_valid data845_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin845 hq

def box846 : LogBox := ⟨![(11249/2048 : ℚ),(20891/4096 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(11249/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data846 : S1TaylorBoxData := ⟨box846,![exp62,exp58,exp18],![exp66,exp62,exp22],![exp64,exp60,exp20]⟩
theorem data846_lower_valid : ∀ j, (data846.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp18_valid
theorem data846_upper_valid : ∀ j, (data846.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp22_valid
theorem data846_center_valid : ∀ j, (data846.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp60_valid
  · exact exp20_valid
theorem margin846 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data846 25 := by decide +kernel
theorem positive846 {q : EdgeTriple} (hq : q ∈ box846.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data846 25
    data846_lower_valid data846_upper_valid data846_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin846 hq

def box847 : LogBox := ⟨![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(20891/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data847 : S1TaylorBoxData := ⟨box847,![exp66,exp54,exp10],![exp70,exp58,exp18],![exp68,exp56,exp14]⟩
theorem data847_lower_valid : ∀ j, (data847.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data847_upper_valid : ∀ j, (data847.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp58_valid
  · exact exp18_valid
theorem data847_center_valid : ∀ j, (data847.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp56_valid
  · exact exp14_valid
theorem margin847 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data847 25 := by decide +kernel
theorem positive847 {q : EdgeTriple} (hq : q ∈ box847.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data847 25
    data847_lower_valid data847_upper_valid data847_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin847 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

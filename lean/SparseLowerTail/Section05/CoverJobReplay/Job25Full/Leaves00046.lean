import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box736 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data736 : S1TaylorBoxData := ⟨box736,![exp58,exp50,exp0],![exp62,exp54,exp4],![exp60,exp52,exp2]⟩
theorem data736_lower_valid : ∀ j, (data736.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp0_valid
theorem data736_upper_valid : ∀ j, (data736.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data736_center_valid : ∀ j, (data736.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp2_valid
theorem margin736 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data736) 25)).lower := by
  decide +kernel
theorem positive736 {q : EdgeTriple} (hq : q ∈ box736.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data736)
    ⟨data736_lower_valid,data736_upper_valid⟩ 25 margin736 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box737 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data737 : S1TaylorBoxData := ⟨box737,![exp58,exp50,exp4],![exp62,exp54,exp10],![exp60,exp52,exp6]⟩
theorem data737_lower_valid : ∀ j, (data737.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data737_upper_valid : ∀ j, (data737.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data737_center_valid : ∀ j, (data737.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp6_valid
theorem margin737 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data737 25 := by decide +kernel
theorem positive737 {q : EdgeTriple} (hq : q ∈ box737.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data737 25
    data737_lower_valid data737_upper_valid data737_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin737 hq

def box738 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data738 : S1TaylorBoxData := ⟨box738,![exp54,exp46,exp10],![exp58,exp50,exp18],![exp56,exp48,exp14]⟩
theorem data738_lower_valid : ∀ j, (data738.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data738_upper_valid : ∀ j, (data738.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data738_center_valid : ∀ j, (data738.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp14_valid
theorem margin738 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data738 25 := by decide +kernel
theorem positive738 {q : EdgeTriple} (hq : q ∈ box738.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data738 25
    data738_lower_valid data738_upper_valid data738_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin738 hq

def box739 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data739 : S1TaylorBoxData := ⟨box739,![exp54,exp46,exp18],![exp58,exp50,exp22],![exp56,exp48,exp20]⟩
theorem data739_lower_valid : ∀ j, (data739.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data739_upper_valid : ∀ j, (data739.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data739_center_valid : ∀ j, (data739.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp20_valid
theorem margin739 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data739 25 := by decide +kernel
theorem positive739 {q : EdgeTriple} (hq : q ∈ box739.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data739 25
    data739_lower_valid data739_upper_valid data739_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin739 hq

def box740 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data740 : S1TaylorBoxData := ⟨box740,![exp54,exp50,exp10],![exp58,exp54,exp18],![exp56,exp52,exp14]⟩
theorem data740_lower_valid : ∀ j, (data740.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data740_upper_valid : ∀ j, (data740.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data740_center_valid : ∀ j, (data740.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp14_valid
theorem margin740 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data740 25 := by decide +kernel
theorem positive740 {q : EdgeTriple} (hq : q ∈ box740.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data740 25
    data740_lower_valid data740_upper_valid data740_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin740 hq

def box741 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data741 : S1TaylorBoxData := ⟨box741,![exp54,exp50,exp18],![exp58,exp54,exp22],![exp56,exp52,exp20]⟩
theorem data741_lower_valid : ∀ j, (data741.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data741_upper_valid : ∀ j, (data741.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data741_center_valid : ∀ j, (data741.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp20_valid
theorem margin741 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data741 25 := by decide +kernel
theorem positive741 {q : EdgeTriple} (hq : q ∈ box741.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data741 25
    data741_lower_valid data741_upper_valid data741_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin741 hq

def box742 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data742 : S1TaylorBoxData := ⟨box742,![exp58,exp46,exp10],![exp62,exp50,exp18],![exp60,exp48,exp14]⟩
theorem data742_lower_valid : ∀ j, (data742.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data742_upper_valid : ∀ j, (data742.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data742_center_valid : ∀ j, (data742.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp14_valid
theorem margin742 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data742 25 := by decide +kernel
theorem positive742 {q : EdgeTriple} (hq : q ∈ box742.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data742 25
    data742_lower_valid data742_upper_valid data742_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin742 hq

def box743 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data743 : S1TaylorBoxData := ⟨box743,![exp58,exp46,exp18],![exp62,exp50,exp22],![exp60,exp48,exp20]⟩
theorem data743_lower_valid : ∀ j, (data743.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data743_upper_valid : ∀ j, (data743.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data743_center_valid : ∀ j, (data743.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp20_valid
theorem margin743 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data743 25 := by decide +kernel
theorem positive743 {q : EdgeTriple} (hq : q ∈ box743.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data743 25
    data743_lower_valid data743_upper_valid data743_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin743 hq

def box744 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data744 : S1TaylorBoxData := ⟨box744,![exp58,exp50,exp10],![exp62,exp54,exp18],![exp60,exp52,exp14]⟩
theorem data744_lower_valid : ∀ j, (data744.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data744_upper_valid : ∀ j, (data744.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data744_center_valid : ∀ j, (data744.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp14_valid
theorem margin744 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data744 25 := by decide +kernel
theorem positive744 {q : EdgeTriple} (hq : q ∈ box744.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data744 25
    data744_lower_valid data744_upper_valid data744_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin744 hq

def box745 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data745 : S1TaylorBoxData := ⟨box745,![exp58,exp50,exp18],![exp62,exp54,exp22],![exp60,exp52,exp20]⟩
theorem data745_lower_valid : ∀ j, (data745.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data745_upper_valid : ∀ j, (data745.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data745_center_valid : ∀ j, (data745.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp20_valid
theorem margin745 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data745 25 := by decide +kernel
theorem positive745 {q : EdgeTriple} (hq : q ∈ box745.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data745 25
    data745_lower_valid data745_upper_valid data745_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin745 hq

def box746 : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data746 : S1TaylorBoxData := ⟨box746,![exp62,exp38,exp0],![exp66,exp42,exp4],![exp64,exp40,exp2]⟩
theorem data746_lower_valid : ∀ j, (data746.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data746_upper_valid : ∀ j, (data746.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data746_center_valid : ∀ j, (data746.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin746 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data746) 25)).lower := by
  decide +kernel
theorem positive746 {q : EdgeTriple} (hq : q ∈ box746.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data746)
    ⟨data746_lower_valid,data746_upper_valid⟩ 25 margin746 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box747 : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data747 : S1TaylorBoxData := ⟨box747,![exp62,exp38,exp4],![exp66,exp42,exp10],![exp64,exp40,exp6]⟩
theorem data747_lower_valid : ∀ j, (data747.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data747_upper_valid : ∀ j, (data747.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data747_center_valid : ∀ j, (data747.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin747 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data747 25 := by decide +kernel
theorem positive747 {q : EdgeTriple} (hq : q ∈ box747.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data747 25
    data747_lower_valid data747_upper_valid data747_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin747 hq

def box748 : LogBox := ⟨![(11249/2048 : ℚ),(14463/4096 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data748 : S1TaylorBoxData := ⟨box748,![exp62,exp42,exp0],![exp66,exp46,exp4],![exp64,exp44,exp2]⟩
theorem data748_lower_valid : ∀ j, (data748.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp0_valid
theorem data748_upper_valid : ∀ j, (data748.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data748_center_valid : ∀ j, (data748.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp44_valid
  · exact exp2_valid
theorem margin748 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data748) 25)).lower := by
  decide +kernel
theorem positive748 {q : EdgeTriple} (hq : q ∈ box748.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data748)
    ⟨data748_lower_valid,data748_upper_valid⟩ 25 margin748 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box749 : LogBox := ⟨![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data749 : S1TaylorBoxData := ⟨box749,![exp62,exp42,exp4],![exp66,exp46,exp10],![exp64,exp44,exp6]⟩
theorem data749_lower_valid : ∀ j, (data749.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data749_upper_valid : ∀ j, (data749.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data749_center_valid : ∀ j, (data749.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp44_valid
  · exact exp6_valid
theorem margin749 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data749 25 := by decide +kernel
theorem positive749 {q : EdgeTriple} (hq : q ∈ box749.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data749 25
    data749_lower_valid data749_upper_valid data749_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin749 hq

def box750 : LogBox := ⟨![(24105/4096 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data750 : S1TaylorBoxData := ⟨box750,![exp66,exp38,exp0],![exp70,exp42,exp4],![exp68,exp40,exp2]⟩
theorem data750_lower_valid : ∀ j, (data750.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data750_upper_valid : ∀ j, (data750.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data750_center_valid : ∀ j, (data750.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin750 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data750) 25)).lower := by
  decide +kernel
theorem positive750 {q : EdgeTriple} (hq : q ∈ box750.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data750)
    ⟨data750_lower_valid,data750_upper_valid⟩ 25 margin750 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box751 : LogBox := ⟨![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data751 : S1TaylorBoxData := ⟨box751,![exp66,exp38,exp4],![exp70,exp42,exp10],![exp68,exp40,exp6]⟩
theorem data751_lower_valid : ∀ j, (data751.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data751_upper_valid : ∀ j, (data751.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data751_center_valid : ∀ j, (data751.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin751 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data751 25 := by decide +kernel
theorem positive751 {q : EdgeTriple} (hq : q ∈ box751.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data751 25
    data751_lower_valid data751_upper_valid data751_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin751 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

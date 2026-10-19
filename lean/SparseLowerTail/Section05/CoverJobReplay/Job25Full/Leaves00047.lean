import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box752 : LogBox := ⟨![(24105/4096 : ℚ),(14463/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data752 : S1TaylorBoxData := ⟨box752,![exp66,exp42,exp0],![exp70,exp46,exp4],![exp68,exp44,exp2]⟩
theorem data752_lower_valid : ∀ j, (data752.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp0_valid
theorem data752_upper_valid : ∀ j, (data752.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data752_center_valid : ∀ j, (data752.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp44_valid
  · exact exp2_valid
theorem margin752 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data752) 25)).lower := by
  decide +kernel
theorem positive752 {q : EdgeTriple} (hq : q ∈ box752.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data752)
    ⟨data752_lower_valid,data752_upper_valid⟩ 25 margin752 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box753 : LogBox := ⟨![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data753 : S1TaylorBoxData := ⟨box753,![exp66,exp42,exp4],![exp70,exp46,exp10],![exp68,exp44,exp6]⟩
theorem data753_lower_valid : ∀ j, (data753.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data753_upper_valid : ∀ j, (data753.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data753_center_valid : ∀ j, (data753.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp44_valid
  · exact exp6_valid
theorem margin753 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data753 25 := by decide +kernel
theorem positive753 {q : EdgeTriple} (hq : q ∈ box753.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data753 25
    data753_lower_valid data753_upper_valid data753_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin753 hq

def box754 : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data754 : S1TaylorBoxData := ⟨box754,![exp62,exp38,exp10],![exp66,exp42,exp18],![exp64,exp40,exp14]⟩
theorem data754_lower_valid : ∀ j, (data754.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data754_upper_valid : ∀ j, (data754.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data754_center_valid : ∀ j, (data754.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin754 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data754 25 := by decide +kernel
theorem positive754 {q : EdgeTriple} (hq : q ∈ box754.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data754 25
    data754_lower_valid data754_upper_valid data754_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin754 hq

def box755 : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data755 : S1TaylorBoxData := ⟨box755,![exp62,exp38,exp18],![exp66,exp42,exp22],![exp64,exp40,exp20]⟩
theorem data755_lower_valid : ∀ j, (data755.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data755_upper_valid : ∀ j, (data755.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data755_center_valid : ∀ j, (data755.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin755 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data755 25 := by decide +kernel
theorem positive755 {q : EdgeTriple} (hq : q ∈ box755.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data755 25
    data755_lower_valid data755_upper_valid data755_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin755 hq

def box756 : LogBox := ⟨![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data756 : S1TaylorBoxData := ⟨box756,![exp62,exp42,exp10],![exp66,exp46,exp18],![exp64,exp44,exp14]⟩
theorem data756_lower_valid : ∀ j, (data756.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data756_upper_valid : ∀ j, (data756.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data756_center_valid : ∀ j, (data756.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp44_valid
  · exact exp14_valid
theorem margin756 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data756 25 := by decide +kernel
theorem positive756 {q : EdgeTriple} (hq : q ∈ box756.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data756 25
    data756_lower_valid data756_upper_valid data756_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin756 hq

def box757 : LogBox := ⟨![(11249/2048 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data757 : S1TaylorBoxData := ⟨box757,![exp62,exp42,exp18],![exp66,exp46,exp22],![exp64,exp44,exp20]⟩
theorem data757_lower_valid : ∀ j, (data757.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data757_upper_valid : ∀ j, (data757.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data757_center_valid : ∀ j, (data757.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp44_valid
  · exact exp20_valid
theorem margin757 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data757 25 := by decide +kernel
theorem positive757 {q : EdgeTriple} (hq : q ∈ box757.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data757 25
    data757_lower_valid data757_upper_valid data757_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin757 hq

def box758 : LogBox := ⟨![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data758 : S1TaylorBoxData := ⟨box758,![exp66,exp38,exp10],![exp70,exp42,exp18],![exp68,exp40,exp14]⟩
theorem data758_lower_valid : ∀ j, (data758.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data758_upper_valid : ∀ j, (data758.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data758_center_valid : ∀ j, (data758.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp40_valid
  · exact exp14_valid
theorem margin758 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data758 25 := by decide +kernel
theorem positive758 {q : EdgeTriple} (hq : q ∈ box758.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data758 25
    data758_lower_valid data758_upper_valid data758_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin758 hq

def box759 : LogBox := ⟨![(24105/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data759 : S1TaylorBoxData := ⟨box759,![exp66,exp38,exp18],![exp70,exp42,exp22],![exp68,exp40,exp20]⟩
theorem data759_lower_valid : ∀ j, (data759.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data759_upper_valid : ∀ j, (data759.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data759_center_valid : ∀ j, (data759.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp40_valid
  · exact exp20_valid
theorem margin759 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data759 25 := by decide +kernel
theorem positive759 {q : EdgeTriple} (hq : q ∈ box759.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data759 25
    data759_lower_valid data759_upper_valid data759_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin759 hq

def box760 : LogBox := ⟨![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data760 : S1TaylorBoxData := ⟨box760,![exp66,exp42,exp10],![exp70,exp46,exp18],![exp68,exp44,exp14]⟩
theorem data760_lower_valid : ∀ j, (data760.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data760_upper_valid : ∀ j, (data760.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data760_center_valid : ∀ j, (data760.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp44_valid
  · exact exp14_valid
theorem margin760 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data760 25 := by decide +kernel
theorem positive760 {q : EdgeTriple} (hq : q ∈ box760.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data760 25
    data760_lower_valid data760_upper_valid data760_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin760 hq

def box761 : LogBox := ⟨![(24105/4096 : ℚ),(14463/4096 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data761 : S1TaylorBoxData := ⟨box761,![exp66,exp42,exp18],![exp70,exp46,exp22],![exp68,exp44,exp20]⟩
theorem data761_lower_valid : ∀ j, (data761.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp18_valid
theorem data761_upper_valid : ∀ j, (data761.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data761_center_valid : ∀ j, (data761.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp44_valid
  · exact exp20_valid
theorem margin761 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data761 25 := by decide +kernel
theorem positive761 {q : EdgeTriple} (hq : q ∈ box761.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data761 25
    data761_lower_valid data761_upper_valid data761_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin761 hq

def box762 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data762 : S1TaylorBoxData := ⟨box762,![exp62,exp46,exp0],![exp66,exp50,exp4],![exp64,exp48,exp2]⟩
theorem data762_lower_valid : ∀ j, (data762.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp0_valid
theorem data762_upper_valid : ∀ j, (data762.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data762_center_valid : ∀ j, (data762.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp2_valid
theorem margin762 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data762) 25)).lower := by
  decide +kernel
theorem positive762 {q : EdgeTriple} (hq : q ∈ box762.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data762)
    ⟨data762_lower_valid,data762_upper_valid⟩ 25 margin762 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box763 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data763 : S1TaylorBoxData := ⟨box763,![exp62,exp46,exp4],![exp66,exp50,exp10],![exp64,exp48,exp6]⟩
theorem data763_lower_valid : ∀ j, (data763.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data763_upper_valid : ∀ j, (data763.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data763_center_valid : ∀ j, (data763.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp6_valid
theorem margin763 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data763 25 := by decide +kernel
theorem positive763 {q : EdgeTriple} (hq : q ∈ box763.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data763 25
    data763_lower_valid data763_upper_valid data763_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin763 hq

def box764 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data764 : S1TaylorBoxData := ⟨box764,![exp62,exp50,exp0],![exp66,exp54,exp4],![exp64,exp52,exp2]⟩
theorem data764_lower_valid : ∀ j, (data764.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp0_valid
theorem data764_upper_valid : ∀ j, (data764.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data764_center_valid : ∀ j, (data764.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp2_valid
theorem margin764 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data764) 25)).lower := by
  decide +kernel
theorem positive764 {q : EdgeTriple} (hq : q ∈ box764.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data764)
    ⟨data764_lower_valid,data764_upper_valid⟩ 25 margin764 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box765 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data765 : S1TaylorBoxData := ⟨box765,![exp62,exp50,exp4],![exp66,exp54,exp10],![exp64,exp52,exp6]⟩
theorem data765_lower_valid : ∀ j, (data765.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data765_upper_valid : ∀ j, (data765.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data765_center_valid : ∀ j, (data765.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp6_valid
theorem margin765 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data765 25 := by decide +kernel
theorem positive765 {q : EdgeTriple} (hq : q ∈ box765.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data765 25
    data765_lower_valid data765_upper_valid data765_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin765 hq

def box766 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data766 : S1TaylorBoxData := ⟨box766,![exp66,exp46,exp0],![exp70,exp50,exp4],![exp68,exp48,exp2]⟩
theorem data766_lower_valid : ∀ j, (data766.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp0_valid
theorem data766_upper_valid : ∀ j, (data766.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data766_center_valid : ∀ j, (data766.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp48_valid
  · exact exp2_valid
theorem margin766 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data766) 25)).lower := by
  decide +kernel
theorem positive766 {q : EdgeTriple} (hq : q ∈ box766.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data766)
    ⟨data766_lower_valid,data766_upper_valid⟩ 25 margin766 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box767 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data767 : S1TaylorBoxData := ⟨box767,![exp66,exp46,exp4],![exp70,exp50,exp10],![exp68,exp48,exp6]⟩
theorem data767_lower_valid : ∀ j, (data767.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp4_valid
theorem data767_upper_valid : ∀ j, (data767.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data767_center_valid : ∀ j, (data767.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp48_valid
  · exact exp6_valid
theorem margin767 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data767 25 := by decide +kernel
theorem positive767 {q : EdgeTriple} (hq : q ∈ box767.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data767 25
    data767_lower_valid data767_upper_valid data767_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin767 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

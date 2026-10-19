import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box768 : LogBox := ⟨![(24105/4096 : ℚ),(17677/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data768 : S1TaylorBoxData := ⟨box768,![exp66,exp50,exp0],![exp70,exp54,exp4],![exp68,exp52,exp2]⟩
theorem data768_lower_valid : ∀ j, (data768.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp0_valid
theorem data768_upper_valid : ∀ j, (data768.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data768_center_valid : ∀ j, (data768.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp52_valid
  · exact exp2_valid
theorem margin768 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data768) 25)).lower := by
  decide +kernel
theorem positive768 {q : EdgeTriple} (hq : q ∈ box768.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data768)
    ⟨data768_lower_valid,data768_upper_valid⟩ 25 margin768 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box769 : LogBox := ⟨![(24105/4096 : ℚ),(17677/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data769 : S1TaylorBoxData := ⟨box769,![exp66,exp50,exp4],![exp70,exp54,exp10],![exp68,exp52,exp6]⟩
theorem data769_lower_valid : ∀ j, (data769.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp4_valid
theorem data769_upper_valid : ∀ j, (data769.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data769_center_valid : ∀ j, (data769.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp52_valid
  · exact exp6_valid
theorem margin769 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data769 25 := by decide +kernel
theorem positive769 {q : EdgeTriple} (hq : q ∈ box769.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data769 25
    data769_lower_valid data769_upper_valid data769_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin769 hq

def box770 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data770 : S1TaylorBoxData := ⟨box770,![exp62,exp46,exp10],![exp66,exp50,exp18],![exp64,exp48,exp14]⟩
theorem data770_lower_valid : ∀ j, (data770.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data770_upper_valid : ∀ j, (data770.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data770_center_valid : ∀ j, (data770.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp14_valid
theorem margin770 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data770 25 := by decide +kernel
theorem positive770 {q : EdgeTriple} (hq : q ∈ box770.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data770 25
    data770_lower_valid data770_upper_valid data770_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin770 hq

def box771 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data771 : S1TaylorBoxData := ⟨box771,![exp62,exp46,exp18],![exp66,exp50,exp22],![exp64,exp48,exp20]⟩
theorem data771_lower_valid : ∀ j, (data771.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data771_upper_valid : ∀ j, (data771.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data771_center_valid : ∀ j, (data771.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp20_valid
theorem margin771 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data771 25 := by decide +kernel
theorem positive771 {q : EdgeTriple} (hq : q ∈ box771.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data771 25
    data771_lower_valid data771_upper_valid data771_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin771 hq

def box772 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data772 : S1TaylorBoxData := ⟨box772,![exp62,exp50,exp10],![exp66,exp54,exp18],![exp64,exp52,exp14]⟩
theorem data772_lower_valid : ∀ j, (data772.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data772_upper_valid : ∀ j, (data772.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data772_center_valid : ∀ j, (data772.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp14_valid
theorem margin772 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data772 25 := by decide +kernel
theorem positive772 {q : EdgeTriple} (hq : q ∈ box772.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data772 25
    data772_lower_valid data772_upper_valid data772_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin772 hq

def box773 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data773 : S1TaylorBoxData := ⟨box773,![exp62,exp50,exp18],![exp66,exp54,exp22],![exp64,exp52,exp20]⟩
theorem data773_lower_valid : ∀ j, (data773.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data773_upper_valid : ∀ j, (data773.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data773_center_valid : ∀ j, (data773.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp20_valid
theorem margin773 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data773 25 := by decide +kernel
theorem positive773 {q : EdgeTriple} (hq : q ∈ box773.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data773 25
    data773_lower_valid data773_upper_valid data773_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin773 hq

def box774 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data774 : S1TaylorBoxData := ⟨box774,![exp66,exp46,exp10],![exp70,exp50,exp18],![exp68,exp48,exp14]⟩
theorem data774_lower_valid : ∀ j, (data774.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp10_valid
theorem data774_upper_valid : ∀ j, (data774.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data774_center_valid : ∀ j, (data774.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp48_valid
  · exact exp14_valid
theorem margin774 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data774 25 := by decide +kernel
theorem positive774 {q : EdgeTriple} (hq : q ∈ box774.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data774 25
    data774_lower_valid data774_upper_valid data774_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin774 hq

def box775 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data775 : S1TaylorBoxData := ⟨box775,![exp66,exp46,exp18],![exp70,exp50,exp22],![exp68,exp48,exp20]⟩
theorem data775_lower_valid : ∀ j, (data775.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp18_valid
theorem data775_upper_valid : ∀ j, (data775.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data775_center_valid : ∀ j, (data775.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp48_valid
  · exact exp20_valid
theorem margin775 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data775 25 := by decide +kernel
theorem positive775 {q : EdgeTriple} (hq : q ∈ box775.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data775 25
    data775_lower_valid data775_upper_valid data775_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin775 hq

def box776 : LogBox := ⟨![(24105/4096 : ℚ),(17677/4096 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data776 : S1TaylorBoxData := ⟨box776,![exp66,exp50,exp10],![exp70,exp54,exp18],![exp68,exp52,exp14]⟩
theorem data776_lower_valid : ∀ j, (data776.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp10_valid
theorem data776_upper_valid : ∀ j, (data776.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data776_center_valid : ∀ j, (data776.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp52_valid
  · exact exp14_valid
theorem margin776 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data776 25 := by decide +kernel
theorem positive776 {q : EdgeTriple} (hq : q ∈ box776.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data776 25
    data776_lower_valid data776_upper_valid data776_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin776 hq

def box777 : LogBox := ⟨![(24105/4096 : ℚ),(17677/4096 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data777 : S1TaylorBoxData := ⟨box777,![exp66,exp50,exp18],![exp70,exp54,exp22],![exp68,exp52,exp20]⟩
theorem data777_lower_valid : ∀ j, (data777.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp18_valid
theorem data777_upper_valid : ∀ j, (data777.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data777_center_valid : ∀ j, (data777.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp52_valid
  · exact exp20_valid
theorem margin777 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data777 25 := by decide +kernel
theorem positive777 {q : EdgeTriple} (hq : q ∈ box777.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data777 25
    data777_lower_valid data777_upper_valid data777_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin777 hq

def box778 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data778 : S1TaylorBoxData := ⟨box778,![exp54,exp38,exp22],![exp58,exp42,exp26],![exp56,exp40,exp24]⟩
theorem data778_lower_valid : ∀ j, (data778.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data778_upper_valid : ∀ j, (data778.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data778_center_valid : ∀ j, (data778.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp24_valid
theorem margin778 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data778 25 := by decide +kernel
theorem positive778 {q : EdgeTriple} (hq : q ∈ box778.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data778 25
    data778_lower_valid data778_upper_valid data778_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin778 hq

def box779 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(8035/4096 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data779 : S1TaylorBoxData := ⟨box779,![exp54,exp38,exp26],![exp58,exp42,exp30],![exp56,exp40,exp28]⟩
theorem data779_lower_valid : ∀ j, (data779.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp26_valid
theorem data779_upper_valid : ∀ j, (data779.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data779_center_valid : ∀ j, (data779.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp28_valid
theorem margin779 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data779 25 := by decide +kernel
theorem positive779 {q : EdgeTriple} (hq : q ∈ box779.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data779 25
    data779_lower_valid data779_upper_valid data779_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin779 hq

def box780 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(8035/4096 : ℚ)]⟩
def data780 : S1TaylorBoxData := ⟨box780,![exp54,exp42,exp22],![exp58,exp46,exp26],![exp56,exp44,exp24]⟩
theorem data780_lower_valid : ∀ j, (data780.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp22_valid
theorem data780_upper_valid : ∀ j, (data780.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp26_valid
theorem data780_center_valid : ∀ j, (data780.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp24_valid
theorem margin780 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data780 25 := by decide +kernel
theorem positive780 {q : EdgeTriple} (hq : q ∈ box780.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data780 25
    data780_lower_valid data780_upper_valid data780_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin780 hq

def box781 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data781 : S1TaylorBoxData := ⟨box781,![exp54,exp42,exp26],![exp58,exp46,exp30],![exp56,exp44,exp28]⟩
theorem data781_lower_valid : ∀ j, (data781.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data781_upper_valid : ∀ j, (data781.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data781_center_valid : ∀ j, (data781.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp28_valid
theorem margin781 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data781 25 := by decide +kernel
theorem positive781 {q : EdgeTriple} (hq : q ∈ box781.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data781 25
    data781_lower_valid data781_upper_valid data781_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin781 hq

def box782 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data782 : S1TaylorBoxData := ⟨box782,![exp58,exp38,exp22],![exp62,exp42,exp26],![exp60,exp40,exp24]⟩
theorem data782_lower_valid : ∀ j, (data782.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data782_upper_valid : ∀ j, (data782.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp26_valid
theorem data782_center_valid : ∀ j, (data782.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp24_valid
theorem margin782 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data782 25 := by decide +kernel
theorem positive782 {q : EdgeTriple} (hq : q ∈ box782.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data782 25
    data782_lower_valid data782_upper_valid data782_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin782 hq

def box783 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(8035/4096 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data783 : S1TaylorBoxData := ⟨box783,![exp58,exp38,exp26],![exp62,exp42,exp30],![exp60,exp40,exp28]⟩
theorem data783_lower_valid : ∀ j, (data783.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp26_valid
theorem data783_upper_valid : ∀ j, (data783.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data783_center_valid : ∀ j, (data783.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp28_valid
theorem margin783 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data783 25 := by decide +kernel
theorem positive783 {q : EdgeTriple} (hq : q ∈ box783.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data783 25
    data783_lower_valid data783_upper_valid data783_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin783 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

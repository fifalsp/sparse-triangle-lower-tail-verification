import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box816 : LogBox := ⟨![(24105/4096 : ℚ),(14463/4096 : ℚ),(4821/2048 : ℚ)],![(1607/256 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)]⟩
def data816 : S1TaylorBoxData := ⟨box816,![exp66,exp42,exp30],![exp70,exp46,exp38],![exp68,exp44,exp34]⟩
theorem data816_lower_valid : ∀ j, (data816.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp30_valid
theorem data816_upper_valid : ∀ j, (data816.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data816_center_valid : ∀ j, (data816.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp44_valid
  · exact exp34_valid
theorem margin816 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data816 25 := by decide +kernel
theorem positive816 {q : EdgeTriple} (hq : q ∈ box816.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data816 25
    data816_lower_valid data816_upper_valid data816_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin816 hq

def box817 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data817 : S1TaylorBoxData := ⟨box817,![exp62,exp46,exp22],![exp66,exp50,exp30],![exp64,exp48,exp26]⟩
theorem data817_lower_valid : ∀ j, (data817.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data817_upper_valid : ∀ j, (data817.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data817_center_valid : ∀ j, (data817.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp26_valid
theorem margin817 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data817 25 := by decide +kernel
theorem positive817 {q : EdgeTriple} (hq : q ∈ box817.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data817 25
    data817_lower_valid data817_upper_valid data817_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin817 hq

def box818 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)]⟩
def data818 : S1TaylorBoxData := ⟨box818,![exp62,exp50,exp22],![exp66,exp54,exp30],![exp64,exp52,exp26]⟩
theorem data818_lower_valid : ∀ j, (data818.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp22_valid
theorem data818_upper_valid : ∀ j, (data818.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data818_center_valid : ∀ j, (data818.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp26_valid
theorem margin818 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data818 25 := by decide +kernel
theorem positive818 {q : EdgeTriple} (hq : q ∈ box818.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data818 25
    data818_lower_valid data818_upper_valid data818_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin818 hq

def box819 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(4821/2048 : ℚ)]⟩
def data819 : S1TaylorBoxData := ⟨box819,![exp66,exp46,exp22],![exp70,exp54,exp30],![exp68,exp50,exp26]⟩
theorem data819_lower_valid : ∀ j, (data819.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp22_valid
theorem data819_upper_valid : ∀ j, (data819.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp30_valid
theorem data819_center_valid : ∀ j, (data819.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp50_valid
  · exact exp26_valid
theorem margin819 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data819 25 := by decide +kernel
theorem positive819 {q : EdgeTriple} (hq : q ∈ box819.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data819 25
    data819_lower_valid data819_upper_valid data819_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin819 hq

def box820 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)]⟩
def data820 : S1TaylorBoxData := ⟨box820,![exp62,exp46,exp30],![exp66,exp50,exp38],![exp64,exp48,exp34]⟩
theorem data820_lower_valid : ∀ j, (data820.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data820_upper_valid : ∀ j, (data820.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data820_center_valid : ∀ j, (data820.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp34_valid
theorem margin820 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data820 25 := by decide +kernel
theorem positive820 {q : EdgeTriple} (hq : q ∈ box820.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data820 25
    data820_lower_valid data820_upper_valid data820_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin820 hq

def box821 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def data821 : S1TaylorBoxData := ⟨box821,![exp62,exp50,exp30],![exp66,exp54,exp38],![exp64,exp52,exp34]⟩
theorem data821_lower_valid : ∀ j, (data821.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp30_valid
theorem data821_upper_valid : ∀ j, (data821.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data821_center_valid : ∀ j, (data821.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp34_valid
theorem margin821 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data821 25 := by decide +kernel
theorem positive821 {q : EdgeTriple} (hq : q ∈ box821.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data821 25
    data821_lower_valid data821_upper_valid data821_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin821 hq

def box822 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(4821/2048 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)]⟩
def data822 : S1TaylorBoxData := ⟨box822,![exp66,exp46,exp30],![exp70,exp54,exp38],![exp68,exp50,exp34]⟩
theorem data822_lower_valid : ∀ j, (data822.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp30_valid
theorem data822_upper_valid : ∀ j, (data822.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data822_center_valid : ∀ j, (data822.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp50_valid
  · exact exp34_valid
theorem margin822 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data822 25 := by decide +kernel
theorem positive822 {q : EdgeTriple} (hq : q ∈ box822.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data822 25
    data822_lower_valid data822_upper_valid data822_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin822 hq

def box823 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data823 : S1TaylorBoxData := ⟨box823,![exp54,exp54,exp0],![exp58,exp58,exp4],![exp56,exp56,exp2]⟩
theorem data823_lower_valid : ∀ j, (data823.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp0_valid
theorem data823_upper_valid : ∀ j, (data823.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp4_valid
theorem data823_center_valid : ∀ j, (data823.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp2_valid
theorem margin823 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data823) 25)).lower := by
  decide +kernel
theorem positive823 {q : EdgeTriple} (hq : q ∈ box823.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data823)
    ⟨data823_lower_valid,data823_upper_valid⟩ 25 margin823 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box824 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data824 : S1TaylorBoxData := ⟨box824,![exp54,exp54,exp4],![exp58,exp58,exp10],![exp56,exp56,exp6]⟩
theorem data824_lower_valid : ∀ j, (data824.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data824_upper_valid : ∀ j, (data824.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp10_valid
theorem data824_center_valid : ∀ j, (data824.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp6_valid
theorem margin824 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data824 25 := by decide +kernel
theorem positive824 {q : EdgeTriple} (hq : q ∈ box824.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data824 25
    data824_lower_valid data824_upper_valid data824_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin824 hq

def box825 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data825 : S1TaylorBoxData := ⟨box825,![exp58,exp54,exp0],![exp62,exp58,exp4],![exp60,exp56,exp2]⟩
theorem data825_lower_valid : ∀ j, (data825.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp0_valid
theorem data825_upper_valid : ∀ j, (data825.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp4_valid
theorem data825_center_valid : ∀ j, (data825.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp2_valid
theorem margin825 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data825) 25)).lower := by
  decide +kernel
theorem positive825 {q : EdgeTriple} (hq : q ∈ box825.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data825)
    ⟨data825_lower_valid,data825_upper_valid⟩ 25 margin825 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box826 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data826 : S1TaylorBoxData := ⟨box826,![exp58,exp54,exp4],![exp62,exp58,exp10],![exp60,exp56,exp6]⟩
theorem data826_lower_valid : ∀ j, (data826.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp4_valid
theorem data826_upper_valid : ∀ j, (data826.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp10_valid
theorem data826_center_valid : ∀ j, (data826.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp6_valid
theorem margin826 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data826 25 := by decide +kernel
theorem positive826 {q : EdgeTriple} (hq : q ∈ box826.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data826 25
    data826_lower_valid data826_upper_valid data826_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin826 hq

def box827 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data827 : S1TaylorBoxData := ⟨box827,![exp58,exp58,exp0],![exp62,exp62,exp4],![exp60,exp60,exp2]⟩
theorem data827_lower_valid : ∀ j, (data827.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp0_valid
theorem data827_upper_valid : ∀ j, (data827.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp4_valid
theorem data827_center_valid : ∀ j, (data827.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp2_valid
theorem margin827 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data827) 25)).lower := by
  decide +kernel
theorem positive827 {q : EdgeTriple} (hq : q ∈ box827.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data827)
    ⟨data827_lower_valid,data827_upper_valid⟩ 25 margin827 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box828 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data828 : S1TaylorBoxData := ⟨box828,![exp58,exp58,exp4],![exp62,exp62,exp10],![exp60,exp60,exp6]⟩
theorem data828_lower_valid : ∀ j, (data828.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp4_valid
theorem data828_upper_valid : ∀ j, (data828.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp10_valid
theorem data828_center_valid : ∀ j, (data828.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp6_valid
theorem margin828 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data828 25 := by decide +kernel
theorem positive828 {q : EdgeTriple} (hq : q ∈ box828.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data828 25
    data828_lower_valid data828_upper_valid data828_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin828 hq

def box829 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data829 : S1TaylorBoxData := ⟨box829,![exp54,exp54,exp10],![exp58,exp58,exp18],![exp56,exp56,exp14]⟩
theorem data829_lower_valid : ∀ j, (data829.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data829_upper_valid : ∀ j, (data829.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp18_valid
theorem data829_center_valid : ∀ j, (data829.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp14_valid
theorem margin829 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data829 25 := by decide +kernel
theorem positive829 {q : EdgeTriple} (hq : q ∈ box829.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data829 25
    data829_lower_valid data829_upper_valid data829_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin829 hq

def box830 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data830 : S1TaylorBoxData := ⟨box830,![exp54,exp54,exp18],![exp58,exp58,exp22],![exp56,exp56,exp20]⟩
theorem data830_lower_valid : ∀ j, (data830.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data830_upper_valid : ∀ j, (data830.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp22_valid
theorem data830_center_valid : ∀ j, (data830.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp20_valid
theorem margin830 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data830 25 := by decide +kernel
theorem positive830 {q : EdgeTriple} (hq : q ∈ box830.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data830 25
    data830_lower_valid data830_upper_valid data830_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin830 hq

def box831 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data831 : S1TaylorBoxData := ⟨box831,![exp58,exp54,exp10],![exp62,exp58,exp18],![exp60,exp56,exp14]⟩
theorem data831_lower_valid : ∀ j, (data831.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp10_valid
theorem data831_upper_valid : ∀ j, (data831.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp18_valid
theorem data831_center_valid : ∀ j, (data831.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp14_valid
theorem margin831 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data831 25 := by decide +kernel
theorem positive831 {q : EdgeTriple} (hq : q ∈ box831.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data831 25
    data831_lower_valid data831_upper_valid data831_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin831 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

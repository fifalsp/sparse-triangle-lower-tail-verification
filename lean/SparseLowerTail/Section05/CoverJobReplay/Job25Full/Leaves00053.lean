import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box848 : LogBox := ⟨![(24105/4096 : ℚ),(4821/1024 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(20891/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data848 : S1TaylorBoxData := ⟨box848,![exp66,exp54,exp18],![exp70,exp58,exp22],![exp68,exp56,exp20]⟩
theorem data848_lower_valid : ∀ j, (data848.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp18_valid
theorem data848_upper_valid : ∀ j, (data848.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp58_valid
  · exact exp22_valid
theorem data848_center_valid : ∀ j, (data848.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp56_valid
  · exact exp20_valid
theorem margin848 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data848 25 := by decide +kernel
theorem positive848 {q : EdgeTriple} (hq : q ∈ box848.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data848 25
    data848_lower_valid data848_upper_valid data848_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin848 hq

def box849 : LogBox := ⟨![(24105/4096 : ℚ),(20891/4096 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data849 : S1TaylorBoxData := ⟨box849,![exp66,exp58,exp10],![exp70,exp62,exp18],![exp68,exp60,exp14]⟩
theorem data849_lower_valid : ∀ j, (data849.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp10_valid
theorem data849_upper_valid : ∀ j, (data849.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp18_valid
theorem data849_center_valid : ∀ j, (data849.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp60_valid
  · exact exp14_valid
theorem margin849 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data849 25 := by decide +kernel
theorem positive849 {q : EdgeTriple} (hq : q ∈ box849.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data849 25
    data849_lower_valid data849_upper_valid data849_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin849 hq

def box850 : LogBox := ⟨![(24105/4096 : ℚ),(20891/4096 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data850 : S1TaylorBoxData := ⟨box850,![exp66,exp58,exp18],![exp70,exp62,exp22],![exp68,exp60,exp20]⟩
theorem data850_lower_valid : ∀ j, (data850.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp18_valid
theorem data850_upper_valid : ∀ j, (data850.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp22_valid
theorem data850_center_valid : ∀ j, (data850.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp60_valid
  · exact exp20_valid
theorem margin850 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data850 25 := by decide +kernel
theorem positive850 {q : EdgeTriple} (hq : q ∈ box850.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data850 25
    data850_lower_valid data850_upper_valid data850_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin850 hq

def box851 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(24105/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data851 : S1TaylorBoxData := ⟨box851,![exp62,exp62,exp0],![exp66,exp66,exp4],![exp64,exp64,exp2]⟩
theorem data851_lower_valid : ∀ j, (data851.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp0_valid
theorem data851_upper_valid : ∀ j, (data851.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp4_valid
theorem data851_center_valid : ∀ j, (data851.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp64_valid
  · exact exp2_valid
theorem margin851 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data851) 25)).lower := by
  decide +kernel
theorem positive851 {q : EdgeTriple} (hq : q ∈ box851.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data851)
    ⟨data851_lower_valid,data851_upper_valid⟩ 25 margin851 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box852 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(24105/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data852 : S1TaylorBoxData := ⟨box852,![exp62,exp62,exp4],![exp66,exp66,exp10],![exp64,exp64,exp6]⟩
theorem data852_lower_valid : ∀ j, (data852.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp4_valid
theorem data852_upper_valid : ∀ j, (data852.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp10_valid
theorem data852_center_valid : ∀ j, (data852.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp64_valid
  · exact exp6_valid
theorem margin852 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data852 25 := by decide +kernel
theorem positive852 {q : EdgeTriple} (hq : q ∈ box852.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data852 25
    data852_lower_valid data852_upper_valid data852_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin852 hq

def box853 : LogBox := ⟨![(24105/4096 : ℚ),(11249/2048 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(24105/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data853 : S1TaylorBoxData := ⟨box853,![exp66,exp62,exp0],![exp70,exp66,exp4],![exp68,exp64,exp2]⟩
theorem data853_lower_valid : ∀ j, (data853.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp0_valid
theorem data853_upper_valid : ∀ j, (data853.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp66_valid
  · exact exp4_valid
theorem data853_center_valid : ∀ j, (data853.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp64_valid
  · exact exp2_valid
theorem margin853 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data853) 25)).lower := by
  decide +kernel
theorem positive853 {q : EdgeTriple} (hq : q ∈ box853.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data853)
    ⟨data853_lower_valid,data853_upper_valid⟩ 25 margin853 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box854 : LogBox := ⟨![(24105/4096 : ℚ),(11249/2048 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(24105/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data854 : S1TaylorBoxData := ⟨box854,![exp66,exp62,exp4],![exp70,exp66,exp10],![exp68,exp64,exp6]⟩
theorem data854_lower_valid : ∀ j, (data854.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp4_valid
theorem data854_upper_valid : ∀ j, (data854.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp66_valid
  · exact exp10_valid
theorem data854_center_valid : ∀ j, (data854.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp64_valid
  · exact exp6_valid
theorem margin854 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data854 25 := by decide +kernel
theorem positive854 {q : EdgeTriple} (hq : q ∈ box854.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data854 25
    data854_lower_valid data854_upper_valid data854_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin854 hq

def box855 : LogBox := ⟨![(24105/4096 : ℚ),(24105/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/4096 : ℚ)]⟩
def data855 : S1TaylorBoxData := ⟨box855,![exp66,exp66,exp0],![exp70,exp70,exp4],![exp68,exp68,exp2]⟩
theorem data855_lower_valid : ∀ j, (data855.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp0_valid
theorem data855_upper_valid : ∀ j, (data855.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp4_valid
theorem data855_center_valid : ∀ j, (data855.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp68_valid
  · exact exp2_valid
theorem margin855 : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data855) 25)).lower := by
  decide +kernel
theorem positive855 {q : EdgeTriple} (hq : q ∈ box855.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data855)
    ⟨data855_lower_valid,data855_upper_valid⟩ 25 margin855 (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)

def box856 : LogBox := ⟨![(24105/4096 : ℚ),(24105/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/2048 : ℚ)]⟩
def data856 : S1TaylorBoxData := ⟨box856,![exp66,exp66,exp4],![exp70,exp70,exp10],![exp68,exp68,exp6]⟩
theorem data856_lower_valid : ∀ j, (data856.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp4_valid
theorem data856_upper_valid : ∀ j, (data856.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp10_valid
theorem data856_center_valid : ∀ j, (data856.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp68_valid
  · exact exp6_valid
theorem margin856 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data856 25 := by decide +kernel
theorem positive856 {q : EdgeTriple} (hq : q ∈ box856.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data856 25
    data856_lower_valid data856_upper_valid data856_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin856 hq

def box857 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(24105/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data857 : S1TaylorBoxData := ⟨box857,![exp62,exp62,exp10],![exp66,exp66,exp18],![exp64,exp64,exp14]⟩
theorem data857_lower_valid : ∀ j, (data857.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp10_valid
theorem data857_upper_valid : ∀ j, (data857.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp18_valid
theorem data857_center_valid : ∀ j, (data857.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp64_valid
  · exact exp14_valid
theorem margin857 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data857 25 := by decide +kernel
theorem positive857 {q : EdgeTriple} (hq : q ∈ box857.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data857 25
    data857_lower_valid data857_upper_valid data857_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin857 hq

def box858 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(24105/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data858 : S1TaylorBoxData := ⟨box858,![exp62,exp62,exp18],![exp66,exp66,exp22],![exp64,exp64,exp20]⟩
theorem data858_lower_valid : ∀ j, (data858.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp18_valid
theorem data858_upper_valid : ∀ j, (data858.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp22_valid
theorem data858_center_valid : ∀ j, (data858.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp64_valid
  · exact exp20_valid
theorem margin858 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data858 25 := by decide +kernel
theorem positive858 {q : EdgeTriple} (hq : q ∈ box858.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data858 25
    data858_lower_valid data858_upper_valid data858_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin858 hq

def box859 : LogBox := ⟨![(24105/4096 : ℚ),(11249/2048 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(24105/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data859 : S1TaylorBoxData := ⟨box859,![exp66,exp62,exp10],![exp70,exp66,exp18],![exp68,exp64,exp14]⟩
theorem data859_lower_valid : ∀ j, (data859.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp10_valid
theorem data859_upper_valid : ∀ j, (data859.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp66_valid
  · exact exp18_valid
theorem data859_center_valid : ∀ j, (data859.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp64_valid
  · exact exp14_valid
theorem margin859 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data859 25 := by decide +kernel
theorem positive859 {q : EdgeTriple} (hq : q ∈ box859.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data859 25
    data859_lower_valid data859_upper_valid data859_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin859 hq

def box860 : LogBox := ⟨![(24105/4096 : ℚ),(11249/2048 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(24105/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data860 : S1TaylorBoxData := ⟨box860,![exp66,exp62,exp18],![exp70,exp66,exp22],![exp68,exp64,exp20]⟩
theorem data860_lower_valid : ∀ j, (data860.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp18_valid
theorem data860_upper_valid : ∀ j, (data860.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp66_valid
  · exact exp22_valid
theorem data860_center_valid : ∀ j, (data860.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp64_valid
  · exact exp20_valid
theorem margin860 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data860 25 := by decide +kernel
theorem positive860 {q : EdgeTriple} (hq : q ∈ box860.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data860 25
    data860_lower_valid data860_upper_valid data860_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin860 hq

def box861 : LogBox := ⟨![(24105/4096 : ℚ),(24105/4096 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(4821/4096 : ℚ)]⟩
def data861 : S1TaylorBoxData := ⟨box861,![exp66,exp66,exp10],![exp70,exp70,exp18],![exp68,exp68,exp14]⟩
theorem data861_lower_valid : ∀ j, (data861.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp10_valid
theorem data861_upper_valid : ∀ j, (data861.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp18_valid
theorem data861_center_valid : ∀ j, (data861.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp68_valid
  · exact exp14_valid
theorem margin861 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data861 25 := by decide +kernel
theorem positive861 {q : EdgeTriple} (hq : q ∈ box861.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data861 25
    data861_lower_valid data861_upper_valid data861_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin861 hq

def box862 : LogBox := ⟨![(24105/4096 : ℚ),(24105/4096 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/1024 : ℚ)]⟩
def data862 : S1TaylorBoxData := ⟨box862,![exp66,exp66,exp18],![exp70,exp70,exp22],![exp68,exp68,exp20]⟩
theorem data862_lower_valid : ∀ j, (data862.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp18_valid
theorem data862_upper_valid : ∀ j, (data862.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp22_valid
theorem data862_center_valid : ∀ j, (data862.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp68_valid
  · exact exp20_valid
theorem margin862 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data862 25 := by decide +kernel
theorem positive862 {q : EdgeTriple} (hq : q ∈ box862.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data862 25
    data862_lower_valid data862_upper_valid data862_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin862 hq

def box863 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/1024 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data863 : S1TaylorBoxData := ⟨box863,![exp54,exp54,exp22],![exp58,exp58,exp26],![exp56,exp56,exp24]⟩
theorem data863_lower_valid : ∀ j, (data863.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp22_valid
theorem data863_upper_valid : ∀ j, (data863.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp26_valid
theorem data863_center_valid : ∀ j, (data863.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp24_valid
theorem margin863 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data863 25 := by decide +kernel
theorem positive863 {q : EdgeTriple} (hq : q ∈ box863.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data863 25
    data863_lower_valid data863_upper_valid data863_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin863 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box112 : LogBox := ⟨![(11249/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(1607/1024 : ℚ),(11249/8192 : ℚ),(4821/4096 : ℚ)]⟩
def data112 : S1TaylorBoxData := ⟨box112,![exp20,exp18,exp10],![exp22,exp20,exp18],![exp21,exp19,exp14]⟩
theorem data112_lower_valid : ∀ j, (data112.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data112_upper_valid : ∀ j, (data112.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp20_valid
  · exact exp18_valid
theorem data112_center_valid : ∀ j, (data112.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp19_valid
  · exact exp14_valid
theorem margin112 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data112 25 := by decide +kernel
theorem positive112 {q : EdgeTriple} (hq : q ∈ box112.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data112 25
    data112_lower_valid data112_upper_valid data112_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin112 hq

def box113 : LogBox := ⟨![(11249/8192 : ℚ),(11249/8192 : ℚ),(1607/2048 : ℚ)],![(1607/1024 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data113 : S1TaylorBoxData := ⟨box113,![exp20,exp20,exp10],![exp22,exp22,exp18],![exp21,exp21,exp14]⟩
theorem data113_lower_valid : ∀ j, (data113.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp10_valid
theorem data113_upper_valid : ∀ j, (data113.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data113_center_valid : ∀ j, (data113.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp21_valid
  · exact exp14_valid
theorem margin113 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data113 25 := by decide +kernel
theorem positive113 {q : EdgeTriple} (hq : q ∈ box113.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data113 25
    data113_lower_valid data113_upper_valid data113_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin113 hq

def box114 : LogBox := ⟨![(4821/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(11249/8192 : ℚ),(11249/8192 : ℚ),(11249/8192 : ℚ)]⟩
def data114 : S1TaylorBoxData := ⟨box114,![exp18,exp18,exp18],![exp20,exp20,exp20],![exp19,exp19,exp19]⟩
theorem data114_lower_valid : ∀ j, (data114.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data114_upper_valid : ∀ j, (data114.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp20_valid
theorem data114_center_valid : ∀ j, (data114.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp19_valid
  · exact exp19_valid
theorem margin114 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data114 25 := by decide +kernel
theorem positive114 {q : EdgeTriple} (hq : q ∈ box114.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data114 25
    data114_lower_valid data114_upper_valid data114_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin114 hq

def box115 : LogBox := ⟨![(11249/8192 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data115 : S1TaylorBoxData := ⟨box115,![exp20,exp18,exp18],![exp22,exp22,exp22],![exp21,exp20,exp20]⟩
theorem data115_lower_valid : ∀ j, (data115.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data115_upper_valid : ∀ j, (data115.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data115_center_valid : ∀ j, (data115.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin115 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data115 25 := by decide +kernel
theorem positive115 {q : EdgeTriple} (hq : q ∈ box115.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data115 25
    data115_lower_valid data115_upper_valid data115_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin115 hq

def box116 : LogBox := ⟨![(1607/1024 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data116 : S1TaylorBoxData := ⟨box116,![exp22,exp0,exp0],![exp24,exp2,exp2],![exp23,exp1,exp1]⟩
theorem data116_lower_valid : ∀ j, (data116.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data116_upper_valid : ∀ j, (data116.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data116_center_valid : ∀ j, (data116.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin116 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data116 25 := by decide +kernel
theorem positive116 {q : EdgeTriple} (hq : q ∈ box116.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data116 25
    data116_lower_valid data116_upper_valid data116_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin116 hq

def box117 : LogBox := ⟨![(1607/1024 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data117 : S1TaylorBoxData := ⟨box117,![exp22,exp2,exp0],![exp24,exp4,exp2],![exp23,exp3,exp1]⟩
theorem data117_lower_valid : ∀ j, (data117.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data117_upper_valid : ∀ j, (data117.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data117_center_valid : ∀ j, (data117.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin117 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data117 25 := by decide +kernel
theorem positive117 {q : EdgeTriple} (hq : q ∈ box117.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data117 25
    data117_lower_valid data117_upper_valid data117_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin117 hq

def box118 : LogBox := ⟨![(1607/1024 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(14463/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data118 : S1TaylorBoxData := ⟨box118,![exp22,exp2,exp2],![exp24,exp4,exp4],![exp23,exp3,exp3]⟩
theorem data118_lower_valid : ∀ j, (data118.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data118_upper_valid : ∀ j, (data118.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data118_center_valid : ∀ j, (data118.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin118 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data118 25 := by decide +kernel
theorem positive118 {q : EdgeTriple} (hq : q ∈ box118.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data118 25
    data118_lower_valid data118_upper_valid data118_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin118 hq

def box119 : LogBox := ⟨![(14463/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data119 : S1TaylorBoxData := ⟨box119,![exp24,exp0,exp0],![exp26,exp2,exp2],![exp25,exp1,exp1]⟩
theorem data119_lower_valid : ∀ j, (data119.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data119_upper_valid : ∀ j, (data119.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data119_center_valid : ∀ j, (data119.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin119 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data119 25 := by decide +kernel
theorem positive119 {q : EdgeTriple} (hq : q ∈ box119.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data119 25
    data119_lower_valid data119_upper_valid data119_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin119 hq

def box120 : LogBox := ⟨![(14463/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data120 : S1TaylorBoxData := ⟨box120,![exp24,exp2,exp0],![exp26,exp4,exp2],![exp25,exp3,exp1]⟩
theorem data120_lower_valid : ∀ j, (data120.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data120_upper_valid : ∀ j, (data120.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data120_center_valid : ∀ j, (data120.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp3_valid
  · exact exp1_valid
theorem margin120 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data120 25 := by decide +kernel
theorem positive120 {q : EdgeTriple} (hq : q ∈ box120.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data120 25
    data120_lower_valid data120_upper_valid data120_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin120 hq

def box121 : LogBox := ⟨![(14463/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)],![(8035/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data121 : S1TaylorBoxData := ⟨box121,![exp24,exp2,exp2],![exp26,exp4,exp4],![exp25,exp3,exp3]⟩
theorem data121_lower_valid : ∀ j, (data121.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data121_upper_valid : ∀ j, (data121.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data121_center_valid : ∀ j, (data121.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp3_valid
  · exact exp3_valid
theorem margin121 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data121 25 := by decide +kernel
theorem positive121 {q : EdgeTriple} (hq : q ∈ box121.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data121 25
    data121_lower_valid data121_upper_valid data121_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin121 hq

def box122 : LogBox := ⟨![(1607/1024 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data122 : S1TaylorBoxData := ⟨box122,![exp22,exp4,exp0],![exp24,exp6,exp2],![exp23,exp5,exp1]⟩
theorem data122_lower_valid : ∀ j, (data122.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data122_upper_valid : ∀ j, (data122.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data122_center_valid : ∀ j, (data122.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin122 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data122 25 := by decide +kernel
theorem positive122 {q : EdgeTriple} (hq : q ∈ box122.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data122 25
    data122_lower_valid data122_upper_valid data122_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin122 hq

def box123 : LogBox := ⟨![(1607/1024 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(14463/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data123 : S1TaylorBoxData := ⟨box123,![exp22,exp4,exp2],![exp24,exp6,exp4],![exp23,exp5,exp3]⟩
theorem data123_lower_valid : ∀ j, (data123.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data123_upper_valid : ∀ j, (data123.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data123_center_valid : ∀ j, (data123.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin123 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data123 25 := by decide +kernel
theorem positive123 {q : EdgeTriple} (hq : q ∈ box123.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data123 25
    data123_lower_valid data123_upper_valid data123_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin123 hq

def box124 : LogBox := ⟨![(1607/1024 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data124 : S1TaylorBoxData := ⟨box124,![exp22,exp6,exp0],![exp24,exp10,exp2],![exp23,exp8,exp1]⟩
theorem data124_lower_valid : ∀ j, (data124.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data124_upper_valid : ∀ j, (data124.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data124_center_valid : ∀ j, (data124.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin124 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data124 25 := by decide +kernel
theorem positive124 {q : EdgeTriple} (hq : q ∈ box124.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data124 25
    data124_lower_valid data124_upper_valid data124_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin124 hq

def box125 : LogBox := ⟨![(1607/1024 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(14463/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data125 : S1TaylorBoxData := ⟨box125,![exp22,exp6,exp2],![exp24,exp10,exp4],![exp23,exp8,exp3]⟩
theorem data125_lower_valid : ∀ j, (data125.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data125_upper_valid : ∀ j, (data125.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data125_center_valid : ∀ j, (data125.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin125 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data125 25 := by decide +kernel
theorem positive125 {q : EdgeTriple} (hq : q ∈ box125.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data125 25
    data125_lower_valid data125_upper_valid data125_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin125 hq

def box126 : LogBox := ⟨![(14463/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data126 : S1TaylorBoxData := ⟨box126,![exp24,exp4,exp0],![exp26,exp6,exp2],![exp25,exp5,exp1]⟩
theorem data126_lower_valid : ∀ j, (data126.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data126_upper_valid : ∀ j, (data126.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data126_center_valid : ∀ j, (data126.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin126 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data126 25 := by decide +kernel
theorem positive126 {q : EdgeTriple} (hq : q ∈ box126.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data126 25
    data126_lower_valid data126_upper_valid data126_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin126 hq

def box127 : LogBox := ⟨![(14463/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(8035/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data127 : S1TaylorBoxData := ⟨box127,![exp24,exp4,exp2],![exp26,exp6,exp4],![exp25,exp5,exp3]⟩
theorem data127_lower_valid : ∀ j, (data127.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data127_upper_valid : ∀ j, (data127.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data127_center_valid : ∀ j, (data127.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin127 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data127 25 := by decide +kernel
theorem positive127 {q : EdgeTriple} (hq : q ∈ box127.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data127 25
    data127_lower_valid data127_upper_valid data127_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin127 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

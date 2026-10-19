import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box96 : LogBox := ⟨![(4821/4096 : ℚ),(4821/4096 : ℚ),(4821/8192 : ℚ)],![(11249/8192 : ℚ),(11249/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data96 : S1TaylorBoxData := ⟨box96,![exp18,exp18,exp6],![exp20,exp20,exp10],![exp19,exp19,exp8]⟩
theorem data96_lower_valid : ∀ j, (data96.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp6_valid
theorem data96_upper_valid : ∀ j, (data96.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp10_valid
theorem data96_center_valid : ∀ j, (data96.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp19_valid
  · exact exp8_valid
theorem margin96 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data96 25 := by decide +kernel
theorem positive96 {q : EdgeTriple} (hq : q ∈ box96.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data96 25
    data96_lower_valid data96_upper_valid data96_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin96 hq

def box97 : LogBox := ⟨![(11249/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(1607/1024 : ℚ),(11249/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data97 : S1TaylorBoxData := ⟨box97,![exp20,exp18,exp4],![exp22,exp20,exp6],![exp21,exp19,exp5]⟩
theorem data97_lower_valid : ∀ j, (data97.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data97_upper_valid : ∀ j, (data97.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp20_valid
  · exact exp6_valid
theorem data97_center_valid : ∀ j, (data97.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp19_valid
  · exact exp5_valid
theorem margin97 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data97 25 := by decide +kernel
theorem positive97 {q : EdgeTriple} (hq : q ∈ box97.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data97 25
    data97_lower_valid data97_upper_valid data97_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin97 hq

def box98 : LogBox := ⟨![(11249/8192 : ℚ),(4821/4096 : ℚ),(4821/8192 : ℚ)],![(1607/1024 : ℚ),(11249/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data98 : S1TaylorBoxData := ⟨box98,![exp20,exp18,exp6],![exp22,exp20,exp10],![exp21,exp19,exp8]⟩
theorem data98_lower_valid : ∀ j, (data98.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp6_valid
theorem data98_upper_valid : ∀ j, (data98.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp20_valid
  · exact exp10_valid
theorem data98_center_valid : ∀ j, (data98.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp19_valid
  · exact exp8_valid
theorem margin98 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data98 25 := by decide +kernel
theorem positive98 {q : EdgeTriple} (hq : q ∈ box98.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data98 25
    data98_lower_valid data98_upper_valid data98_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin98 hq

def box99 : LogBox := ⟨![(11249/8192 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)],![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data99 : S1TaylorBoxData := ⟨box99,![exp20,exp20,exp4],![exp22,exp22,exp10],![exp21,exp21,exp6]⟩
theorem data99_lower_valid : ∀ j, (data99.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data99_upper_valid : ∀ j, (data99.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data99_center_valid : ∀ j, (data99.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp21_valid
  · exact exp6_valid
theorem margin99 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data99 25 := by decide +kernel
theorem positive99 {q : EdgeTriple} (hq : q ∈ box99.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data99 25
    data99_lower_valid data99_upper_valid data99_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin99 hq

def box100 : LogBox := ⟨![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(14463/16384 : ℚ),(14463/16384 : ℚ),(14463/16384 : ℚ)]⟩
def data100 : S1TaylorBoxData := ⟨box100,![exp10,exp10,exp10],![exp12,exp12,exp12],![exp11,exp11,exp11]⟩
theorem data100_lower_valid : ∀ j, (data100.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data100_upper_valid : ∀ j, (data100.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp12_valid
  · exact exp12_valid
theorem data100_center_valid : ∀ j, (data100.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp11_valid
  · exact exp11_valid
  · exact exp11_valid
theorem margin100 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data100 25 := by decide +kernel
theorem positive100 {q : EdgeTriple} (hq : q ∈ box100.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data100 25
    data100_lower_valid data100_upper_valid data100_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin100 hq

def box101 : LogBox := ⟨![(14463/16384 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(8035/8192 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data101 : S1TaylorBoxData := ⟨box101,![exp12,exp10,exp10],![exp14,exp14,exp14],![exp13,exp12,exp12]⟩
theorem data101_lower_valid : ∀ j, (data101.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data101_upper_valid : ∀ j, (data101.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data101_center_valid : ∀ j, (data101.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp13_valid
  · exact exp12_valid
  · exact exp12_valid
theorem margin101 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data101 25 := by decide +kernel
theorem positive101 {q : EdgeTriple} (hq : q ∈ box101.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data101 25
    data101_lower_valid data101_upper_valid data101_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin101 hq

def box102 : LogBox := ⟨![(8035/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(4821/4096 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data102 : S1TaylorBoxData := ⟨box102,![exp14,exp10,exp10],![exp18,exp14,exp14],![exp16,exp12,exp12]⟩
theorem data102_lower_valid : ∀ j, (data102.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data102_upper_valid : ∀ j, (data102.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data102_center_valid : ∀ j, (data102.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp12_valid
  · exact exp12_valid
theorem margin102 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data102 25 := by decide +kernel
theorem positive102 {q : EdgeTriple} (hq : q ∈ box102.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data102 25
    data102_lower_valid data102_upper_valid data102_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin102 hq

def box103 : LogBox := ⟨![(8035/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)],![(4821/4096 : ℚ),(4821/4096 : ℚ),(8035/8192 : ℚ)]⟩
def data103 : S1TaylorBoxData := ⟨box103,![exp14,exp14,exp10],![exp18,exp18,exp14],![exp16,exp16,exp12]⟩
theorem data103_lower_valid : ∀ j, (data103.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data103_upper_valid : ∀ j, (data103.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp14_valid
theorem data103_center_valid : ∀ j, (data103.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp16_valid
  · exact exp12_valid
theorem margin103 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data103 25 := by decide +kernel
theorem positive103 {q : EdgeTriple} (hq : q ∈ box103.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data103 25
    data103_lower_valid data103_upper_valid data103_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin103 hq

def box104 : LogBox := ⟨![(8035/8192 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)],![(4821/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data104 : S1TaylorBoxData := ⟨box104,![exp14,exp14,exp14],![exp18,exp18,exp18],![exp16,exp16,exp16]⟩
theorem data104_lower_valid : ∀ j, (data104.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data104_upper_valid : ∀ j, (data104.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data104_center_valid : ∀ j, (data104.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp16_valid
  · exact exp16_valid
theorem margin104 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data104 25 := by decide +kernel
theorem positive104 {q : EdgeTriple} (hq : q ∈ box104.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data104 25
    data104_lower_valid data104_upper_valid data104_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin104 hq

def box105 : LogBox := ⟨![(4821/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(11249/8192 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data105 : S1TaylorBoxData := ⟨box105,![exp18,exp10,exp10],![exp20,exp14,exp14],![exp19,exp12,exp12]⟩
theorem data105_lower_valid : ∀ j, (data105.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data105_upper_valid : ∀ j, (data105.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data105_center_valid : ∀ j, (data105.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp12_valid
  · exact exp12_valid
theorem margin105 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data105 25 := by decide +kernel
theorem positive105 {q : EdgeTriple} (hq : q ∈ box105.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data105 25
    data105_lower_valid data105_upper_valid data105_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin105 hq

def box106 : LogBox := ⟨![(4821/4096 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)],![(11249/8192 : ℚ),(4821/4096 : ℚ),(8035/8192 : ℚ)]⟩
def data106 : S1TaylorBoxData := ⟨box106,![exp18,exp14,exp10],![exp20,exp18,exp14],![exp19,exp16,exp12]⟩
theorem data106_lower_valid : ∀ j, (data106.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data106_upper_valid : ∀ j, (data106.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp14_valid
theorem data106_center_valid : ∀ j, (data106.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp16_valid
  · exact exp12_valid
theorem margin106 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data106 25 := by decide +kernel
theorem positive106 {q : EdgeTriple} (hq : q ∈ box106.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data106 25
    data106_lower_valid data106_upper_valid data106_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin106 hq

def box107 : LogBox := ⟨![(4821/4096 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)],![(11249/8192 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data107 : S1TaylorBoxData := ⟨box107,![exp18,exp14,exp14],![exp20,exp18,exp18],![exp19,exp16,exp16]⟩
theorem data107_lower_valid : ∀ j, (data107.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data107_upper_valid : ∀ j, (data107.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data107_center_valid : ∀ j, (data107.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp16_valid
  · exact exp16_valid
theorem margin107 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data107 25 := by decide +kernel
theorem positive107 {q : EdgeTriple} (hq : q ∈ box107.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data107 25
    data107_lower_valid data107_upper_valid data107_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin107 hq

def box108 : LogBox := ⟨![(11249/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(1607/1024 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data108 : S1TaylorBoxData := ⟨box108,![exp20,exp10,exp10],![exp22,exp14,exp14],![exp21,exp12,exp12]⟩
theorem data108_lower_valid : ∀ j, (data108.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data108_upper_valid : ∀ j, (data108.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data108_center_valid : ∀ j, (data108.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp12_valid
  · exact exp12_valid
theorem margin108 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data108 25 := by decide +kernel
theorem positive108 {q : EdgeTriple} (hq : q ∈ box108.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data108 25
    data108_lower_valid data108_upper_valid data108_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin108 hq

def box109 : LogBox := ⟨![(11249/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)],![(1607/1024 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data109 : S1TaylorBoxData := ⟨box109,![exp20,exp14,exp10],![exp22,exp18,exp18],![exp21,exp16,exp14]⟩
theorem data109_lower_valid : ∀ j, (data109.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data109_upper_valid : ∀ j, (data109.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data109_center_valid : ∀ j, (data109.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp16_valid
  · exact exp14_valid
theorem margin109 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data109 25 := by decide +kernel
theorem positive109 {q : EdgeTriple} (hq : q ∈ box109.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data109 25
    data109_lower_valid data109_upper_valid data109_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin109 hq

def box110 : LogBox := ⟨![(4821/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(11249/8192 : ℚ),(11249/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data110 : S1TaylorBoxData := ⟨box110,![exp18,exp18,exp10],![exp20,exp20,exp14],![exp19,exp19,exp12]⟩
theorem data110_lower_valid : ∀ j, (data110.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data110_upper_valid : ∀ j, (data110.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp14_valid
theorem data110_center_valid : ∀ j, (data110.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp19_valid
  · exact exp12_valid
theorem margin110 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data110 25 := by decide +kernel
theorem positive110 {q : EdgeTriple} (hq : q ∈ box110.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data110 25
    data110_lower_valid data110_upper_valid data110_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin110 hq

def box111 : LogBox := ⟨![(4821/4096 : ℚ),(4821/4096 : ℚ),(8035/8192 : ℚ)],![(11249/8192 : ℚ),(11249/8192 : ℚ),(4821/4096 : ℚ)]⟩
def data111 : S1TaylorBoxData := ⟨box111,![exp18,exp18,exp14],![exp20,exp20,exp18],![exp19,exp19,exp16]⟩
theorem data111_lower_valid : ∀ j, (data111.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp14_valid
theorem data111_upper_valid : ∀ j, (data111.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp18_valid
theorem data111_center_valid : ∀ j, (data111.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp19_valid
  · exact exp16_valid
theorem margin111 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data111 25 := by decide +kernel
theorem positive111 {q : EdgeTriple} (hq : q ∈ box111.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data111 25
    data111_lower_valid data111_upper_valid data111_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin111 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

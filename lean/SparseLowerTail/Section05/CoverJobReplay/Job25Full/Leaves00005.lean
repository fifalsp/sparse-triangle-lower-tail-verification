import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box80 : LogBox := ⟨![(4821/4096 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)],![(11249/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data80 : S1TaylorBoxData := ⟨box80,![exp18,exp14,exp2],![exp20,exp18,exp4],![exp19,exp16,exp3]⟩
theorem data80_lower_valid : ∀ j, (data80.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data80_upper_valid : ∀ j, (data80.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data80_center_valid : ∀ j, (data80.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp16_valid
  · exact exp3_valid
theorem margin80 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data80 25 := by decide +kernel
theorem positive80 {q : EdgeTriple} (hq : q ∈ box80.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data80 25
    data80_lower_valid data80_upper_valid data80_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin80 hq

def box81 : LogBox := ⟨![(11249/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data81 : S1TaylorBoxData := ⟨box81,![exp20,exp10,exp0],![exp22,exp14,exp2],![exp21,exp12,exp1]⟩
theorem data81_lower_valid : ∀ j, (data81.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data81_upper_valid : ∀ j, (data81.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data81_center_valid : ∀ j, (data81.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp12_valid
  · exact exp1_valid
theorem margin81 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data81 25 := by decide +kernel
theorem positive81 {q : EdgeTriple} (hq : q ∈ box81.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data81 25
    data81_lower_valid data81_upper_valid data81_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin81 hq

def box82 : LogBox := ⟨![(11249/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)],![(1607/1024 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data82 : S1TaylorBoxData := ⟨box82,![exp20,exp10,exp2],![exp22,exp14,exp4],![exp21,exp12,exp3]⟩
theorem data82_lower_valid : ∀ j, (data82.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data82_upper_valid : ∀ j, (data82.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data82_center_valid : ∀ j, (data82.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp12_valid
  · exact exp3_valid
theorem margin82 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data82 25 := by decide +kernel
theorem positive82 {q : EdgeTriple} (hq : q ∈ box82.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data82 25
    data82_lower_valid data82_upper_valid data82_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin82 hq

def box83 : LogBox := ⟨![(11249/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data83 : S1TaylorBoxData := ⟨box83,![exp20,exp14,exp0],![exp22,exp18,exp4],![exp21,exp16,exp2]⟩
theorem data83_lower_valid : ∀ j, (data83.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data83_upper_valid : ∀ j, (data83.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data83_center_valid : ∀ j, (data83.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin83 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data83 25 := by decide +kernel
theorem positive83 {q : EdgeTriple} (hq : q ∈ box83.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data83 25
    data83_lower_valid data83_upper_valid data83_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin83 hq

def box84 : LogBox := ⟨![(4821/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(11249/8192 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data84 : S1TaylorBoxData := ⟨box84,![exp18,exp10,exp4],![exp20,exp14,exp6],![exp19,exp12,exp5]⟩
theorem data84_lower_valid : ∀ j, (data84.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data84_upper_valid : ∀ j, (data84.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data84_center_valid : ∀ j, (data84.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp12_valid
  · exact exp5_valid
theorem margin84 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data84 25 := by decide +kernel
theorem positive84 {q : EdgeTriple} (hq : q ∈ box84.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data84 25
    data84_lower_valid data84_upper_valid data84_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin84 hq

def box85 : LogBox := ⟨![(4821/4096 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(11249/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data85 : S1TaylorBoxData := ⟨box85,![exp18,exp10,exp6],![exp20,exp14,exp10],![exp19,exp12,exp8]⟩
theorem data85_lower_valid : ∀ j, (data85.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data85_upper_valid : ∀ j, (data85.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data85_center_valid : ∀ j, (data85.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp12_valid
  · exact exp8_valid
theorem margin85 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data85 25 := by decide +kernel
theorem positive85 {q : EdgeTriple} (hq : q ∈ box85.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data85 25
    data85_lower_valid data85_upper_valid data85_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin85 hq

def box86 : LogBox := ⟨![(4821/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(11249/8192 : ℚ),(4821/4096 : ℚ),(4821/8192 : ℚ)]⟩
def data86 : S1TaylorBoxData := ⟨box86,![exp18,exp14,exp4],![exp20,exp18,exp6],![exp19,exp16,exp5]⟩
theorem data86_lower_valid : ∀ j, (data86.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data86_upper_valid : ∀ j, (data86.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp6_valid
theorem data86_center_valid : ∀ j, (data86.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp16_valid
  · exact exp5_valid
theorem margin86 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data86 25 := by decide +kernel
theorem positive86 {q : EdgeTriple} (hq : q ∈ box86.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data86 25
    data86_lower_valid data86_upper_valid data86_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin86 hq

def box87 : LogBox := ⟨![(4821/4096 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)],![(11249/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data87 : S1TaylorBoxData := ⟨box87,![exp18,exp14,exp6],![exp20,exp18,exp10],![exp19,exp16,exp8]⟩
theorem data87_lower_valid : ∀ j, (data87.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data87_upper_valid : ∀ j, (data87.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data87_center_valid : ∀ j, (data87.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp16_valid
  · exact exp8_valid
theorem margin87 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data87 25 := by decide +kernel
theorem positive87 {q : EdgeTriple} (hq : q ∈ box87.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data87 25
    data87_lower_valid data87_upper_valid data87_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin87 hq

def box88 : LogBox := ⟨![(11249/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(1607/1024 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data88 : S1TaylorBoxData := ⟨box88,![exp20,exp10,exp4],![exp22,exp14,exp6],![exp21,exp12,exp5]⟩
theorem data88_lower_valid : ∀ j, (data88.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data88_upper_valid : ∀ j, (data88.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data88_center_valid : ∀ j, (data88.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp12_valid
  · exact exp5_valid
theorem margin88 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data88 25 := by decide +kernel
theorem positive88 {q : EdgeTriple} (hq : q ∈ box88.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data88 25
    data88_lower_valid data88_upper_valid data88_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin88 hq

def box89 : LogBox := ⟨![(11249/8192 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(1607/1024 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data89 : S1TaylorBoxData := ⟨box89,![exp20,exp10,exp6],![exp22,exp14,exp10],![exp21,exp12,exp8]⟩
theorem data89_lower_valid : ∀ j, (data89.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data89_upper_valid : ∀ j, (data89.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data89_center_valid : ∀ j, (data89.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp12_valid
  · exact exp8_valid
theorem margin89 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data89 25 := by decide +kernel
theorem positive89 {q : EdgeTriple} (hq : q ∈ box89.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data89 25
    data89_lower_valid data89_upper_valid data89_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin89 hq

def box90 : LogBox := ⟨![(11249/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(1607/1024 : ℚ),(4821/4096 : ℚ),(4821/8192 : ℚ)]⟩
def data90 : S1TaylorBoxData := ⟨box90,![exp20,exp14,exp4],![exp22,exp18,exp6],![exp21,exp16,exp5]⟩
theorem data90_lower_valid : ∀ j, (data90.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data90_upper_valid : ∀ j, (data90.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp6_valid
theorem data90_center_valid : ∀ j, (data90.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp16_valid
  · exact exp5_valid
theorem margin90 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data90 25 := by decide +kernel
theorem positive90 {q : EdgeTriple} (hq : q ∈ box90.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data90 25
    data90_lower_valid data90_upper_valid data90_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin90 hq

def box91 : LogBox := ⟨![(11249/8192 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)],![(1607/1024 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data91 : S1TaylorBoxData := ⟨box91,![exp20,exp14,exp6],![exp22,exp18,exp10],![exp21,exp16,exp8]⟩
theorem data91_lower_valid : ∀ j, (data91.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data91_upper_valid : ∀ j, (data91.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data91_center_valid : ∀ j, (data91.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp16_valid
  · exact exp8_valid
theorem margin91 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data91 25 := by decide +kernel
theorem positive91 {q : EdgeTriple} (hq : q ∈ box91.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data91 25
    data91_lower_valid data91_upper_valid data91_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin91 hq

def box92 : LogBox := ⟨![(4821/4096 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(11249/8192 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data92 : S1TaylorBoxData := ⟨box92,![exp18,exp18,exp0],![exp20,exp20,exp4],![exp19,exp19,exp2]⟩
theorem data92_lower_valid : ∀ j, (data92.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data92_upper_valid : ∀ j, (data92.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data92_center_valid : ∀ j, (data92.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp19_valid
  · exact exp2_valid
theorem margin92 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data92 25 := by decide +kernel
theorem positive92 {q : EdgeTriple} (hq : q ∈ box92.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data92 25
    data92_lower_valid data92_upper_valid data92_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin92 hq

def box93 : LogBox := ⟨![(11249/8192 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data93 : S1TaylorBoxData := ⟨box93,![exp20,exp18,exp0],![exp22,exp20,exp4],![exp21,exp19,exp2]⟩
theorem data93_lower_valid : ∀ j, (data93.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data93_upper_valid : ∀ j, (data93.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data93_center_valid : ∀ j, (data93.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp19_valid
  · exact exp2_valid
theorem margin93 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data93 25 := by decide +kernel
theorem positive93 {q : EdgeTriple} (hq : q ∈ box93.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data93 25
    data93_lower_valid data93_upper_valid data93_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin93 hq

def box94 : LogBox := ⟨![(11249/8192 : ℚ),(11249/8192 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data94 : S1TaylorBoxData := ⟨box94,![exp20,exp20,exp0],![exp22,exp22,exp4],![exp21,exp21,exp2]⟩
theorem data94_lower_valid : ∀ j, (data94.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp0_valid
theorem data94_upper_valid : ∀ j, (data94.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data94_center_valid : ∀ j, (data94.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp21_valid
  · exact exp2_valid
theorem margin94 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data94 25 := by decide +kernel
theorem positive94 {q : EdgeTriple} (hq : q ∈ box94.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data94 25
    data94_lower_valid data94_upper_valid data94_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin94 hq

def box95 : LogBox := ⟨![(4821/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(11249/8192 : ℚ),(11249/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data95 : S1TaylorBoxData := ⟨box95,![exp18,exp18,exp4],![exp20,exp20,exp6],![exp19,exp19,exp5]⟩
theorem data95_lower_valid : ∀ j, (data95.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data95_upper_valid : ∀ j, (data95.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp20_valid
  · exact exp6_valid
theorem data95_center_valid : ∀ j, (data95.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp19_valid
  · exact exp5_valid
theorem margin95 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data95 25 := by decide +kernel
theorem positive95 {q : EdgeTriple} (hq : q ∈ box95.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data95 25
    data95_lower_valid data95_upper_valid data95_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin95 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

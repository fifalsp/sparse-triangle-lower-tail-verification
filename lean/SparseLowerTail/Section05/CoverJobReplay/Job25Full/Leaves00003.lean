import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box48 : LogBox := ⟨![(4821/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(11249/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data48 : S1TaylorBoxData := ⟨box48,![exp18,exp4,exp0],![exp20,exp6,exp2],![exp19,exp5,exp1]⟩
theorem data48_lower_valid : ∀ j, (data48.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data48_upper_valid : ∀ j, (data48.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data48_center_valid : ∀ j, (data48.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin48 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data48 25 := by decide +kernel
theorem positive48 {q : EdgeTriple} (hq : q ∈ box48.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data48 25
    data48_lower_valid data48_upper_valid data48_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin48 hq

def box49 : LogBox := ⟨![(4821/4096 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(11249/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data49 : S1TaylorBoxData := ⟨box49,![exp18,exp4,exp2],![exp20,exp6,exp4],![exp19,exp5,exp3]⟩
theorem data49_lower_valid : ∀ j, (data49.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data49_upper_valid : ∀ j, (data49.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data49_center_valid : ∀ j, (data49.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin49 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data49 25 := by decide +kernel
theorem positive49 {q : EdgeTriple} (hq : q ∈ box49.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data49 25
    data49_lower_valid data49_upper_valid data49_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin49 hq

def box50 : LogBox := ⟨![(4821/4096 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(11249/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data50 : S1TaylorBoxData := ⟨box50,![exp18,exp6,exp0],![exp20,exp10,exp2],![exp19,exp8,exp1]⟩
theorem data50_lower_valid : ∀ j, (data50.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data50_upper_valid : ∀ j, (data50.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data50_center_valid : ∀ j, (data50.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin50 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data50 25 := by decide +kernel
theorem positive50 {q : EdgeTriple} (hq : q ∈ box50.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data50 25
    data50_lower_valid data50_upper_valid data50_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin50 hq

def box51 : LogBox := ⟨![(4821/4096 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(11249/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data51 : S1TaylorBoxData := ⟨box51,![exp18,exp6,exp2],![exp20,exp10,exp4],![exp19,exp8,exp3]⟩
theorem data51_lower_valid : ∀ j, (data51.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data51_upper_valid : ∀ j, (data51.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data51_center_valid : ∀ j, (data51.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin51 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data51 25 := by decide +kernel
theorem positive51 {q : EdgeTriple} (hq : q ∈ box51.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data51 25
    data51_lower_valid data51_upper_valid data51_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin51 hq

def box52 : LogBox := ⟨![(11249/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data52 : S1TaylorBoxData := ⟨box52,![exp20,exp4,exp0],![exp22,exp6,exp2],![exp21,exp5,exp1]⟩
theorem data52_lower_valid : ∀ j, (data52.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data52_upper_valid : ∀ j, (data52.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data52_center_valid : ∀ j, (data52.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin52 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data52 25 := by decide +kernel
theorem positive52 {q : EdgeTriple} (hq : q ∈ box52.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data52 25
    data52_lower_valid data52_upper_valid data52_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin52 hq

def box53 : LogBox := ⟨![(11249/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(1607/1024 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data53 : S1TaylorBoxData := ⟨box53,![exp20,exp4,exp2],![exp22,exp6,exp4],![exp21,exp5,exp3]⟩
theorem data53_lower_valid : ∀ j, (data53.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data53_upper_valid : ∀ j, (data53.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data53_center_valid : ∀ j, (data53.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin53 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data53 25 := by decide +kernel
theorem positive53 {q : EdgeTriple} (hq : q ∈ box53.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data53 25
    data53_lower_valid data53_upper_valid data53_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin53 hq

def box54 : LogBox := ⟨![(11249/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data54 : S1TaylorBoxData := ⟨box54,![exp20,exp6,exp0],![exp22,exp10,exp2],![exp21,exp8,exp1]⟩
theorem data54_lower_valid : ∀ j, (data54.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data54_upper_valid : ∀ j, (data54.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data54_center_valid : ∀ j, (data54.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin54 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data54 25 := by decide +kernel
theorem positive54 {q : EdgeTriple} (hq : q ∈ box54.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data54 25
    data54_lower_valid data54_upper_valid data54_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin54 hq

def box55 : LogBox := ⟨![(11249/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data55 : S1TaylorBoxData := ⟨box55,![exp20,exp6,exp2],![exp22,exp10,exp4],![exp21,exp8,exp3]⟩
theorem data55_lower_valid : ∀ j, (data55.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data55_upper_valid : ∀ j, (data55.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data55_center_valid : ∀ j, (data55.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin55 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data55 25 := by decide +kernel
theorem positive55 {q : EdgeTriple} (hq : q ∈ box55.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data55 25
    data55_lower_valid data55_upper_valid data55_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin55 hq

def box56 : LogBox := ⟨![(4821/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(11249/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data56 : S1TaylorBoxData := ⟨box56,![exp18,exp4,exp4],![exp20,exp6,exp6],![exp19,exp5,exp5]⟩
theorem data56_lower_valid : ∀ j, (data56.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data56_upper_valid : ∀ j, (data56.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data56_center_valid : ∀ j, (data56.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin56 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data56 25 := by decide +kernel
theorem positive56 {q : EdgeTriple} (hq : q ∈ box56.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data56 25
    data56_lower_valid data56_upper_valid data56_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin56 hq

def box57 : LogBox := ⟨![(4821/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(11249/8192 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)]⟩
def data57 : S1TaylorBoxData := ⟨box57,![exp18,exp6,exp4],![exp20,exp10,exp6],![exp19,exp8,exp5]⟩
theorem data57_lower_valid : ∀ j, (data57.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data57_upper_valid : ∀ j, (data57.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data57_center_valid : ∀ j, (data57.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp8_valid
  · exact exp5_valid
theorem margin57 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data57 25 := by decide +kernel
theorem positive57 {q : EdgeTriple} (hq : q ∈ box57.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data57 25
    data57_lower_valid data57_upper_valid data57_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin57 hq

def box58 : LogBox := ⟨![(4821/4096 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(11249/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data58 : S1TaylorBoxData := ⟨box58,![exp18,exp6,exp6],![exp20,exp10,exp10],![exp19,exp8,exp8]⟩
theorem data58_lower_valid : ∀ j, (data58.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data58_upper_valid : ∀ j, (data58.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data58_center_valid : ∀ j, (data58.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin58 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data58 25 := by decide +kernel
theorem positive58 {q : EdgeTriple} (hq : q ∈ box58.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data58 25
    data58_lower_valid data58_upper_valid data58_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin58 hq

def box59 : LogBox := ⟨![(11249/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(1607/1024 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data59 : S1TaylorBoxData := ⟨box59,![exp20,exp4,exp4],![exp22,exp6,exp6],![exp21,exp5,exp5]⟩
theorem data59_lower_valid : ∀ j, (data59.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data59_upper_valid : ∀ j, (data59.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data59_center_valid : ∀ j, (data59.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin59 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data59 25 := by decide +kernel
theorem positive59 {q : EdgeTriple} (hq : q ∈ box59.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data59 25
    data59_lower_valid data59_upper_valid data59_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin59 hq

def box60 : LogBox := ⟨![(11249/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(1607/1024 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)]⟩
def data60 : S1TaylorBoxData := ⟨box60,![exp20,exp6,exp4],![exp22,exp10,exp6],![exp21,exp8,exp5]⟩
theorem data60_lower_valid : ∀ j, (data60.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data60_upper_valid : ∀ j, (data60.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data60_center_valid : ∀ j, (data60.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp8_valid
  · exact exp5_valid
theorem margin60 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data60 25 := by decide +kernel
theorem positive60 {q : EdgeTriple} (hq : q ∈ box60.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data60 25
    data60_lower_valid data60_upper_valid data60_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin60 hq

def box61 : LogBox := ⟨![(11249/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)],![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data61 : S1TaylorBoxData := ⟨box61,![exp20,exp6,exp6],![exp22,exp10,exp10],![exp21,exp8,exp8]⟩
theorem data61_lower_valid : ∀ j, (data61.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data61_upper_valid : ∀ j, (data61.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data61_center_valid : ∀ j, (data61.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp21_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin61 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data61 25 := by decide +kernel
theorem positive61 {q : EdgeTriple} (hq : q ∈ box61.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data61 25
    data61_lower_valid data61_upper_valid data61_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin61 hq

def box62 : LogBox := ⟨![(1607/2048 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(8035/8192 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data62 : S1TaylorBoxData := ⟨box62,![exp10,exp10,exp0],![exp14,exp14,exp2],![exp12,exp12,exp1]⟩
theorem data62_lower_valid : ∀ j, (data62.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data62_upper_valid : ∀ j, (data62.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data62_center_valid : ∀ j, (data62.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp12_valid
  · exact exp1_valid
theorem margin62 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data62 25 := by decide +kernel
theorem positive62 {q : EdgeTriple} (hq : q ∈ box62.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data62 25
    data62_lower_valid data62_upper_valid data62_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin62 hq

def box63 : LogBox := ⟨![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)],![(8035/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data63 : S1TaylorBoxData := ⟨box63,![exp10,exp10,exp2],![exp14,exp14,exp4],![exp12,exp12,exp3]⟩
theorem data63_lower_valid : ∀ j, (data63.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data63_upper_valid : ∀ j, (data63.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data63_center_valid : ∀ j, (data63.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp12_valid
  · exact exp3_valid
theorem margin63 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data63 25 := by decide +kernel
theorem positive63 {q : EdgeTriple} (hq : q ∈ box63.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data63 25
    data63_lower_valid data63_upper_valid data63_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin63 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

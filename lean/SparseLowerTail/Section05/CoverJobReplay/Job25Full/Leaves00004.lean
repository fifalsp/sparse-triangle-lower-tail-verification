import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box64 : LogBox := ⟨![(8035/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data64 : S1TaylorBoxData := ⟨box64,![exp14,exp10,exp0],![exp18,exp14,exp2],![exp16,exp12,exp1]⟩
theorem data64_lower_valid : ∀ j, (data64.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data64_upper_valid : ∀ j, (data64.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data64_center_valid : ∀ j, (data64.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp12_valid
  · exact exp1_valid
theorem margin64 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data64 25 := by decide +kernel
theorem positive64 {q : EdgeTriple} (hq : q ∈ box64.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data64 25
    data64_lower_valid data64_upper_valid data64_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin64 hq

def box65 : LogBox := ⟨![(8035/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)],![(4821/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data65 : S1TaylorBoxData := ⟨box65,![exp14,exp10,exp2],![exp18,exp14,exp4],![exp16,exp12,exp3]⟩
theorem data65_lower_valid : ∀ j, (data65.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data65_upper_valid : ∀ j, (data65.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data65_center_valid : ∀ j, (data65.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp12_valid
  · exact exp3_valid
theorem margin65 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data65 25 := by decide +kernel
theorem positive65 {q : EdgeTriple} (hq : q ∈ box65.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data65 25
    data65_lower_valid data65_upper_valid data65_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin65 hq

def box66 : LogBox := ⟨![(8035/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(4821/4096 : ℚ),(4821/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data66 : S1TaylorBoxData := ⟨box66,![exp14,exp14,exp0],![exp18,exp18,exp2],![exp16,exp16,exp1]⟩
theorem data66_lower_valid : ∀ j, (data66.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data66_upper_valid : ∀ j, (data66.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp2_valid
theorem data66_center_valid : ∀ j, (data66.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp16_valid
  · exact exp1_valid
theorem margin66 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data66 25 := by decide +kernel
theorem positive66 {q : EdgeTriple} (hq : q ∈ box66.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data66 25
    data66_lower_valid data66_upper_valid data66_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin66 hq

def box67 : LogBox := ⟨![(8035/8192 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)],![(4821/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data67 : S1TaylorBoxData := ⟨box67,![exp14,exp14,exp2],![exp18,exp18,exp4],![exp16,exp16,exp3]⟩
theorem data67_lower_valid : ∀ j, (data67.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data67_upper_valid : ∀ j, (data67.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data67_center_valid : ∀ j, (data67.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp16_valid
  · exact exp3_valid
theorem margin67 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data67 25 := by decide +kernel
theorem positive67 {q : EdgeTriple} (hq : q ∈ box67.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data67 25
    data67_lower_valid data67_upper_valid data67_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin67 hq

def box68 : LogBox := ⟨![(1607/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(14463/16384 : ℚ),(14463/16384 : ℚ),(4821/8192 : ℚ)]⟩
def data68 : S1TaylorBoxData := ⟨box68,![exp10,exp10,exp4],![exp12,exp12,exp6],![exp11,exp11,exp5]⟩
theorem data68_lower_valid : ∀ j, (data68.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data68_upper_valid : ∀ j, (data68.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp12_valid
  · exact exp6_valid
theorem data68_center_valid : ∀ j, (data68.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp11_valid
  · exact exp11_valid
  · exact exp5_valid
theorem margin68 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data68 25 := by decide +kernel
theorem positive68 {q : EdgeTriple} (hq : q ∈ box68.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data68 25
    data68_lower_valid data68_upper_valid data68_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin68 hq

def box69 : LogBox := ⟨![(14463/16384 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(8035/8192 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data69 : S1TaylorBoxData := ⟨box69,![exp12,exp10,exp4],![exp14,exp14,exp6],![exp13,exp12,exp5]⟩
theorem data69_lower_valid : ∀ j, (data69.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data69_upper_valid : ∀ j, (data69.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data69_center_valid : ∀ j, (data69.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp13_valid
  · exact exp12_valid
  · exact exp5_valid
theorem margin69 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data69 25 := by decide +kernel
theorem positive69 {q : EdgeTriple} (hq : q ∈ box69.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data69 25
    data69_lower_valid data69_upper_valid data69_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin69 hq

def box70 : LogBox := ⟨![(1607/2048 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(14463/16384 : ℚ),(14463/16384 : ℚ),(1607/2048 : ℚ)]⟩
def data70 : S1TaylorBoxData := ⟨box70,![exp10,exp10,exp6],![exp12,exp12,exp10],![exp11,exp11,exp8]⟩
theorem data70_lower_valid : ∀ j, (data70.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp10_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data70_upper_valid : ∀ j, (data70.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp12_valid
  · exact exp10_valid
theorem data70_center_valid : ∀ j, (data70.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp11_valid
  · exact exp11_valid
  · exact exp8_valid
theorem margin70 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data70 25 := by decide +kernel
theorem positive70 {q : EdgeTriple} (hq : q ∈ box70.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data70 25
    data70_lower_valid data70_upper_valid data70_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin70 hq

def box71 : LogBox := ⟨![(14463/16384 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(8035/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data71 : S1TaylorBoxData := ⟨box71,![exp12,exp10,exp6],![exp14,exp14,exp10],![exp13,exp12,exp8]⟩
theorem data71_lower_valid : ∀ j, (data71.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp12_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data71_upper_valid : ∀ j, (data71.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data71_center_valid : ∀ j, (data71.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp13_valid
  · exact exp12_valid
  · exact exp8_valid
theorem margin71 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data71 25 := by decide +kernel
theorem positive71 {q : EdgeTriple} (hq : q ∈ box71.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data71 25
    data71_lower_valid data71_upper_valid data71_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin71 hq

def box72 : LogBox := ⟨![(8035/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(4821/4096 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data72 : S1TaylorBoxData := ⟨box72,![exp14,exp10,exp4],![exp18,exp14,exp6],![exp16,exp12,exp5]⟩
theorem data72_lower_valid : ∀ j, (data72.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data72_upper_valid : ∀ j, (data72.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data72_center_valid : ∀ j, (data72.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp12_valid
  · exact exp5_valid
theorem margin72 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data72 25 := by decide +kernel
theorem positive72 {q : EdgeTriple} (hq : q ∈ box72.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data72 25
    data72_lower_valid data72_upper_valid data72_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin72 hq

def box73 : LogBox := ⟨![(8035/8192 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(17677/16384 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data73 : S1TaylorBoxData := ⟨box73,![exp14,exp10,exp6],![exp16,exp14,exp10],![exp15,exp12,exp8]⟩
theorem data73_lower_valid : ∀ j, (data73.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data73_upper_valid : ∀ j, (data73.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data73_center_valid : ∀ j, (data73.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp15_valid
  · exact exp12_valid
  · exact exp8_valid
theorem margin73 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data73 25 := by decide +kernel
theorem positive73 {q : EdgeTriple} (hq : q ∈ box73.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data73 25
    data73_lower_valid data73_upper_valid data73_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin73 hq

def box74 : LogBox := ⟨![(17677/16384 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(4821/4096 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data74 : S1TaylorBoxData := ⟨box74,![exp16,exp10,exp6],![exp18,exp14,exp10],![exp17,exp12,exp8]⟩
theorem data74_lower_valid : ∀ j, (data74.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data74_upper_valid : ∀ j, (data74.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data74_center_valid : ∀ j, (data74.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp17_valid
  · exact exp12_valid
  · exact exp8_valid
theorem margin74 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data74 25 := by decide +kernel
theorem positive74 {q : EdgeTriple} (hq : q ∈ box74.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data74 25
    data74_lower_valid data74_upper_valid data74_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin74 hq

def box75 : LogBox := ⟨![(8035/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(4821/4096 : ℚ),(4821/4096 : ℚ),(4821/8192 : ℚ)]⟩
def data75 : S1TaylorBoxData := ⟨box75,![exp14,exp14,exp4],![exp18,exp18,exp6],![exp16,exp16,exp5]⟩
theorem data75_lower_valid : ∀ j, (data75.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data75_upper_valid : ∀ j, (data75.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp6_valid
theorem data75_center_valid : ∀ j, (data75.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp16_valid
  · exact exp5_valid
theorem margin75 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data75 25 := by decide +kernel
theorem positive75 {q : EdgeTriple} (hq : q ∈ box75.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data75 25
    data75_lower_valid data75_upper_valid data75_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin75 hq

def box76 : LogBox := ⟨![(8035/8192 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)],![(4821/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data76 : S1TaylorBoxData := ⟨box76,![exp14,exp14,exp6],![exp18,exp18,exp10],![exp16,exp16,exp8]⟩
theorem data76_lower_valid : ∀ j, (data76.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp14_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data76_upper_valid : ∀ j, (data76.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data76_center_valid : ∀ j, (data76.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp16_valid
  · exact exp8_valid
theorem margin76 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data76 25 := by decide +kernel
theorem positive76 {q : EdgeTriple} (hq : q ∈ box76.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data76 25
    data76_lower_valid data76_upper_valid data76_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin76 hq

def box77 : LogBox := ⟨![(4821/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(11249/8192 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data77 : S1TaylorBoxData := ⟨box77,![exp18,exp10,exp0],![exp20,exp14,exp2],![exp19,exp12,exp1]⟩
theorem data77_lower_valid : ∀ j, (data77.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data77_upper_valid : ∀ j, (data77.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data77_center_valid : ∀ j, (data77.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp12_valid
  · exact exp1_valid
theorem margin77 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data77 25 := by decide +kernel
theorem positive77 {q : EdgeTriple} (hq : q ∈ box77.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data77 25
    data77_lower_valid data77_upper_valid data77_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin77 hq

def box78 : LogBox := ⟨![(4821/4096 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)],![(11249/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data78 : S1TaylorBoxData := ⟨box78,![exp18,exp10,exp2],![exp20,exp14,exp4],![exp19,exp12,exp3]⟩
theorem data78_lower_valid : ∀ j, (data78.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data78_upper_valid : ∀ j, (data78.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data78_center_valid : ∀ j, (data78.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp12_valid
  · exact exp3_valid
theorem margin78 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data78 25 := by decide +kernel
theorem positive78 {q : EdgeTriple} (hq : q ∈ box78.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data78 25
    data78_lower_valid data78_upper_valid data78_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin78 hq

def box79 : LogBox := ⟨![(4821/4096 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(11249/8192 : ℚ),(4821/4096 : ℚ),(1607/8192 : ℚ)]⟩
def data79 : S1TaylorBoxData := ⟨box79,![exp18,exp14,exp0],![exp20,exp18,exp2],![exp19,exp16,exp1]⟩
theorem data79_lower_valid : ∀ j, (data79.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp18_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data79_upper_valid : ∀ j, (data79.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp20_valid
  · exact exp18_valid
  · exact exp2_valid
theorem data79_center_valid : ∀ j, (data79.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp19_valid
  · exact exp16_valid
  · exact exp1_valid
theorem margin79 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data79 25 := by decide +kernel
theorem positive79 {q : EdgeTriple} (hq : q ∈ box79.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data79 25
    data79_lower_valid data79_upper_valid data79_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin79 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

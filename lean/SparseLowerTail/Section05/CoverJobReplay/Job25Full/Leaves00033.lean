import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box528 : LogBox := ⟨![(49817/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data528 : S1TaylorBoxData := ⟨box528,![exp68,exp2,exp0],![exp70,exp4,exp4],![exp69,exp3,exp2]⟩
theorem data528_lower_valid : ∀ j, (data528.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data528_upper_valid : ∀ j, (data528.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data528_center_valid : ∀ j, (data528.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp69_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin528 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data528 25 := by decide +kernel
theorem positive528 {q : EdgeTriple} (hq : q ∈ box528.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data528 25
    data528_lower_valid data528_upper_valid data528_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin528 hq

def box529 : LogBox := ⟨![(24105/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(49817/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data529 : S1TaylorBoxData := ⟨box529,![exp66,exp4,exp0],![exp68,exp6,exp4],![exp67,exp5,exp2]⟩
theorem data529_lower_valid : ∀ j, (data529.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data529_upper_valid : ∀ j, (data529.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data529_center_valid : ∀ j, (data529.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp67_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin529 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data529 25 := by decide +kernel
theorem positive529 {q : EdgeTriple} (hq : q ∈ box529.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data529 25
    data529_lower_valid data529_upper_valid data529_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin529 hq

def box530 : LogBox := ⟨![(24105/4096 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(49817/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data530 : S1TaylorBoxData := ⟨box530,![exp66,exp6,exp0],![exp68,exp10,exp4],![exp67,exp8,exp2]⟩
theorem data530_lower_valid : ∀ j, (data530.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data530_upper_valid : ∀ j, (data530.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data530_center_valid : ∀ j, (data530.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp67_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin530 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data530 25 := by decide +kernel
theorem positive530 {q : EdgeTriple} (hq : q ∈ box530.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data530 25
    data530_lower_valid data530_upper_valid data530_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin530 hq

def box531 : LogBox := ⟨![(49817/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data531 : S1TaylorBoxData := ⟨box531,![exp68,exp4,exp0],![exp70,exp6,exp4],![exp69,exp5,exp2]⟩
theorem data531_lower_valid : ∀ j, (data531.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data531_upper_valid : ∀ j, (data531.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data531_center_valid : ∀ j, (data531.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp69_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin531 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data531 25 := by decide +kernel
theorem positive531 {q : EdgeTriple} (hq : q ∈ box531.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data531 25
    data531_lower_valid data531_upper_valid data531_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin531 hq

def box532 : LogBox := ⟨![(49817/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data532 : S1TaylorBoxData := ⟨box532,![exp68,exp6,exp0],![exp70,exp10,exp4],![exp69,exp8,exp2]⟩
theorem data532_lower_valid : ∀ j, (data532.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data532_upper_valid : ∀ j, (data532.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data532_center_valid : ∀ j, (data532.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp69_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin532 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data532 25 := by decide +kernel
theorem positive532 {q : EdgeTriple} (hq : q ∈ box532.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data532 25
    data532_lower_valid data532_upper_valid data532_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin532 hq

def box533 : LogBox := ⟨![(24105/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data533 : S1TaylorBoxData := ⟨box533,![exp66,exp4,exp4],![exp70,exp10,exp10],![exp68,exp6,exp6]⟩
theorem data533_lower_valid : ∀ j, (data533.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data533_upper_valid : ∀ j, (data533.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data533_center_valid : ∀ j, (data533.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin533 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data533 25 := by decide +kernel
theorem positive533 {q : EdgeTriple} (hq : q ∈ box533.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data533 25
    data533_lower_valid data533_upper_valid data533_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin533 hq

def box534 : LogBox := ⟨![(11249/2048 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data534 : S1TaylorBoxData := ⟨box534,![exp62,exp10,exp0],![exp66,exp18,exp4],![exp64,exp14,exp2]⟩
theorem data534_lower_valid : ∀ j, (data534.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data534_upper_valid : ∀ j, (data534.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data534_center_valid : ∀ j, (data534.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp14_valid
  · exact exp2_valid
theorem margin534 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data534 25 := by decide +kernel
theorem positive534 {q : EdgeTriple} (hq : q ∈ box534.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data534 25
    data534_lower_valid data534_upper_valid data534_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin534 hq

def box535 : LogBox := ⟨![(11249/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data535 : S1TaylorBoxData := ⟨box535,![exp62,exp10,exp4],![exp66,exp18,exp10],![exp64,exp14,exp6]⟩
theorem data535_lower_valid : ∀ j, (data535.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data535_upper_valid : ∀ j, (data535.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data535_center_valid : ∀ j, (data535.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin535 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data535 25 := by decide +kernel
theorem positive535 {q : EdgeTriple} (hq : q ∈ box535.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data535 25
    data535_lower_valid data535_upper_valid data535_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin535 hq

def box536 : LogBox := ⟨![(11249/2048 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data536 : S1TaylorBoxData := ⟨box536,![exp62,exp18,exp0],![exp66,exp22,exp4],![exp64,exp20,exp2]⟩
theorem data536_lower_valid : ∀ j, (data536.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data536_upper_valid : ∀ j, (data536.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data536_center_valid : ∀ j, (data536.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin536 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data536 25 := by decide +kernel
theorem positive536 {q : EdgeTriple} (hq : q ∈ box536.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data536 25
    data536_lower_valid data536_upper_valid data536_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin536 hq

def box537 : LogBox := ⟨![(11249/2048 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data537 : S1TaylorBoxData := ⟨box537,![exp62,exp18,exp4],![exp66,exp22,exp10],![exp64,exp20,exp6]⟩
theorem data537_lower_valid : ∀ j, (data537.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data537_upper_valid : ∀ j, (data537.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data537_center_valid : ∀ j, (data537.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin537 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data537 25 := by decide +kernel
theorem positive537 {q : EdgeTriple} (hq : q ∈ box537.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data537 25
    data537_lower_valid data537_upper_valid data537_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin537 hq

def box538 : LogBox := ⟨![(24105/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data538 : S1TaylorBoxData := ⟨box538,![exp66,exp10,exp0],![exp70,exp18,exp4],![exp68,exp14,exp2]⟩
theorem data538_lower_valid : ∀ j, (data538.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data538_upper_valid : ∀ j, (data538.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data538_center_valid : ∀ j, (data538.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp14_valid
  · exact exp2_valid
theorem margin538 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data538 25 := by decide +kernel
theorem positive538 {q : EdgeTriple} (hq : q ∈ box538.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data538 25
    data538_lower_valid data538_upper_valid data538_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin538 hq

def box539 : LogBox := ⟨![(24105/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data539 : S1TaylorBoxData := ⟨box539,![exp66,exp10,exp4],![exp70,exp18,exp10],![exp68,exp14,exp6]⟩
theorem data539_lower_valid : ∀ j, (data539.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data539_upper_valid : ∀ j, (data539.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data539_center_valid : ∀ j, (data539.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin539 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data539 25 := by decide +kernel
theorem positive539 {q : EdgeTriple} (hq : q ∈ box539.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data539 25
    data539_lower_valid data539_upper_valid data539_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin539 hq

def box540 : LogBox := ⟨![(24105/4096 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data540 : S1TaylorBoxData := ⟨box540,![exp66,exp18,exp0],![exp70,exp22,exp4],![exp68,exp20,exp2]⟩
theorem data540_lower_valid : ∀ j, (data540.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data540_upper_valid : ∀ j, (data540.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data540_center_valid : ∀ j, (data540.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin540 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data540 25 := by decide +kernel
theorem positive540 {q : EdgeTriple} (hq : q ∈ box540.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data540 25
    data540_lower_valid data540_upper_valid data540_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin540 hq

def box541 : LogBox := ⟨![(24105/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data541 : S1TaylorBoxData := ⟨box541,![exp66,exp18,exp4],![exp70,exp22,exp10],![exp68,exp20,exp6]⟩
theorem data541_lower_valid : ∀ j, (data541.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data541_upper_valid : ∀ j, (data541.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data541_center_valid : ∀ j, (data541.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin541 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data541 25 := by decide +kernel
theorem positive541 {q : EdgeTriple} (hq : q ∈ box541.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data541 25
    data541_lower_valid data541_upper_valid data541_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin541 hq

def box542 : LogBox := ⟨![(11249/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data542 : S1TaylorBoxData := ⟨box542,![exp62,exp10,exp10],![exp66,exp18,exp18],![exp64,exp14,exp14]⟩
theorem data542_lower_valid : ∀ j, (data542.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data542_upper_valid : ∀ j, (data542.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data542_center_valid : ∀ j, (data542.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin542 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data542 25 := by decide +kernel
theorem positive542 {q : EdgeTriple} (hq : q ∈ box542.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data542 25
    data542_lower_valid data542_upper_valid data542_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin542 hq

def box543 : LogBox := ⟨![(11249/2048 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data543 : S1TaylorBoxData := ⟨box543,![exp62,exp18,exp10],![exp66,exp22,exp18],![exp64,exp20,exp14]⟩
theorem data543_lower_valid : ∀ j, (data543.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data543_upper_valid : ∀ j, (data543.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data543_center_valid : ∀ j, (data543.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin543 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data543 25 := by decide +kernel
theorem positive543 {q : EdgeTriple} (hq : q ∈ box543.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data543 25
    data543_lower_valid data543_upper_valid data543_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin543 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

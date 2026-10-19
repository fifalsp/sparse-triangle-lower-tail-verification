import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box592 : LogBox := ⟨![(24105/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data592 : S1TaylorBoxData := ⟨box592,![exp66,exp22,exp10],![exp70,exp26,exp18],![exp68,exp24,exp14]⟩
theorem data592_lower_valid : ∀ j, (data592.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data592_upper_valid : ∀ j, (data592.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data592_center_valid : ∀ j, (data592.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin592 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data592 25 := by decide +kernel
theorem positive592 {q : EdgeTriple} (hq : q ∈ box592.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data592 25
    data592_lower_valid data592_upper_valid data592_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin592 hq

def box593 : LogBox := ⟨![(24105/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data593 : S1TaylorBoxData := ⟨box593,![exp66,exp22,exp18],![exp70,exp26,exp22],![exp68,exp24,exp20]⟩
theorem data593_lower_valid : ∀ j, (data593.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data593_upper_valid : ∀ j, (data593.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data593_center_valid : ∀ j, (data593.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin593 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data593 25 := by decide +kernel
theorem positive593 {q : EdgeTriple} (hq : q ∈ box593.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data593 25
    data593_lower_valid data593_upper_valid data593_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin593 hq

def box594 : LogBox := ⟨![(24105/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data594 : S1TaylorBoxData := ⟨box594,![exp66,exp26,exp10],![exp70,exp30,exp18],![exp68,exp28,exp14]⟩
theorem data594_lower_valid : ∀ j, (data594.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data594_upper_valid : ∀ j, (data594.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data594_center_valid : ∀ j, (data594.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin594 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data594 25 := by decide +kernel
theorem positive594 {q : EdgeTriple} (hq : q ∈ box594.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data594 25
    data594_lower_valid data594_upper_valid data594_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin594 hq

def box595 : LogBox := ⟨![(24105/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data595 : S1TaylorBoxData := ⟨box595,![exp66,exp26,exp18],![exp70,exp30,exp22],![exp68,exp28,exp20]⟩
theorem data595_lower_valid : ∀ j, (data595.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data595_upper_valid : ∀ j, (data595.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data595_center_valid : ∀ j, (data595.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin595 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data595 25 := by decide +kernel
theorem positive595 {q : EdgeTriple} (hq : q ∈ box595.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data595 25
    data595_lower_valid data595_upper_valid data595_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin595 hq

def box596 : LogBox := ⟨![(11249/2048 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data596 : S1TaylorBoxData := ⟨box596,![exp62,exp30,exp0],![exp66,exp34,exp4],![exp64,exp32,exp2]⟩
theorem data596_lower_valid : ∀ j, (data596.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data596_upper_valid : ∀ j, (data596.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data596_center_valid : ∀ j, (data596.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin596 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data596 25 := by decide +kernel
theorem positive596 {q : EdgeTriple} (hq : q ∈ box596.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data596 25
    data596_lower_valid data596_upper_valid data596_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin596 hq

def box597 : LogBox := ⟨![(11249/2048 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data597 : S1TaylorBoxData := ⟨box597,![exp62,exp30,exp4],![exp66,exp34,exp10],![exp64,exp32,exp6]⟩
theorem data597_lower_valid : ∀ j, (data597.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data597_upper_valid : ∀ j, (data597.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data597_center_valid : ∀ j, (data597.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin597 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data597 25 := by decide +kernel
theorem positive597 {q : EdgeTriple} (hq : q ∈ box597.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data597 25
    data597_lower_valid data597_upper_valid data597_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin597 hq

def box598 : LogBox := ⟨![(11249/2048 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data598 : S1TaylorBoxData := ⟨box598,![exp62,exp34,exp0],![exp66,exp38,exp4],![exp64,exp36,exp2]⟩
theorem data598_lower_valid : ∀ j, (data598.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data598_upper_valid : ∀ j, (data598.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data598_center_valid : ∀ j, (data598.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin598 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data598 25 := by decide +kernel
theorem positive598 {q : EdgeTriple} (hq : q ∈ box598.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data598 25
    data598_lower_valid data598_upper_valid data598_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin598 hq

def box599 : LogBox := ⟨![(11249/2048 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data599 : S1TaylorBoxData := ⟨box599,![exp62,exp34,exp4],![exp66,exp38,exp10],![exp64,exp36,exp6]⟩
theorem data599_lower_valid : ∀ j, (data599.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data599_upper_valid : ∀ j, (data599.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data599_center_valid : ∀ j, (data599.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin599 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data599 25 := by decide +kernel
theorem positive599 {q : EdgeTriple} (hq : q ∈ box599.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data599 25
    data599_lower_valid data599_upper_valid data599_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin599 hq

def box600 : LogBox := ⟨![(24105/4096 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data600 : S1TaylorBoxData := ⟨box600,![exp66,exp30,exp0],![exp70,exp34,exp4],![exp68,exp32,exp2]⟩
theorem data600_lower_valid : ∀ j, (data600.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data600_upper_valid : ∀ j, (data600.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data600_center_valid : ∀ j, (data600.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin600 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data600 25 := by decide +kernel
theorem positive600 {q : EdgeTriple} (hq : q ∈ box600.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data600 25
    data600_lower_valid data600_upper_valid data600_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin600 hq

def box601 : LogBox := ⟨![(24105/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data601 : S1TaylorBoxData := ⟨box601,![exp66,exp30,exp4],![exp70,exp34,exp10],![exp68,exp32,exp6]⟩
theorem data601_lower_valid : ∀ j, (data601.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data601_upper_valid : ∀ j, (data601.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data601_center_valid : ∀ j, (data601.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin601 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data601 25 := by decide +kernel
theorem positive601 {q : EdgeTriple} (hq : q ∈ box601.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data601 25
    data601_lower_valid data601_upper_valid data601_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin601 hq

def box602 : LogBox := ⟨![(24105/4096 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data602 : S1TaylorBoxData := ⟨box602,![exp66,exp34,exp0],![exp70,exp38,exp4],![exp68,exp36,exp2]⟩
theorem data602_lower_valid : ∀ j, (data602.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data602_upper_valid : ∀ j, (data602.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data602_center_valid : ∀ j, (data602.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin602 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data602 25 := by decide +kernel
theorem positive602 {q : EdgeTriple} (hq : q ∈ box602.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data602 25
    data602_lower_valid data602_upper_valid data602_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin602 hq

def box603 : LogBox := ⟨![(24105/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data603 : S1TaylorBoxData := ⟨box603,![exp66,exp34,exp4],![exp70,exp38,exp10],![exp68,exp36,exp6]⟩
theorem data603_lower_valid : ∀ j, (data603.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data603_upper_valid : ∀ j, (data603.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data603_center_valid : ∀ j, (data603.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin603 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data603 25 := by decide +kernel
theorem positive603 {q : EdgeTriple} (hq : q ∈ box603.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data603 25
    data603_lower_valid data603_upper_valid data603_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin603 hq

def box604 : LogBox := ⟨![(11249/2048 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data604 : S1TaylorBoxData := ⟨box604,![exp62,exp30,exp10],![exp66,exp34,exp18],![exp64,exp32,exp14]⟩
theorem data604_lower_valid : ∀ j, (data604.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data604_upper_valid : ∀ j, (data604.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data604_center_valid : ∀ j, (data604.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin604 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data604 25 := by decide +kernel
theorem positive604 {q : EdgeTriple} (hq : q ∈ box604.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data604 25
    data604_lower_valid data604_upper_valid data604_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin604 hq

def box605 : LogBox := ⟨![(11249/2048 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data605 : S1TaylorBoxData := ⟨box605,![exp62,exp30,exp18],![exp66,exp34,exp22],![exp64,exp32,exp20]⟩
theorem data605_lower_valid : ∀ j, (data605.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data605_upper_valid : ∀ j, (data605.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data605_center_valid : ∀ j, (data605.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin605 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data605 25 := by decide +kernel
theorem positive605 {q : EdgeTriple} (hq : q ∈ box605.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data605 25
    data605_lower_valid data605_upper_valid data605_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin605 hq

def box606 : LogBox := ⟨![(11249/2048 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(24105/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data606 : S1TaylorBoxData := ⟨box606,![exp62,exp34,exp10],![exp66,exp38,exp18],![exp64,exp36,exp14]⟩
theorem data606_lower_valid : ∀ j, (data606.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data606_upper_valid : ∀ j, (data606.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data606_center_valid : ∀ j, (data606.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin606 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data606 25 := by decide +kernel
theorem positive606 {q : EdgeTriple} (hq : q ∈ box606.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data606 25
    data606_lower_valid data606_upper_valid data606_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin606 hq

def box607 : LogBox := ⟨![(11249/2048 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data607 : S1TaylorBoxData := ⟨box607,![exp62,exp34,exp18],![exp66,exp38,exp22],![exp64,exp36,exp20]⟩
theorem data607_lower_valid : ∀ j, (data607.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data607_upper_valid : ∀ j, (data607.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data607_center_valid : ∀ j, (data607.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin607 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data607 25 := by decide +kernel
theorem positive607 {q : EdgeTriple} (hq : q ∈ box607.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data607 25
    data607_lower_valid data607_upper_valid data607_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin607 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

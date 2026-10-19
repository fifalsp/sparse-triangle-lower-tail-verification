import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box560 : LogBox := ⟨![(20891/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data560 : S1TaylorBoxData := ⟨box560,![exp58,exp22,exp10],![exp62,exp26,exp18],![exp60,exp24,exp14]⟩
theorem data560_lower_valid : ∀ j, (data560.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data560_upper_valid : ∀ j, (data560.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data560_center_valid : ∀ j, (data560.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin560 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data560 25 := by decide +kernel
theorem positive560 {q : EdgeTriple} (hq : q ∈ box560.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data560 25
    data560_lower_valid data560_upper_valid data560_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin560 hq

def box561 : LogBox := ⟨![(20891/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data561 : S1TaylorBoxData := ⟨box561,![exp58,exp22,exp18],![exp62,exp26,exp22],![exp60,exp24,exp20]⟩
theorem data561_lower_valid : ∀ j, (data561.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data561_upper_valid : ∀ j, (data561.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data561_center_valid : ∀ j, (data561.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin561 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data561 25 := by decide +kernel
theorem positive561 {q : EdgeTriple} (hq : q ∈ box561.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data561 25
    data561_lower_valid data561_upper_valid data561_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin561 hq

def box562 : LogBox := ⟨![(20891/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(11249/2048 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data562 : S1TaylorBoxData := ⟨box562,![exp58,exp26,exp10],![exp62,exp30,exp18],![exp60,exp28,exp14]⟩
theorem data562_lower_valid : ∀ j, (data562.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data562_upper_valid : ∀ j, (data562.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data562_center_valid : ∀ j, (data562.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin562 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data562 25 := by decide +kernel
theorem positive562 {q : EdgeTriple} (hq : q ∈ box562.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data562 25
    data562_lower_valid data562_upper_valid data562_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin562 hq

def box563 : LogBox := ⟨![(20891/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(11249/2048 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data563 : S1TaylorBoxData := ⟨box563,![exp58,exp26,exp18],![exp62,exp30,exp22],![exp60,exp28,exp20]⟩
theorem data563_lower_valid : ∀ j, (data563.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data563_upper_valid : ∀ j, (data563.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data563_center_valid : ∀ j, (data563.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin563 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data563 25 := by decide +kernel
theorem positive563 {q : EdgeTriple} (hq : q ∈ box563.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data563 25
    data563_lower_valid data563_upper_valid data563_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin563 hq

def box564 : LogBox := ⟨![(4821/1024 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data564 : S1TaylorBoxData := ⟨box564,![exp54,exp30,exp0],![exp58,exp34,exp4],![exp56,exp32,exp2]⟩
theorem data564_lower_valid : ∀ j, (data564.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data564_upper_valid : ∀ j, (data564.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data564_center_valid : ∀ j, (data564.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin564 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data564 25 := by decide +kernel
theorem positive564 {q : EdgeTriple} (hq : q ∈ box564.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data564 25
    data564_lower_valid data564_upper_valid data564_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin564 hq

def box565 : LogBox := ⟨![(4821/1024 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data565 : S1TaylorBoxData := ⟨box565,![exp54,exp30,exp4],![exp58,exp34,exp10],![exp56,exp32,exp6]⟩
theorem data565_lower_valid : ∀ j, (data565.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data565_upper_valid : ∀ j, (data565.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data565_center_valid : ∀ j, (data565.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin565 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data565 25 := by decide +kernel
theorem positive565 {q : EdgeTriple} (hq : q ∈ box565.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data565 25
    data565_lower_valid data565_upper_valid data565_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin565 hq

def box566 : LogBox := ⟨![(4821/1024 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data566 : S1TaylorBoxData := ⟨box566,![exp54,exp34,exp0],![exp58,exp38,exp4],![exp56,exp36,exp2]⟩
theorem data566_lower_valid : ∀ j, (data566.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data566_upper_valid : ∀ j, (data566.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data566_center_valid : ∀ j, (data566.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin566 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data566 25 := by decide +kernel
theorem positive566 {q : EdgeTriple} (hq : q ∈ box566.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data566 25
    data566_lower_valid data566_upper_valid data566_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin566 hq

def box567 : LogBox := ⟨![(4821/1024 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data567 : S1TaylorBoxData := ⟨box567,![exp54,exp34,exp4],![exp58,exp38,exp10],![exp56,exp36,exp6]⟩
theorem data567_lower_valid : ∀ j, (data567.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data567_upper_valid : ∀ j, (data567.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data567_center_valid : ∀ j, (data567.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin567 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data567 25 := by decide +kernel
theorem positive567 {q : EdgeTriple} (hq : q ∈ box567.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data567 25
    data567_lower_valid data567_upper_valid data567_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin567 hq

def box568 : LogBox := ⟨![(20891/4096 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data568 : S1TaylorBoxData := ⟨box568,![exp58,exp30,exp0],![exp62,exp34,exp4],![exp60,exp32,exp2]⟩
theorem data568_lower_valid : ∀ j, (data568.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data568_upper_valid : ∀ j, (data568.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data568_center_valid : ∀ j, (data568.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin568 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data568 25 := by decide +kernel
theorem positive568 {q : EdgeTriple} (hq : q ∈ box568.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data568 25
    data568_lower_valid data568_upper_valid data568_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin568 hq

def box569 : LogBox := ⟨![(20891/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data569 : S1TaylorBoxData := ⟨box569,![exp58,exp30,exp4],![exp62,exp34,exp10],![exp60,exp32,exp6]⟩
theorem data569_lower_valid : ∀ j, (data569.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data569_upper_valid : ∀ j, (data569.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data569_center_valid : ∀ j, (data569.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin569 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data569 25 := by decide +kernel
theorem positive569 {q : EdgeTriple} (hq : q ∈ box569.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data569 25
    data569_lower_valid data569_upper_valid data569_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin569 hq

def box570 : LogBox := ⟨![(20891/4096 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data570 : S1TaylorBoxData := ⟨box570,![exp58,exp34,exp0],![exp62,exp38,exp4],![exp60,exp36,exp2]⟩
theorem data570_lower_valid : ∀ j, (data570.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data570_upper_valid : ∀ j, (data570.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data570_center_valid : ∀ j, (data570.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin570 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data570 25 := by decide +kernel
theorem positive570 {q : EdgeTriple} (hq : q ∈ box570.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data570 25
    data570_lower_valid data570_upper_valid data570_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin570 hq

def box571 : LogBox := ⟨![(20891/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data571 : S1TaylorBoxData := ⟨box571,![exp58,exp34,exp4],![exp62,exp38,exp10],![exp60,exp36,exp6]⟩
theorem data571_lower_valid : ∀ j, (data571.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data571_upper_valid : ∀ j, (data571.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data571_center_valid : ∀ j, (data571.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin571 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data571 25 := by decide +kernel
theorem positive571 {q : EdgeTriple} (hq : q ∈ box571.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data571 25
    data571_lower_valid data571_upper_valid data571_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin571 hq

def box572 : LogBox := ⟨![(4821/1024 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data572 : S1TaylorBoxData := ⟨box572,![exp54,exp30,exp10],![exp58,exp34,exp18],![exp56,exp32,exp14]⟩
theorem data572_lower_valid : ∀ j, (data572.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data572_upper_valid : ∀ j, (data572.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data572_center_valid : ∀ j, (data572.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp32_valid
  · exact exp14_valid
theorem margin572 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data572 25 := by decide +kernel
theorem positive572 {q : EdgeTriple} (hq : q ∈ box572.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data572 25
    data572_lower_valid data572_upper_valid data572_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin572 hq

def box573 : LogBox := ⟨![(4821/1024 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data573 : S1TaylorBoxData := ⟨box573,![exp54,exp30,exp18],![exp58,exp34,exp22],![exp56,exp32,exp20]⟩
theorem data573_lower_valid : ∀ j, (data573.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data573_upper_valid : ∀ j, (data573.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data573_center_valid : ∀ j, (data573.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp32_valid
  · exact exp20_valid
theorem margin573 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data573 25 := by decide +kernel
theorem positive573 {q : EdgeTriple} (hq : q ∈ box573.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data573 25
    data573_lower_valid data573_upper_valid data573_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin573 hq

def box574 : LogBox := ⟨![(4821/1024 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(1607/512 : ℚ),(4821/4096 : ℚ)]⟩
def data574 : S1TaylorBoxData := ⟨box574,![exp54,exp34,exp10],![exp58,exp38,exp18],![exp56,exp36,exp14]⟩
theorem data574_lower_valid : ∀ j, (data574.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data574_upper_valid : ∀ j, (data574.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp18_valid
theorem data574_center_valid : ∀ j, (data574.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp36_valid
  · exact exp14_valid
theorem margin574 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data574 25 := by decide +kernel
theorem positive574 {q : EdgeTriple} (hq : q ∈ box574.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data574 25
    data574_lower_valid data574_upper_valid data574_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin574 hq

def box575 : LogBox := ⟨![(4821/1024 : ℚ),(11249/4096 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/1024 : ℚ)]⟩
def data575 : S1TaylorBoxData := ⟨box575,![exp54,exp34,exp18],![exp58,exp38,exp22],![exp56,exp36,exp20]⟩
theorem data575_lower_valid : ∀ j, (data575.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp18_valid
theorem data575_upper_valid : ∀ j, (data575.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp22_valid
theorem data575_center_valid : ∀ j, (data575.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp36_valid
  · exact exp20_valid
theorem margin575 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data575 25 := by decide +kernel
theorem positive575 {q : EdgeTriple} (hq : q ∈ box575.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data575 25
    data575_lower_valid data575_upper_valid data575_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin575 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

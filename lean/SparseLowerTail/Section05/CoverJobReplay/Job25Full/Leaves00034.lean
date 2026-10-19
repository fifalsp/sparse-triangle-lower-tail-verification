import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box544 : LogBox := ⟨![(11249/2048 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(24105/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data544 : S1TaylorBoxData := ⟨box544,![exp62,exp18,exp18],![exp66,exp22,exp22],![exp64,exp20,exp20]⟩
theorem data544_lower_valid : ∀ j, (data544.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data544_upper_valid : ∀ j, (data544.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data544_center_valid : ∀ j, (data544.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin544 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data544 25 := by decide +kernel
theorem positive544 {q : EdgeTriple} (hq : q ∈ box544.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data544 25
    data544_lower_valid data544_upper_valid data544_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin544 hq

def box545 : LogBox := ⟨![(24105/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data545 : S1TaylorBoxData := ⟨box545,![exp66,exp10,exp10],![exp70,exp18,exp18],![exp68,exp14,exp14]⟩
theorem data545_lower_valid : ∀ j, (data545.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data545_upper_valid : ∀ j, (data545.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data545_center_valid : ∀ j, (data545.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin545 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data545 25 := by decide +kernel
theorem positive545 {q : EdgeTriple} (hq : q ∈ box545.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data545 25
    data545_lower_valid data545_upper_valid data545_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin545 hq

def box546 : LogBox := ⟨![(24105/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(1607/256 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data546 : S1TaylorBoxData := ⟨box546,![exp66,exp18,exp10],![exp70,exp22,exp18],![exp68,exp20,exp14]⟩
theorem data546_lower_valid : ∀ j, (data546.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data546_upper_valid : ∀ j, (data546.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data546_center_valid : ∀ j, (data546.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin546 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data546 25 := by decide +kernel
theorem positive546 {q : EdgeTriple} (hq : q ∈ box546.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data546 25
    data546_lower_valid data546_upper_valid data546_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin546 hq

def box547 : LogBox := ⟨![(24105/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(1607/256 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data547 : S1TaylorBoxData := ⟨box547,![exp66,exp18,exp18],![exp70,exp22,exp22],![exp68,exp20,exp20]⟩
theorem data547_lower_valid : ∀ j, (data547.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data547_upper_valid : ∀ j, (data547.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data547_center_valid : ∀ j, (data547.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin547 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data547 25 := by decide +kernel
theorem positive547 {q : EdgeTriple} (hq : q ∈ box547.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data547 25
    data547_lower_valid data547_upper_valid data547_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin547 hq

def box548 : LogBox := ⟨![(4821/1024 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data548 : S1TaylorBoxData := ⟨box548,![exp54,exp22,exp0],![exp58,exp26,exp4],![exp56,exp24,exp2]⟩
theorem data548_lower_valid : ∀ j, (data548.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data548_upper_valid : ∀ j, (data548.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data548_center_valid : ∀ j, (data548.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin548 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data548 25 := by decide +kernel
theorem positive548 {q : EdgeTriple} (hq : q ∈ box548.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data548 25
    data548_lower_valid data548_upper_valid data548_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin548 hq

def box549 : LogBox := ⟨![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data549 : S1TaylorBoxData := ⟨box549,![exp54,exp22,exp4],![exp58,exp26,exp10],![exp56,exp24,exp6]⟩
theorem data549_lower_valid : ∀ j, (data549.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data549_upper_valid : ∀ j, (data549.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data549_center_valid : ∀ j, (data549.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin549 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data549 25 := by decide +kernel
theorem positive549 {q : EdgeTriple} (hq : q ∈ box549.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data549 25
    data549_lower_valid data549_upper_valid data549_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin549 hq

def box550 : LogBox := ⟨![(4821/1024 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data550 : S1TaylorBoxData := ⟨box550,![exp54,exp26,exp0],![exp58,exp30,exp4],![exp56,exp28,exp2]⟩
theorem data550_lower_valid : ∀ j, (data550.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data550_upper_valid : ∀ j, (data550.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data550_center_valid : ∀ j, (data550.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin550 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data550 25 := by decide +kernel
theorem positive550 {q : EdgeTriple} (hq : q ∈ box550.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data550 25
    data550_lower_valid data550_upper_valid data550_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin550 hq

def box551 : LogBox := ⟨![(4821/1024 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data551 : S1TaylorBoxData := ⟨box551,![exp54,exp26,exp4],![exp58,exp30,exp10],![exp56,exp28,exp6]⟩
theorem data551_lower_valid : ∀ j, (data551.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data551_upper_valid : ∀ j, (data551.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data551_center_valid : ∀ j, (data551.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin551 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data551 25 := by decide +kernel
theorem positive551 {q : EdgeTriple} (hq : q ∈ box551.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data551 25
    data551_lower_valid data551_upper_valid data551_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin551 hq

def box552 : LogBox := ⟨![(20891/4096 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data552 : S1TaylorBoxData := ⟨box552,![exp58,exp22,exp0],![exp62,exp26,exp4],![exp60,exp24,exp2]⟩
theorem data552_lower_valid : ∀ j, (data552.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data552_upper_valid : ∀ j, (data552.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data552_center_valid : ∀ j, (data552.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin552 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data552 25 := by decide +kernel
theorem positive552 {q : EdgeTriple} (hq : q ∈ box552.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data552 25
    data552_lower_valid data552_upper_valid data552_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin552 hq

def box553 : LogBox := ⟨![(20891/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data553 : S1TaylorBoxData := ⟨box553,![exp58,exp22,exp4],![exp62,exp26,exp10],![exp60,exp24,exp6]⟩
theorem data553_lower_valid : ∀ j, (data553.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data553_upper_valid : ∀ j, (data553.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data553_center_valid : ∀ j, (data553.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin553 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data553 25 := by decide +kernel
theorem positive553 {q : EdgeTriple} (hq : q ∈ box553.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data553 25
    data553_lower_valid data553_upper_valid data553_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin553 hq

def box554 : LogBox := ⟨![(20891/4096 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data554 : S1TaylorBoxData := ⟨box554,![exp58,exp26,exp0],![exp62,exp30,exp4],![exp60,exp28,exp2]⟩
theorem data554_lower_valid : ∀ j, (data554.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data554_upper_valid : ∀ j, (data554.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data554_center_valid : ∀ j, (data554.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin554 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data554 25 := by decide +kernel
theorem positive554 {q : EdgeTriple} (hq : q ∈ box554.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data554 25
    data554_lower_valid data554_upper_valid data554_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin554 hq

def box555 : LogBox := ⟨![(20891/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data555 : S1TaylorBoxData := ⟨box555,![exp58,exp26,exp4],![exp62,exp30,exp10],![exp60,exp28,exp6]⟩
theorem data555_lower_valid : ∀ j, (data555.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data555_upper_valid : ∀ j, (data555.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data555_center_valid : ∀ j, (data555.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin555 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data555 25 := by decide +kernel
theorem positive555 {q : EdgeTriple} (hq : q ∈ box555.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data555 25
    data555_lower_valid data555_upper_valid data555_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin555 hq

def box556 : LogBox := ⟨![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data556 : S1TaylorBoxData := ⟨box556,![exp54,exp22,exp10],![exp58,exp26,exp18],![exp56,exp24,exp14]⟩
theorem data556_lower_valid : ∀ j, (data556.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data556_upper_valid : ∀ j, (data556.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data556_center_valid : ∀ j, (data556.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin556 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data556 25 := by decide +kernel
theorem positive556 {q : EdgeTriple} (hq : q ∈ box556.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data556 25
    data556_lower_valid data556_upper_valid data556_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin556 hq

def box557 : LogBox := ⟨![(4821/1024 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data557 : S1TaylorBoxData := ⟨box557,![exp54,exp22,exp18],![exp58,exp26,exp22],![exp56,exp24,exp20]⟩
theorem data557_lower_valid : ∀ j, (data557.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data557_upper_valid : ∀ j, (data557.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data557_center_valid : ∀ j, (data557.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin557 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data557 25 := by decide +kernel
theorem positive557 {q : EdgeTriple} (hq : q ∈ box557.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data557 25
    data557_lower_valid data557_upper_valid data557_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin557 hq

def box558 : LogBox := ⟨![(4821/1024 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data558 : S1TaylorBoxData := ⟨box558,![exp54,exp26,exp10],![exp58,exp30,exp18],![exp56,exp28,exp14]⟩
theorem data558_lower_valid : ∀ j, (data558.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data558_upper_valid : ∀ j, (data558.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data558_center_valid : ∀ j, (data558.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin558 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data558 25 := by decide +kernel
theorem positive558 {q : EdgeTriple} (hq : q ∈ box558.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data558 25
    data558_lower_valid data558_upper_valid data558_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin558 hq

def box559 : LogBox := ⟨![(4821/1024 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(20891/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data559 : S1TaylorBoxData := ⟨box559,![exp54,exp26,exp18],![exp58,exp30,exp22],![exp56,exp28,exp20]⟩
theorem data559_lower_valid : ∀ j, (data559.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data559_upper_valid : ∀ j, (data559.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data559_center_valid : ∀ j, (data559.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin559 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data559 25 := by decide +kernel
theorem positive559 {q : EdgeTriple} (hq : q ∈ box559.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data559 25
    data559_lower_valid data559_upper_valid data559_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin559 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

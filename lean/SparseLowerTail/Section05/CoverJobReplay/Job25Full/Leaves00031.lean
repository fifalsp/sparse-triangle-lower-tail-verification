import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box496 : LogBox := ⟨![(43389/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data496 : S1TaylorBoxData := ⟨box496,![exp60,exp2,exp0],![exp62,exp4,exp4],![exp61,exp3,exp2]⟩
theorem data496_lower_valid : ∀ j, (data496.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data496_upper_valid : ∀ j, (data496.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data496_center_valid : ∀ j, (data496.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp61_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin496 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data496 25 := by decide +kernel
theorem positive496 {q : EdgeTriple} (hq : q ∈ box496.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data496 25
    data496_lower_valid data496_upper_valid data496_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin496 hq

def box497 : LogBox := ⟨![(20891/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(43389/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data497 : S1TaylorBoxData := ⟨box497,![exp58,exp4,exp0],![exp60,exp6,exp4],![exp59,exp5,exp2]⟩
theorem data497_lower_valid : ∀ j, (data497.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data497_upper_valid : ∀ j, (data497.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data497_center_valid : ∀ j, (data497.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp59_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin497 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data497 25 := by decide +kernel
theorem positive497 {q : EdgeTriple} (hq : q ∈ box497.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data497 25
    data497_lower_valid data497_upper_valid data497_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin497 hq

def box498 : LogBox := ⟨![(20891/4096 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(43389/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data498 : S1TaylorBoxData := ⟨box498,![exp58,exp6,exp0],![exp60,exp10,exp4],![exp59,exp8,exp2]⟩
theorem data498_lower_valid : ∀ j, (data498.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data498_upper_valid : ∀ j, (data498.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data498_center_valid : ∀ j, (data498.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp59_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin498 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data498 25 := by decide +kernel
theorem positive498 {q : EdgeTriple} (hq : q ∈ box498.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data498 25
    data498_lower_valid data498_upper_valid data498_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin498 hq

def box499 : LogBox := ⟨![(43389/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data499 : S1TaylorBoxData := ⟨box499,![exp60,exp4,exp0],![exp62,exp6,exp4],![exp61,exp5,exp2]⟩
theorem data499_lower_valid : ∀ j, (data499.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data499_upper_valid : ∀ j, (data499.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data499_center_valid : ∀ j, (data499.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp61_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin499 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data499 25 := by decide +kernel
theorem positive499 {q : EdgeTriple} (hq : q ∈ box499.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data499 25
    data499_lower_valid data499_upper_valid data499_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin499 hq

def box500 : LogBox := ⟨![(43389/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data500 : S1TaylorBoxData := ⟨box500,![exp60,exp6,exp0],![exp62,exp10,exp4],![exp61,exp8,exp2]⟩
theorem data500_lower_valid : ∀ j, (data500.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data500_upper_valid : ∀ j, (data500.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data500_center_valid : ∀ j, (data500.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp61_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin500 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data500 25 := by decide +kernel
theorem positive500 {q : EdgeTriple} (hq : q ∈ box500.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data500 25
    data500_lower_valid data500_upper_valid data500_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin500 hq

def box501 : LogBox := ⟨![(20891/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data501 : S1TaylorBoxData := ⟨box501,![exp58,exp4,exp4],![exp62,exp10,exp10],![exp60,exp6,exp6]⟩
theorem data501_lower_valid : ∀ j, (data501.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data501_upper_valid : ∀ j, (data501.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data501_center_valid : ∀ j, (data501.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin501 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data501 25 := by decide +kernel
theorem positive501 {q : EdgeTriple} (hq : q ∈ box501.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data501 25
    data501_lower_valid data501_upper_valid data501_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin501 hq

def box502 : LogBox := ⟨![(4821/1024 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data502 : S1TaylorBoxData := ⟨box502,![exp54,exp10,exp0],![exp58,exp18,exp4],![exp56,exp14,exp2]⟩
theorem data502_lower_valid : ∀ j, (data502.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data502_upper_valid : ∀ j, (data502.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data502_center_valid : ∀ j, (data502.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp14_valid
  · exact exp2_valid
theorem margin502 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data502 25 := by decide +kernel
theorem positive502 {q : EdgeTriple} (hq : q ∈ box502.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data502 25
    data502_lower_valid data502_upper_valid data502_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin502 hq

def box503 : LogBox := ⟨![(4821/1024 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data503 : S1TaylorBoxData := ⟨box503,![exp54,exp10,exp4],![exp58,exp18,exp10],![exp56,exp14,exp6]⟩
theorem data503_lower_valid : ∀ j, (data503.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data503_upper_valid : ∀ j, (data503.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data503_center_valid : ∀ j, (data503.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin503 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data503 25 := by decide +kernel
theorem positive503 {q : EdgeTriple} (hq : q ∈ box503.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data503 25
    data503_lower_valid data503_upper_valid data503_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin503 hq

def box504 : LogBox := ⟨![(4821/1024 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data504 : S1TaylorBoxData := ⟨box504,![exp54,exp18,exp0],![exp58,exp22,exp4],![exp56,exp20,exp2]⟩
theorem data504_lower_valid : ∀ j, (data504.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data504_upper_valid : ∀ j, (data504.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data504_center_valid : ∀ j, (data504.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin504 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data504 25 := by decide +kernel
theorem positive504 {q : EdgeTriple} (hq : q ∈ box504.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data504 25
    data504_lower_valid data504_upper_valid data504_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin504 hq

def box505 : LogBox := ⟨![(4821/1024 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data505 : S1TaylorBoxData := ⟨box505,![exp54,exp18,exp4],![exp58,exp22,exp10],![exp56,exp20,exp6]⟩
theorem data505_lower_valid : ∀ j, (data505.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data505_upper_valid : ∀ j, (data505.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data505_center_valid : ∀ j, (data505.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin505 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data505 25 := by decide +kernel
theorem positive505 {q : EdgeTriple} (hq : q ∈ box505.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data505 25
    data505_lower_valid data505_upper_valid data505_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin505 hq

def box506 : LogBox := ⟨![(20891/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data506 : S1TaylorBoxData := ⟨box506,![exp58,exp10,exp0],![exp62,exp18,exp4],![exp60,exp14,exp2]⟩
theorem data506_lower_valid : ∀ j, (data506.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data506_upper_valid : ∀ j, (data506.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data506_center_valid : ∀ j, (data506.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp14_valid
  · exact exp2_valid
theorem margin506 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data506 25 := by decide +kernel
theorem positive506 {q : EdgeTriple} (hq : q ∈ box506.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data506 25
    data506_lower_valid data506_upper_valid data506_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin506 hq

def box507 : LogBox := ⟨![(20891/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data507 : S1TaylorBoxData := ⟨box507,![exp58,exp10,exp4],![exp62,exp18,exp10],![exp60,exp14,exp6]⟩
theorem data507_lower_valid : ∀ j, (data507.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data507_upper_valid : ∀ j, (data507.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data507_center_valid : ∀ j, (data507.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin507 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data507 25 := by decide +kernel
theorem positive507 {q : EdgeTriple} (hq : q ∈ box507.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data507 25
    data507_lower_valid data507_upper_valid data507_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin507 hq

def box508 : LogBox := ⟨![(20891/4096 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data508 : S1TaylorBoxData := ⟨box508,![exp58,exp18,exp0],![exp62,exp22,exp4],![exp60,exp20,exp2]⟩
theorem data508_lower_valid : ∀ j, (data508.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data508_upper_valid : ∀ j, (data508.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data508_center_valid : ∀ j, (data508.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin508 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data508 25 := by decide +kernel
theorem positive508 {q : EdgeTriple} (hq : q ∈ box508.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data508 25
    data508_lower_valid data508_upper_valid data508_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin508 hq

def box509 : LogBox := ⟨![(20891/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(11249/2048 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data509 : S1TaylorBoxData := ⟨box509,![exp58,exp18,exp4],![exp62,exp22,exp10],![exp60,exp20,exp6]⟩
theorem data509_lower_valid : ∀ j, (data509.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data509_upper_valid : ∀ j, (data509.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data509_center_valid : ∀ j, (data509.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin509 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data509 25 := by decide +kernel
theorem positive509 {q : EdgeTriple} (hq : q ∈ box509.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data509 25
    data509_lower_valid data509_upper_valid data509_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin509 hq

def box510 : LogBox := ⟨![(4821/1024 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data510 : S1TaylorBoxData := ⟨box510,![exp54,exp10,exp10],![exp58,exp18,exp18],![exp56,exp14,exp14]⟩
theorem data510_lower_valid : ∀ j, (data510.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data510_upper_valid : ∀ j, (data510.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data510_center_valid : ∀ j, (data510.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin510 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data510 25 := by decide +kernel
theorem positive510 {q : EdgeTriple} (hq : q ∈ box510.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data510 25
    data510_lower_valid data510_upper_valid data510_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin510 hq

def box511 : LogBox := ⟨![(4821/1024 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(20891/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data511 : S1TaylorBoxData := ⟨box511,![exp54,exp18,exp10],![exp58,exp22,exp18],![exp56,exp20,exp14]⟩
theorem data511_lower_valid : ∀ j, (data511.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data511_upper_valid : ∀ j, (data511.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data511_center_valid : ∀ j, (data511.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin511 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data511 25 := by decide +kernel
theorem positive511 {q : EdgeTriple} (hq : q ∈ box511.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data511 25
    data511_lower_valid data511_upper_valid data511_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin511 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box352 : LogBox := ⟨![(14463/4096 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data352 : S1TaylorBoxData := ⟨box352,![exp42,exp18,exp0],![exp46,exp22,exp4],![exp44,exp20,exp2]⟩
theorem data352_lower_valid : ∀ j, (data352.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data352_upper_valid : ∀ j, (data352.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data352_center_valid : ∀ j, (data352.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin352 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data352 25 := by decide +kernel
theorem positive352 {q : EdgeTriple} (hq : q ∈ box352.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data352 25
    data352_lower_valid data352_upper_valid data352_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin352 hq

def box353 : LogBox := ⟨![(14463/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data353 : S1TaylorBoxData := ⟨box353,![exp42,exp18,exp4],![exp46,exp22,exp10],![exp44,exp20,exp6]⟩
theorem data353_lower_valid : ∀ j, (data353.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data353_upper_valid : ∀ j, (data353.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data353_center_valid : ∀ j, (data353.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin353 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data353 25 := by decide +kernel
theorem positive353 {q : EdgeTriple} (hq : q ∈ box353.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data353 25
    data353_lower_valid data353_upper_valid data353_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin353 hq

def box354 : LogBox := ⟨![(1607/512 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(14463/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data354 : S1TaylorBoxData := ⟨box354,![exp38,exp10,exp10],![exp42,exp18,exp18],![exp40,exp14,exp14]⟩
theorem data354_lower_valid : ∀ j, (data354.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data354_upper_valid : ∀ j, (data354.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data354_center_valid : ∀ j, (data354.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin354 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data354 25 := by decide +kernel
theorem positive354 {q : EdgeTriple} (hq : q ∈ box354.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data354 25
    data354_lower_valid data354_upper_valid data354_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin354 hq

def box355 : LogBox := ⟨![(1607/512 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(14463/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data355 : S1TaylorBoxData := ⟨box355,![exp38,exp18,exp10],![exp42,exp22,exp18],![exp40,exp20,exp14]⟩
theorem data355_lower_valid : ∀ j, (data355.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data355_upper_valid : ∀ j, (data355.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data355_center_valid : ∀ j, (data355.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin355 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data355 25 := by decide +kernel
theorem positive355 {q : EdgeTriple} (hq : q ∈ box355.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data355 25
    data355_lower_valid data355_upper_valid data355_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin355 hq

def box356 : LogBox := ⟨![(1607/512 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(14463/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data356 : S1TaylorBoxData := ⟨box356,![exp38,exp18,exp18],![exp42,exp22,exp22],![exp40,exp20,exp20]⟩
theorem data356_lower_valid : ∀ j, (data356.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data356_upper_valid : ∀ j, (data356.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data356_center_valid : ∀ j, (data356.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin356 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data356 25 := by decide +kernel
theorem positive356 {q : EdgeTriple} (hq : q ∈ box356.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data356 25
    data356_lower_valid data356_upper_valid data356_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin356 hq

def box357 : LogBox := ⟨![(14463/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data357 : S1TaylorBoxData := ⟨box357,![exp42,exp10,exp10],![exp46,exp18,exp18],![exp44,exp14,exp14]⟩
theorem data357_lower_valid : ∀ j, (data357.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data357_upper_valid : ∀ j, (data357.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data357_center_valid : ∀ j, (data357.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin357 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data357 25 := by decide +kernel
theorem positive357 {q : EdgeTriple} (hq : q ∈ box357.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data357 25
    data357_lower_valid data357_upper_valid data357_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin357 hq

def box358 : LogBox := ⟨![(14463/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data358 : S1TaylorBoxData := ⟨box358,![exp42,exp18,exp10],![exp46,exp22,exp18],![exp44,exp20,exp14]⟩
theorem data358_lower_valid : ∀ j, (data358.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data358_upper_valid : ∀ j, (data358.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data358_center_valid : ∀ j, (data358.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin358 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data358 25 := by decide +kernel
theorem positive358 {q : EdgeTriple} (hq : q ∈ box358.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data358 25
    data358_lower_valid data358_upper_valid data358_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin358 hq

def box359 : LogBox := ⟨![(14463/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(8035/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data359 : S1TaylorBoxData := ⟨box359,![exp42,exp18,exp18],![exp46,exp22,exp22],![exp44,exp20,exp20]⟩
theorem data359_lower_valid : ∀ j, (data359.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data359_upper_valid : ∀ j, (data359.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data359_center_valid : ∀ j, (data359.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin359 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data359 25 := by decide +kernel
theorem positive359 {q : EdgeTriple} (hq : q ∈ box359.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data359 25
    data359_lower_valid data359_upper_valid data359_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin359 hq

def box360 : LogBox := ⟨![(8035/2048 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(33747/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data360 : S1TaylorBoxData := ⟨box360,![exp46,exp0,exp0],![exp48,exp2,exp2],![exp47,exp1,exp1]⟩
theorem data360_lower_valid : ∀ j, (data360.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data360_upper_valid : ∀ j, (data360.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data360_center_valid : ∀ j, (data360.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp47_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin360 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data360 25 := by decide +kernel
theorem positive360 {q : EdgeTriple} (hq : q ∈ box360.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data360 25
    data360_lower_valid data360_upper_valid data360_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin360 hq

def box361 : LogBox := ⟨![(8035/2048 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(33747/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data361 : S1TaylorBoxData := ⟨box361,![exp46,exp2,exp0],![exp48,exp4,exp4],![exp47,exp3,exp2]⟩
theorem data361_lower_valid : ∀ j, (data361.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data361_upper_valid : ∀ j, (data361.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data361_center_valid : ∀ j, (data361.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp47_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin361 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data361 25 := by decide +kernel
theorem positive361 {q : EdgeTriple} (hq : q ∈ box361.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data361 25
    data361_lower_valid data361_upper_valid data361_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin361 hq

def box362 : LogBox := ⟨![(33747/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data362 : S1TaylorBoxData := ⟨box362,![exp48,exp0,exp0],![exp50,exp2,exp2],![exp49,exp1,exp1]⟩
theorem data362_lower_valid : ∀ j, (data362.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data362_upper_valid : ∀ j, (data362.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data362_center_valid : ∀ j, (data362.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp49_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin362 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data362 25 := by decide +kernel
theorem positive362 {q : EdgeTriple} (hq : q ∈ box362.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data362 25
    data362_lower_valid data362_upper_valid data362_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin362 hq

def box363 : LogBox := ⟨![(33747/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data363 : S1TaylorBoxData := ⟨box363,![exp48,exp2,exp0],![exp50,exp4,exp4],![exp49,exp3,exp2]⟩
theorem data363_lower_valid : ∀ j, (data363.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data363_upper_valid : ∀ j, (data363.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data363_center_valid : ∀ j, (data363.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp49_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin363 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data363 25 := by decide +kernel
theorem positive363 {q : EdgeTriple} (hq : q ∈ box363.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data363 25
    data363_lower_valid data363_upper_valid data363_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin363 hq

def box364 : LogBox := ⟨![(8035/2048 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(33747/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data364 : S1TaylorBoxData := ⟨box364,![exp46,exp4,exp0],![exp48,exp6,exp4],![exp47,exp5,exp2]⟩
theorem data364_lower_valid : ∀ j, (data364.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data364_upper_valid : ∀ j, (data364.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data364_center_valid : ∀ j, (data364.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp47_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin364 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data364 25 := by decide +kernel
theorem positive364 {q : EdgeTriple} (hq : q ∈ box364.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data364 25
    data364_lower_valid data364_upper_valid data364_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin364 hq

def box365 : LogBox := ⟨![(8035/2048 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(33747/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data365 : S1TaylorBoxData := ⟨box365,![exp46,exp6,exp0],![exp48,exp10,exp4],![exp47,exp8,exp2]⟩
theorem data365_lower_valid : ∀ j, (data365.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data365_upper_valid : ∀ j, (data365.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data365_center_valid : ∀ j, (data365.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp47_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin365 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data365 25 := by decide +kernel
theorem positive365 {q : EdgeTriple} (hq : q ∈ box365.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data365 25
    data365_lower_valid data365_upper_valid data365_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin365 hq

def box366 : LogBox := ⟨![(33747/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data366 : S1TaylorBoxData := ⟨box366,![exp48,exp4,exp0],![exp50,exp6,exp4],![exp49,exp5,exp2]⟩
theorem data366_lower_valid : ∀ j, (data366.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data366_upper_valid : ∀ j, (data366.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data366_center_valid : ∀ j, (data366.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp49_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin366 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data366 25 := by decide +kernel
theorem positive366 {q : EdgeTriple} (hq : q ∈ box366.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data366 25
    data366_lower_valid data366_upper_valid data366_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin366 hq

def box367 : LogBox := ⟨![(33747/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data367 : S1TaylorBoxData := ⟨box367,![exp48,exp6,exp0],![exp50,exp10,exp4],![exp49,exp8,exp2]⟩
theorem data367_lower_valid : ∀ j, (data367.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data367_upper_valid : ∀ j, (data367.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data367_center_valid : ∀ j, (data367.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp49_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin367 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data367 25 := by decide +kernel
theorem positive367 {q : EdgeTriple} (hq : q ∈ box367.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data367 25
    data367_lower_valid data367_upper_valid data367_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin367 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

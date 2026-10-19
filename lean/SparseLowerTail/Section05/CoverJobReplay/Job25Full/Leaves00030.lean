import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box480 : LogBox := ⟨![(8035/2048 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(17677/4096 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data480 : S1TaylorBoxData := ⟨box480,![exp46,exp30,exp30],![exp50,exp34,exp34],![exp48,exp32,exp32]⟩
theorem data480_lower_valid : ∀ j, (data480.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data480_upper_valid : ∀ j, (data480.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data480_center_valid : ∀ j, (data480.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin480 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data480 25 := by decide +kernel
theorem positive480 {q : EdgeTriple} (hq : q ∈ box480.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data480 25
    data480_lower_valid data480_upper_valid data480_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin480 hq

def box481 : LogBox := ⟨![(8035/2048 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data481 : S1TaylorBoxData := ⟨box481,![exp46,exp34,exp30],![exp50,exp38,exp38],![exp48,exp36,exp34]⟩
theorem data481_lower_valid : ∀ j, (data481.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data481_upper_valid : ∀ j, (data481.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data481_center_valid : ∀ j, (data481.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin481 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data481 25 := by decide +kernel
theorem positive481 {q : EdgeTriple} (hq : q ∈ box481.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data481 25
    data481_lower_valid data481_upper_valid data481_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin481 hq

def box482 : LogBox := ⟨![(17677/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(4821/1024 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data482 : S1TaylorBoxData := ⟨box482,![exp50,exp30,exp30],![exp54,exp34,exp34],![exp52,exp32,exp32]⟩
theorem data482_lower_valid : ∀ j, (data482.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data482_upper_valid : ∀ j, (data482.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data482_center_valid : ∀ j, (data482.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin482 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data482 25 := by decide +kernel
theorem positive482 {q : EdgeTriple} (hq : q ∈ box482.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data482 25
    data482_lower_valid data482_upper_valid data482_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin482 hq

def box483 : LogBox := ⟨![(17677/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data483 : S1TaylorBoxData := ⟨box483,![exp50,exp34,exp30],![exp54,exp38,exp38],![exp52,exp36,exp34]⟩
theorem data483_lower_valid : ∀ j, (data483.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data483_upper_valid : ∀ j, (data483.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data483_center_valid : ∀ j, (data483.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin483 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data483 25 := by decide +kernel
theorem positive483 {q : EdgeTriple} (hq : q ∈ box483.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data483 25
    data483_lower_valid data483_upper_valid data483_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin483 hq

def box484 : LogBox := ⟨![(4821/1024 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(40175/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data484 : S1TaylorBoxData := ⟨box484,![exp54,exp0,exp0],![exp56,exp2,exp2],![exp55,exp1,exp1]⟩
theorem data484_lower_valid : ∀ j, (data484.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data484_upper_valid : ∀ j, (data484.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data484_center_valid : ∀ j, (data484.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp55_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin484 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data484 25 := by decide +kernel
theorem positive484 {q : EdgeTriple} (hq : q ∈ box484.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data484 25
    data484_lower_valid data484_upper_valid data484_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin484 hq

def box485 : LogBox := ⟨![(4821/1024 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(40175/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data485 : S1TaylorBoxData := ⟨box485,![exp54,exp2,exp0],![exp56,exp4,exp4],![exp55,exp3,exp2]⟩
theorem data485_lower_valid : ∀ j, (data485.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data485_upper_valid : ∀ j, (data485.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data485_center_valid : ∀ j, (data485.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp55_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin485 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data485 25 := by decide +kernel
theorem positive485 {q : EdgeTriple} (hq : q ∈ box485.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data485 25
    data485_lower_valid data485_upper_valid data485_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin485 hq

def box486 : LogBox := ⟨![(40175/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data486 : S1TaylorBoxData := ⟨box486,![exp56,exp0,exp0],![exp58,exp2,exp2],![exp57,exp1,exp1]⟩
theorem data486_lower_valid : ∀ j, (data486.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data486_upper_valid : ∀ j, (data486.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data486_center_valid : ∀ j, (data486.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp57_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin486 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data486 25 := by decide +kernel
theorem positive486 {q : EdgeTriple} (hq : q ∈ box486.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data486 25
    data486_lower_valid data486_upper_valid data486_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin486 hq

def box487 : LogBox := ⟨![(40175/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data487 : S1TaylorBoxData := ⟨box487,![exp56,exp2,exp0],![exp58,exp4,exp4],![exp57,exp3,exp2]⟩
theorem data487_lower_valid : ∀ j, (data487.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data487_upper_valid : ∀ j, (data487.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data487_center_valid : ∀ j, (data487.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp57_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin487 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data487 25 := by decide +kernel
theorem positive487 {q : EdgeTriple} (hq : q ∈ box487.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data487 25
    data487_lower_valid data487_upper_valid data487_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin487 hq

def box488 : LogBox := ⟨![(4821/1024 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(40175/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data488 : S1TaylorBoxData := ⟨box488,![exp54,exp4,exp0],![exp56,exp6,exp4],![exp55,exp5,exp2]⟩
theorem data488_lower_valid : ∀ j, (data488.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data488_upper_valid : ∀ j, (data488.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data488_center_valid : ∀ j, (data488.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp55_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin488 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data488 25 := by decide +kernel
theorem positive488 {q : EdgeTriple} (hq : q ∈ box488.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data488 25
    data488_lower_valid data488_upper_valid data488_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin488 hq

def box489 : LogBox := ⟨![(4821/1024 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(40175/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data489 : S1TaylorBoxData := ⟨box489,![exp54,exp6,exp0],![exp56,exp10,exp4],![exp55,exp8,exp2]⟩
theorem data489_lower_valid : ∀ j, (data489.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data489_upper_valid : ∀ j, (data489.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data489_center_valid : ∀ j, (data489.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp55_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin489 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data489 25 := by decide +kernel
theorem positive489 {q : EdgeTriple} (hq : q ∈ box489.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data489 25
    data489_lower_valid data489_upper_valid data489_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin489 hq

def box490 : LogBox := ⟨![(40175/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data490 : S1TaylorBoxData := ⟨box490,![exp56,exp4,exp0],![exp58,exp6,exp4],![exp57,exp5,exp2]⟩
theorem data490_lower_valid : ∀ j, (data490.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data490_upper_valid : ∀ j, (data490.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data490_center_valid : ∀ j, (data490.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp57_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin490 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data490 25 := by decide +kernel
theorem positive490 {q : EdgeTriple} (hq : q ∈ box490.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data490 25
    data490_lower_valid data490_upper_valid data490_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin490 hq

def box491 : LogBox := ⟨![(40175/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(20891/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data491 : S1TaylorBoxData := ⟨box491,![exp56,exp6,exp0],![exp58,exp10,exp4],![exp57,exp8,exp2]⟩
theorem data491_lower_valid : ∀ j, (data491.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data491_upper_valid : ∀ j, (data491.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data491_center_valid : ∀ j, (data491.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp57_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin491 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data491 25 := by decide +kernel
theorem positive491 {q : EdgeTriple} (hq : q ∈ box491.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data491 25
    data491_lower_valid data491_upper_valid data491_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin491 hq

def box492 : LogBox := ⟨![(4821/1024 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(20891/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data492 : S1TaylorBoxData := ⟨box492,![exp54,exp4,exp4],![exp58,exp10,exp10],![exp56,exp6,exp6]⟩
theorem data492_lower_valid : ∀ j, (data492.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data492_upper_valid : ∀ j, (data492.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data492_center_valid : ∀ j, (data492.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin492 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data492 25 := by decide +kernel
theorem positive492 {q : EdgeTriple} (hq : q ∈ box492.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data492 25
    data492_lower_valid data492_upper_valid data492_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin492 hq

def box493 : LogBox := ⟨![(20891/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(43389/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data493 : S1TaylorBoxData := ⟨box493,![exp58,exp0,exp0],![exp60,exp2,exp2],![exp59,exp1,exp1]⟩
theorem data493_lower_valid : ∀ j, (data493.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data493_upper_valid : ∀ j, (data493.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data493_center_valid : ∀ j, (data493.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp59_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin493 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data493 25 := by decide +kernel
theorem positive493 {q : EdgeTriple} (hq : q ∈ box493.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data493 25
    data493_lower_valid data493_upper_valid data493_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin493 hq

def box494 : LogBox := ⟨![(20891/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(43389/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data494 : S1TaylorBoxData := ⟨box494,![exp58,exp2,exp0],![exp60,exp4,exp4],![exp59,exp3,exp2]⟩
theorem data494_lower_valid : ∀ j, (data494.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data494_upper_valid : ∀ j, (data494.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data494_center_valid : ∀ j, (data494.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp59_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin494 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data494 25 := by decide +kernel
theorem positive494 {q : EdgeTriple} (hq : q ∈ box494.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data494 25
    data494_lower_valid data494_upper_valid data494_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin494 hq

def box495 : LogBox := ⟨![(43389/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(11249/2048 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data495 : S1TaylorBoxData := ⟨box495,![exp60,exp0,exp0],![exp62,exp2,exp2],![exp61,exp1,exp1]⟩
theorem data495_lower_valid : ∀ j, (data495.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data495_upper_valid : ∀ j, (data495.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data495_center_valid : ∀ j, (data495.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp61_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin495 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data495 25 := by decide +kernel
theorem positive495 {q : EdgeTriple} (hq : q ∈ box495.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data495 25
    data495_lower_valid data495_upper_valid data495_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin495 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

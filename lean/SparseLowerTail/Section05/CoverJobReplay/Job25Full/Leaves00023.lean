import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box368 : LogBox := ⟨![(8035/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data368 : S1TaylorBoxData := ⟨box368,![exp46,exp4,exp4],![exp50,exp10,exp10],![exp48,exp6,exp6]⟩
theorem data368_lower_valid : ∀ j, (data368.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data368_upper_valid : ∀ j, (data368.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data368_center_valid : ∀ j, (data368.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin368 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data368 25 := by decide +kernel
theorem positive368 {q : EdgeTriple} (hq : q ∈ box368.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data368 25
    data368_lower_valid data368_upper_valid data368_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin368 hq

def box369 : LogBox := ⟨![(17677/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(36961/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data369 : S1TaylorBoxData := ⟨box369,![exp50,exp0,exp0],![exp52,exp2,exp2],![exp51,exp1,exp1]⟩
theorem data369_lower_valid : ∀ j, (data369.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data369_upper_valid : ∀ j, (data369.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data369_center_valid : ∀ j, (data369.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp51_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin369 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data369 25 := by decide +kernel
theorem positive369 {q : EdgeTriple} (hq : q ∈ box369.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data369 25
    data369_lower_valid data369_upper_valid data369_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin369 hq

def box370 : LogBox := ⟨![(17677/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(36961/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data370 : S1TaylorBoxData := ⟨box370,![exp50,exp2,exp0],![exp52,exp4,exp4],![exp51,exp3,exp2]⟩
theorem data370_lower_valid : ∀ j, (data370.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data370_upper_valid : ∀ j, (data370.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data370_center_valid : ∀ j, (data370.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp51_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin370 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data370 25 := by decide +kernel
theorem positive370 {q : EdgeTriple} (hq : q ∈ box370.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data370 25
    data370_lower_valid data370_upper_valid data370_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin370 hq

def box371 : LogBox := ⟨![(36961/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data371 : S1TaylorBoxData := ⟨box371,![exp52,exp0,exp0],![exp54,exp2,exp2],![exp53,exp1,exp1]⟩
theorem data371_lower_valid : ∀ j, (data371.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data371_upper_valid : ∀ j, (data371.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data371_center_valid : ∀ j, (data371.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp53_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin371 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data371 25 := by decide +kernel
theorem positive371 {q : EdgeTriple} (hq : q ∈ box371.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data371 25
    data371_lower_valid data371_upper_valid data371_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin371 hq

def box372 : LogBox := ⟨![(36961/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data372 : S1TaylorBoxData := ⟨box372,![exp52,exp2,exp0],![exp54,exp4,exp4],![exp53,exp3,exp2]⟩
theorem data372_lower_valid : ∀ j, (data372.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data372_upper_valid : ∀ j, (data372.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data372_center_valid : ∀ j, (data372.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp53_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin372 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data372 25 := by decide +kernel
theorem positive372 {q : EdgeTriple} (hq : q ∈ box372.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data372 25
    data372_lower_valid data372_upper_valid data372_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin372 hq

def box373 : LogBox := ⟨![(17677/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(36961/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data373 : S1TaylorBoxData := ⟨box373,![exp50,exp4,exp0],![exp52,exp6,exp4],![exp51,exp5,exp2]⟩
theorem data373_lower_valid : ∀ j, (data373.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data373_upper_valid : ∀ j, (data373.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data373_center_valid : ∀ j, (data373.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp51_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin373 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data373 25 := by decide +kernel
theorem positive373 {q : EdgeTriple} (hq : q ∈ box373.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data373 25
    data373_lower_valid data373_upper_valid data373_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin373 hq

def box374 : LogBox := ⟨![(17677/4096 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(36961/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data374 : S1TaylorBoxData := ⟨box374,![exp50,exp6,exp0],![exp52,exp10,exp4],![exp51,exp8,exp2]⟩
theorem data374_lower_valid : ∀ j, (data374.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data374_upper_valid : ∀ j, (data374.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data374_center_valid : ∀ j, (data374.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp51_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin374 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data374 25 := by decide +kernel
theorem positive374 {q : EdgeTriple} (hq : q ∈ box374.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data374 25
    data374_lower_valid data374_upper_valid data374_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin374 hq

def box375 : LogBox := ⟨![(36961/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data375 : S1TaylorBoxData := ⟨box375,![exp52,exp4,exp0],![exp54,exp6,exp4],![exp53,exp5,exp2]⟩
theorem data375_lower_valid : ∀ j, (data375.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data375_upper_valid : ∀ j, (data375.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data375_center_valid : ∀ j, (data375.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp53_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin375 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data375 25 := by decide +kernel
theorem positive375 {q : EdgeTriple} (hq : q ∈ box375.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data375 25
    data375_lower_valid data375_upper_valid data375_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin375 hq

def box376 : LogBox := ⟨![(36961/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data376 : S1TaylorBoxData := ⟨box376,![exp52,exp6,exp0],![exp54,exp10,exp4],![exp53,exp8,exp2]⟩
theorem data376_lower_valid : ∀ j, (data376.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data376_upper_valid : ∀ j, (data376.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data376_center_valid : ∀ j, (data376.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp53_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin376 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data376 25 := by decide +kernel
theorem positive376 {q : EdgeTriple} (hq : q ∈ box376.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data376 25
    data376_lower_valid data376_upper_valid data376_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin376 hq

def box377 : LogBox := ⟨![(17677/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data377 : S1TaylorBoxData := ⟨box377,![exp50,exp4,exp4],![exp54,exp10,exp10],![exp52,exp6,exp6]⟩
theorem data377_lower_valid : ∀ j, (data377.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data377_upper_valid : ∀ j, (data377.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data377_center_valid : ∀ j, (data377.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin377 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data377 25 := by decide +kernel
theorem positive377 {q : EdgeTriple} (hq : q ∈ box377.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data377 25
    data377_lower_valid data377_upper_valid data377_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin377 hq

def box378 : LogBox := ⟨![(8035/2048 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(33747/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data378 : S1TaylorBoxData := ⟨box378,![exp46,exp10,exp0],![exp48,exp14,exp4],![exp47,exp12,exp2]⟩
theorem data378_lower_valid : ∀ j, (data378.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data378_upper_valid : ∀ j, (data378.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data378_center_valid : ∀ j, (data378.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp47_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin378 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data378 25 := by decide +kernel
theorem positive378 {q : EdgeTriple} (hq : q ∈ box378.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data378 25
    data378_lower_valid data378_upper_valid data378_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin378 hq

def box379 : LogBox := ⟨![(8035/2048 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(33747/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data379 : S1TaylorBoxData := ⟨box379,![exp46,exp14,exp0],![exp48,exp18,exp4],![exp47,exp16,exp2]⟩
theorem data379_lower_valid : ∀ j, (data379.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data379_upper_valid : ∀ j, (data379.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data379_center_valid : ∀ j, (data379.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp47_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin379 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data379 25 := by decide +kernel
theorem positive379 {q : EdgeTriple} (hq : q ∈ box379.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data379 25
    data379_lower_valid data379_upper_valid data379_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin379 hq

def box380 : LogBox := ⟨![(33747/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data380 : S1TaylorBoxData := ⟨box380,![exp48,exp10,exp0],![exp50,exp14,exp4],![exp49,exp12,exp2]⟩
theorem data380_lower_valid : ∀ j, (data380.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data380_upper_valid : ∀ j, (data380.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data380_center_valid : ∀ j, (data380.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp49_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin380 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data380 25 := by decide +kernel
theorem positive380 {q : EdgeTriple} (hq : q ∈ box380.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data380 25
    data380_lower_valid data380_upper_valid data380_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin380 hq

def box381 : LogBox := ⟨![(33747/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data381 : S1TaylorBoxData := ⟨box381,![exp48,exp14,exp0],![exp50,exp18,exp4],![exp49,exp16,exp2]⟩
theorem data381_lower_valid : ∀ j, (data381.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data381_upper_valid : ∀ j, (data381.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data381_center_valid : ∀ j, (data381.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp49_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin381 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data381 25 := by decide +kernel
theorem positive381 {q : EdgeTriple} (hq : q ∈ box381.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data381 25
    data381_lower_valid data381_upper_valid data381_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin381 hq

def box382 : LogBox := ⟨![(8035/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data382 : S1TaylorBoxData := ⟨box382,![exp46,exp10,exp4],![exp50,exp18,exp10],![exp48,exp14,exp6]⟩
theorem data382_lower_valid : ∀ j, (data382.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data382_upper_valid : ∀ j, (data382.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data382_center_valid : ∀ j, (data382.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin382 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data382 25 := by decide +kernel
theorem positive382 {q : EdgeTriple} (hq : q ∈ box382.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data382 25
    data382_lower_valid data382_upper_valid data382_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin382 hq

def box383 : LogBox := ⟨![(8035/2048 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(17677/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data383 : S1TaylorBoxData := ⟨box383,![exp46,exp18,exp0],![exp50,exp22,exp4],![exp48,exp20,exp2]⟩
theorem data383_lower_valid : ∀ j, (data383.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data383_upper_valid : ∀ j, (data383.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data383_center_valid : ∀ j, (data383.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin383 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data383 25 := by decide +kernel
theorem positive383 {q : EdgeTriple} (hq : q ∈ box383.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data383 25
    data383_lower_valid data383_upper_valid data383_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin383 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

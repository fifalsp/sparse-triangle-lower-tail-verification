import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box384 : LogBox := ⟨![(8035/2048 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(17677/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data384 : S1TaylorBoxData := ⟨box384,![exp46,exp18,exp4],![exp50,exp22,exp10],![exp48,exp20,exp6]⟩
theorem data384_lower_valid : ∀ j, (data384.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data384_upper_valid : ∀ j, (data384.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data384_center_valid : ∀ j, (data384.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin384 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data384 25 := by decide +kernel
theorem positive384 {q : EdgeTriple} (hq : q ∈ box384.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data384 25
    data384_lower_valid data384_upper_valid data384_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin384 hq

def box385 : LogBox := ⟨![(17677/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(36961/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data385 : S1TaylorBoxData := ⟨box385,![exp50,exp10,exp0],![exp52,exp18,exp4],![exp51,exp14,exp2]⟩
theorem data385_lower_valid : ∀ j, (data385.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data385_upper_valid : ∀ j, (data385.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data385_center_valid : ∀ j, (data385.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp51_valid
  · exact exp14_valid
  · exact exp2_valid
theorem margin385 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data385 25 := by decide +kernel
theorem positive385 {q : EdgeTriple} (hq : q ∈ box385.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data385 25
    data385_lower_valid data385_upper_valid data385_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin385 hq

def box386 : LogBox := ⟨![(36961/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data386 : S1TaylorBoxData := ⟨box386,![exp52,exp10,exp0],![exp54,exp18,exp4],![exp53,exp14,exp2]⟩
theorem data386_lower_valid : ∀ j, (data386.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data386_upper_valid : ∀ j, (data386.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data386_center_valid : ∀ j, (data386.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp53_valid
  · exact exp14_valid
  · exact exp2_valid
theorem margin386 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data386 25 := by decide +kernel
theorem positive386 {q : EdgeTriple} (hq : q ∈ box386.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data386 25
    data386_lower_valid data386_upper_valid data386_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin386 hq

def box387 : LogBox := ⟨![(17677/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data387 : S1TaylorBoxData := ⟨box387,![exp50,exp10,exp4],![exp54,exp18,exp10],![exp52,exp14,exp6]⟩
theorem data387_lower_valid : ∀ j, (data387.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data387_upper_valid : ∀ j, (data387.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data387_center_valid : ∀ j, (data387.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin387 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data387 25 := by decide +kernel
theorem positive387 {q : EdgeTriple} (hq : q ∈ box387.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data387 25
    data387_lower_valid data387_upper_valid data387_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin387 hq

def box388 : LogBox := ⟨![(17677/4096 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data388 : S1TaylorBoxData := ⟨box388,![exp50,exp18,exp0],![exp54,exp22,exp4],![exp52,exp20,exp2]⟩
theorem data388_lower_valid : ∀ j, (data388.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data388_upper_valid : ∀ j, (data388.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data388_center_valid : ∀ j, (data388.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin388 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data388 25 := by decide +kernel
theorem positive388 {q : EdgeTriple} (hq : q ∈ box388.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data388 25
    data388_lower_valid data388_upper_valid data388_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin388 hq

def box389 : LogBox := ⟨![(17677/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data389 : S1TaylorBoxData := ⟨box389,![exp50,exp18,exp4],![exp54,exp22,exp10],![exp52,exp20,exp6]⟩
theorem data389_lower_valid : ∀ j, (data389.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data389_upper_valid : ∀ j, (data389.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data389_center_valid : ∀ j, (data389.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin389 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data389 25 := by decide +kernel
theorem positive389 {q : EdgeTriple} (hq : q ∈ box389.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data389 25
    data389_lower_valid data389_upper_valid data389_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin389 hq

def box390 : LogBox := ⟨![(8035/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data390 : S1TaylorBoxData := ⟨box390,![exp46,exp10,exp10],![exp50,exp18,exp18],![exp48,exp14,exp14]⟩
theorem data390_lower_valid : ∀ j, (data390.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data390_upper_valid : ∀ j, (data390.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data390_center_valid : ∀ j, (data390.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin390 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data390 25 := by decide +kernel
theorem positive390 {q : EdgeTriple} (hq : q ∈ box390.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data390 25
    data390_lower_valid data390_upper_valid data390_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin390 hq

def box391 : LogBox := ⟨![(8035/2048 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(17677/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data391 : S1TaylorBoxData := ⟨box391,![exp46,exp18,exp10],![exp50,exp22,exp18],![exp48,exp20,exp14]⟩
theorem data391_lower_valid : ∀ j, (data391.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data391_upper_valid : ∀ j, (data391.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data391_center_valid : ∀ j, (data391.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin391 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data391 25 := by decide +kernel
theorem positive391 {q : EdgeTriple} (hq : q ∈ box391.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data391 25
    data391_lower_valid data391_upper_valid data391_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin391 hq

def box392 : LogBox := ⟨![(8035/2048 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(17677/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data392 : S1TaylorBoxData := ⟨box392,![exp46,exp18,exp18],![exp50,exp22,exp22],![exp48,exp20,exp20]⟩
theorem data392_lower_valid : ∀ j, (data392.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data392_upper_valid : ∀ j, (data392.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data392_center_valid : ∀ j, (data392.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin392 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data392 25 := by decide +kernel
theorem positive392 {q : EdgeTriple} (hq : q ∈ box392.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data392 25
    data392_lower_valid data392_upper_valid data392_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin392 hq

def box393 : LogBox := ⟨![(17677/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data393 : S1TaylorBoxData := ⟨box393,![exp50,exp10,exp10],![exp54,exp18,exp18],![exp52,exp14,exp14]⟩
theorem data393_lower_valid : ∀ j, (data393.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data393_upper_valid : ∀ j, (data393.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data393_center_valid : ∀ j, (data393.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin393 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data393 25 := by decide +kernel
theorem positive393 {q : EdgeTriple} (hq : q ∈ box393.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data393 25
    data393_lower_valid data393_upper_valid data393_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin393 hq

def box394 : LogBox := ⟨![(17677/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(4821/1024 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data394 : S1TaylorBoxData := ⟨box394,![exp50,exp18,exp10],![exp54,exp22,exp18],![exp52,exp20,exp14]⟩
theorem data394_lower_valid : ∀ j, (data394.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data394_upper_valid : ∀ j, (data394.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data394_center_valid : ∀ j, (data394.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin394 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data394 25 := by decide +kernel
theorem positive394 {q : EdgeTriple} (hq : q ∈ box394.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data394 25
    data394_lower_valid data394_upper_valid data394_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin394 hq

def box395 : LogBox := ⟨![(17677/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(4821/1024 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data395 : S1TaylorBoxData := ⟨box395,![exp50,exp18,exp18],![exp54,exp22,exp22],![exp52,exp20,exp20]⟩
theorem data395_lower_valid : ∀ j, (data395.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data395_upper_valid : ∀ j, (data395.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data395_center_valid : ∀ j, (data395.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin395 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data395 25 := by decide +kernel
theorem positive395 {q : EdgeTriple} (hq : q ∈ box395.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data395 25
    data395_lower_valid data395_upper_valid data395_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin395 hq

def box396 : LogBox := ⟨![(1607/512 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data396 : S1TaylorBoxData := ⟨box396,![exp38,exp22,exp0],![exp42,exp26,exp4],![exp40,exp24,exp2]⟩
theorem data396_lower_valid : ∀ j, (data396.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data396_upper_valid : ∀ j, (data396.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data396_center_valid : ∀ j, (data396.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin396 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data396 25 := by decide +kernel
theorem positive396 {q : EdgeTriple} (hq : q ∈ box396.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data396 25
    data396_lower_valid data396_upper_valid data396_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin396 hq

def box397 : LogBox := ⟨![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data397 : S1TaylorBoxData := ⟨box397,![exp38,exp22,exp4],![exp42,exp26,exp10],![exp40,exp24,exp6]⟩
theorem data397_lower_valid : ∀ j, (data397.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data397_upper_valid : ∀ j, (data397.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data397_center_valid : ∀ j, (data397.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin397 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data397 25 := by decide +kernel
theorem positive397 {q : EdgeTriple} (hq : q ∈ box397.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data397 25
    data397_lower_valid data397_upper_valid data397_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin397 hq

def box398 : LogBox := ⟨![(1607/512 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data398 : S1TaylorBoxData := ⟨box398,![exp38,exp26,exp0],![exp42,exp30,exp4],![exp40,exp28,exp2]⟩
theorem data398_lower_valid : ∀ j, (data398.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data398_upper_valid : ∀ j, (data398.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data398_center_valid : ∀ j, (data398.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin398 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data398 25 := by decide +kernel
theorem positive398 {q : EdgeTriple} (hq : q ∈ box398.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data398 25
    data398_lower_valid data398_upper_valid data398_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin398 hq

def box399 : LogBox := ⟨![(1607/512 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data399 : S1TaylorBoxData := ⟨box399,![exp38,exp26,exp4],![exp42,exp30,exp10],![exp40,exp28,exp6]⟩
theorem data399_lower_valid : ∀ j, (data399.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data399_upper_valid : ∀ j, (data399.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data399_center_valid : ∀ j, (data399.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin399 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data399 25 := by decide +kernel
theorem positive399 {q : EdgeTriple} (hq : q ∈ box399.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data399 25
    data399_lower_valid data399_upper_valid data399_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin399 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

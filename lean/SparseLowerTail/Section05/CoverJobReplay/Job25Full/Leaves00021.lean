import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box336 : LogBox := ⟨![(30533/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data336 : S1TaylorBoxData := ⟨box336,![exp44,exp6,exp0],![exp46,exp10,exp4],![exp45,exp8,exp2]⟩
theorem data336_lower_valid : ∀ j, (data336.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data336_upper_valid : ∀ j, (data336.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data336_center_valid : ∀ j, (data336.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp45_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin336 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data336 25 := by decide +kernel
theorem positive336 {q : EdgeTriple} (hq : q ∈ box336.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data336 25
    data336_lower_valid data336_upper_valid data336_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin336 hq

def box337 : LogBox := ⟨![(14463/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(30533/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data337 : S1TaylorBoxData := ⟨box337,![exp42,exp4,exp4],![exp44,exp10,exp10],![exp43,exp6,exp6]⟩
theorem data337_lower_valid : ∀ j, (data337.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data337_upper_valid : ∀ j, (data337.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data337_center_valid : ∀ j, (data337.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp43_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin337 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data337 25 := by decide +kernel
theorem positive337 {q : EdgeTriple} (hq : q ∈ box337.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data337 25
    data337_lower_valid data337_upper_valid data337_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin337 hq

def box338 : LogBox := ⟨![(30533/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data338 : S1TaylorBoxData := ⟨box338,![exp44,exp4,exp4],![exp46,exp10,exp10],![exp45,exp6,exp6]⟩
theorem data338_lower_valid : ∀ j, (data338.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data338_upper_valid : ∀ j, (data338.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data338_center_valid : ∀ j, (data338.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp45_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin338 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data338 25 := by decide +kernel
theorem positive338 {q : EdgeTriple} (hq : q ∈ box338.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data338 25
    data338_lower_valid data338_upper_valid data338_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin338 hq

def box339 : LogBox := ⟨![(1607/512 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(27319/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data339 : S1TaylorBoxData := ⟨box339,![exp38,exp10,exp0],![exp40,exp14,exp4],![exp39,exp12,exp2]⟩
theorem data339_lower_valid : ∀ j, (data339.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data339_upper_valid : ∀ j, (data339.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data339_center_valid : ∀ j, (data339.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin339 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data339 25 := by decide +kernel
theorem positive339 {q : EdgeTriple} (hq : q ∈ box339.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data339 25
    data339_lower_valid data339_upper_valid data339_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin339 hq

def box340 : LogBox := ⟨![(1607/512 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(27319/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data340 : S1TaylorBoxData := ⟨box340,![exp38,exp14,exp0],![exp40,exp18,exp4],![exp39,exp16,exp2]⟩
theorem data340_lower_valid : ∀ j, (data340.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data340_upper_valid : ∀ j, (data340.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data340_center_valid : ∀ j, (data340.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin340 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data340 25 := by decide +kernel
theorem positive340 {q : EdgeTriple} (hq : q ∈ box340.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data340 25
    data340_lower_valid data340_upper_valid data340_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin340 hq

def box341 : LogBox := ⟨![(27319/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data341 : S1TaylorBoxData := ⟨box341,![exp40,exp10,exp0],![exp42,exp14,exp4],![exp41,exp12,exp2]⟩
theorem data341_lower_valid : ∀ j, (data341.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data341_upper_valid : ∀ j, (data341.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data341_center_valid : ∀ j, (data341.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin341 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data341 25 := by decide +kernel
theorem positive341 {q : EdgeTriple} (hq : q ∈ box341.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data341 25
    data341_lower_valid data341_upper_valid data341_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin341 hq

def box342 : LogBox := ⟨![(27319/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data342 : S1TaylorBoxData := ⟨box342,![exp40,exp14,exp0],![exp42,exp18,exp4],![exp41,exp16,exp2]⟩
theorem data342_lower_valid : ∀ j, (data342.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data342_upper_valid : ∀ j, (data342.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data342_center_valid : ∀ j, (data342.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin342 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data342 25 := by decide +kernel
theorem positive342 {q : EdgeTriple} (hq : q ∈ box342.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data342 25
    data342_lower_valid data342_upper_valid data342_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin342 hq

def box343 : LogBox := ⟨![(1607/512 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(27319/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data343 : S1TaylorBoxData := ⟨box343,![exp38,exp10,exp4],![exp40,exp18,exp10],![exp39,exp14,exp6]⟩
theorem data343_lower_valid : ∀ j, (data343.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data343_upper_valid : ∀ j, (data343.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data343_center_valid : ∀ j, (data343.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin343 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data343 25 := by decide +kernel
theorem positive343 {q : EdgeTriple} (hq : q ∈ box343.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data343 25
    data343_lower_valid data343_upper_valid data343_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin343 hq

def box344 : LogBox := ⟨![(27319/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data344 : S1TaylorBoxData := ⟨box344,![exp40,exp10,exp4],![exp42,exp18,exp10],![exp41,exp14,exp6]⟩
theorem data344_lower_valid : ∀ j, (data344.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data344_upper_valid : ∀ j, (data344.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data344_center_valid : ∀ j, (data344.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin344 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data344 25 := by decide +kernel
theorem positive344 {q : EdgeTriple} (hq : q ∈ box344.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data344 25
    data344_lower_valid data344_upper_valid data344_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin344 hq

def box345 : LogBox := ⟨![(1607/512 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data345 : S1TaylorBoxData := ⟨box345,![exp38,exp18,exp0],![exp42,exp22,exp4],![exp40,exp20,exp2]⟩
theorem data345_lower_valid : ∀ j, (data345.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data345_upper_valid : ∀ j, (data345.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data345_center_valid : ∀ j, (data345.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin345 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data345 25 := by decide +kernel
theorem positive345 {q : EdgeTriple} (hq : q ∈ box345.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data345 25
    data345_lower_valid data345_upper_valid data345_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin345 hq

def box346 : LogBox := ⟨![(1607/512 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data346 : S1TaylorBoxData := ⟨box346,![exp38,exp18,exp4],![exp42,exp22,exp10],![exp40,exp20,exp6]⟩
theorem data346_lower_valid : ∀ j, (data346.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data346_upper_valid : ∀ j, (data346.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data346_center_valid : ∀ j, (data346.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin346 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data346 25 := by decide +kernel
theorem positive346 {q : EdgeTriple} (hq : q ∈ box346.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data346 25
    data346_lower_valid data346_upper_valid data346_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin346 hq

def box347 : LogBox := ⟨![(14463/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(30533/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data347 : S1TaylorBoxData := ⟨box347,![exp42,exp10,exp0],![exp44,exp14,exp4],![exp43,exp12,exp2]⟩
theorem data347_lower_valid : ∀ j, (data347.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data347_upper_valid : ∀ j, (data347.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data347_center_valid : ∀ j, (data347.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp43_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin347 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data347 25 := by decide +kernel
theorem positive347 {q : EdgeTriple} (hq : q ∈ box347.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data347 25
    data347_lower_valid data347_upper_valid data347_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin347 hq

def box348 : LogBox := ⟨![(14463/4096 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(30533/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data348 : S1TaylorBoxData := ⟨box348,![exp42,exp14,exp0],![exp44,exp18,exp4],![exp43,exp16,exp2]⟩
theorem data348_lower_valid : ∀ j, (data348.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data348_upper_valid : ∀ j, (data348.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data348_center_valid : ∀ j, (data348.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp43_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin348 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data348 25 := by decide +kernel
theorem positive348 {q : EdgeTriple} (hq : q ∈ box348.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data348 25
    data348_lower_valid data348_upper_valid data348_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin348 hq

def box349 : LogBox := ⟨![(30533/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data349 : S1TaylorBoxData := ⟨box349,![exp44,exp10,exp0],![exp46,exp14,exp4],![exp45,exp12,exp2]⟩
theorem data349_lower_valid : ∀ j, (data349.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data349_upper_valid : ∀ j, (data349.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data349_center_valid : ∀ j, (data349.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp45_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin349 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data349 25 := by decide +kernel
theorem positive349 {q : EdgeTriple} (hq : q ∈ box349.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data349 25
    data349_lower_valid data349_upper_valid data349_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin349 hq

def box350 : LogBox := ⟨![(30533/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data350 : S1TaylorBoxData := ⟨box350,![exp44,exp14,exp0],![exp46,exp18,exp4],![exp45,exp16,exp2]⟩
theorem data350_lower_valid : ∀ j, (data350.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data350_upper_valid : ∀ j, (data350.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data350_center_valid : ∀ j, (data350.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp45_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin350 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data350 25 := by decide +kernel
theorem positive350 {q : EdgeTriple} (hq : q ∈ box350.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data350 25
    data350_lower_valid data350_upper_valid data350_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin350 hq

def box351 : LogBox := ⟨![(14463/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data351 : S1TaylorBoxData := ⟨box351,![exp42,exp10,exp4],![exp46,exp18,exp10],![exp44,exp14,exp6]⟩
theorem data351_lower_valid : ∀ j, (data351.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data351_upper_valid : ∀ j, (data351.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data351_center_valid : ∀ j, (data351.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp14_valid
  · exact exp6_valid
theorem margin351 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data351 25 := by decide +kernel
theorem positive351 {q : EdgeTriple} (hq : q ∈ box351.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data351 25
    data351_lower_valid data351_upper_valid data351_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin351 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

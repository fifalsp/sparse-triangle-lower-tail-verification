import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box320 : LogBox := ⟨![(1607/512 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(27319/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data320 : S1TaylorBoxData := ⟨box320,![exp38,exp4,exp0],![exp40,exp6,exp2],![exp39,exp5,exp1]⟩
theorem data320_lower_valid : ∀ j, (data320.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data320_upper_valid : ∀ j, (data320.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data320_center_valid : ∀ j, (data320.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin320 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data320 25 := by decide +kernel
theorem positive320 {q : EdgeTriple} (hq : q ∈ box320.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data320 25
    data320_lower_valid data320_upper_valid data320_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin320 hq

def box321 : LogBox := ⟨![(1607/512 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(27319/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data321 : S1TaylorBoxData := ⟨box321,![exp38,exp4,exp2],![exp40,exp6,exp4],![exp39,exp5,exp3]⟩
theorem data321_lower_valid : ∀ j, (data321.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data321_upper_valid : ∀ j, (data321.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data321_center_valid : ∀ j, (data321.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin321 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data321 25 := by decide +kernel
theorem positive321 {q : EdgeTriple} (hq : q ∈ box321.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data321 25
    data321_lower_valid data321_upper_valid data321_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin321 hq

def box322 : LogBox := ⟨![(1607/512 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(27319/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data322 : S1TaylorBoxData := ⟨box322,![exp38,exp6,exp0],![exp40,exp10,exp4],![exp39,exp8,exp2]⟩
theorem data322_lower_valid : ∀ j, (data322.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data322_upper_valid : ∀ j, (data322.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data322_center_valid : ∀ j, (data322.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin322 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data322 25 := by decide +kernel
theorem positive322 {q : EdgeTriple} (hq : q ∈ box322.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data322 25
    data322_lower_valid data322_upper_valid data322_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin322 hq

def box323 : LogBox := ⟨![(27319/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data323 : S1TaylorBoxData := ⟨box323,![exp40,exp4,exp0],![exp42,exp6,exp2],![exp41,exp5,exp1]⟩
theorem data323_lower_valid : ∀ j, (data323.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data323_upper_valid : ∀ j, (data323.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data323_center_valid : ∀ j, (data323.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin323 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data323 25 := by decide +kernel
theorem positive323 {q : EdgeTriple} (hq : q ∈ box323.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data323 25
    data323_lower_valid data323_upper_valid data323_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin323 hq

def box324 : LogBox := ⟨![(27319/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(14463/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data324 : S1TaylorBoxData := ⟨box324,![exp40,exp4,exp2],![exp42,exp6,exp4],![exp41,exp5,exp3]⟩
theorem data324_lower_valid : ∀ j, (data324.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data324_upper_valid : ∀ j, (data324.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data324_center_valid : ∀ j, (data324.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin324 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data324 25 := by decide +kernel
theorem positive324 {q : EdgeTriple} (hq : q ∈ box324.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data324 25
    data324_lower_valid data324_upper_valid data324_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin324 hq

def box325 : LogBox := ⟨![(27319/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data325 : S1TaylorBoxData := ⟨box325,![exp40,exp6,exp0],![exp42,exp10,exp4],![exp41,exp8,exp2]⟩
theorem data325_lower_valid : ∀ j, (data325.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data325_upper_valid : ∀ j, (data325.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data325_center_valid : ∀ j, (data325.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin325 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data325 25 := by decide +kernel
theorem positive325 {q : EdgeTriple} (hq : q ∈ box325.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data325 25
    data325_lower_valid data325_upper_valid data325_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin325 hq

def box326 : LogBox := ⟨![(1607/512 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(27319/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data326 : S1TaylorBoxData := ⟨box326,![exp38,exp4,exp4],![exp40,exp6,exp6],![exp39,exp5,exp5]⟩
theorem data326_lower_valid : ∀ j, (data326.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data326_upper_valid : ∀ j, (data326.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data326_center_valid : ∀ j, (data326.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin326 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data326 25 := by decide +kernel
theorem positive326 {q : EdgeTriple} (hq : q ∈ box326.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data326 25
    data326_lower_valid data326_upper_valid data326_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin326 hq

def box327 : LogBox := ⟨![(1607/512 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(27319/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data327 : S1TaylorBoxData := ⟨box327,![exp38,exp6,exp4],![exp40,exp10,exp10],![exp39,exp8,exp6]⟩
theorem data327_lower_valid : ∀ j, (data327.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data327_upper_valid : ∀ j, (data327.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data327_center_valid : ∀ j, (data327.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp39_valid
  · exact exp8_valid
  · exact exp6_valid
theorem margin327 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data327 25 := by decide +kernel
theorem positive327 {q : EdgeTriple} (hq : q ∈ box327.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data327 25
    data327_lower_valid data327_upper_valid data327_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin327 hq

def box328 : LogBox := ⟨![(27319/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data328 : S1TaylorBoxData := ⟨box328,![exp40,exp4,exp4],![exp42,exp10,exp10],![exp41,exp6,exp6]⟩
theorem data328_lower_valid : ∀ j, (data328.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data328_upper_valid : ∀ j, (data328.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data328_center_valid : ∀ j, (data328.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp41_valid
  · exact exp6_valid
  · exact exp6_valid
theorem margin328 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data328 25 := by decide +kernel
theorem positive328 {q : EdgeTriple} (hq : q ∈ box328.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data328 25
    data328_lower_valid data328_upper_valid data328_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin328 hq

def box329 : LogBox := ⟨![(14463/4096 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(30533/8192 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data329 : S1TaylorBoxData := ⟨box329,![exp42,exp0,exp0],![exp44,exp2,exp2],![exp43,exp1,exp1]⟩
theorem data329_lower_valid : ∀ j, (data329.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data329_upper_valid : ∀ j, (data329.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data329_center_valid : ∀ j, (data329.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp43_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin329 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data329 25 := by decide +kernel
theorem positive329 {q : EdgeTriple} (hq : q ∈ box329.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data329 25
    data329_lower_valid data329_upper_valid data329_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin329 hq

def box330 : LogBox := ⟨![(14463/4096 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(30533/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data330 : S1TaylorBoxData := ⟨box330,![exp42,exp2,exp0],![exp44,exp4,exp4],![exp43,exp3,exp2]⟩
theorem data330_lower_valid : ∀ j, (data330.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data330_upper_valid : ∀ j, (data330.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data330_center_valid : ∀ j, (data330.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp43_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin330 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data330 25 := by decide +kernel
theorem positive330 {q : EdgeTriple} (hq : q ∈ box330.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data330 25
    data330_lower_valid data330_upper_valid data330_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin330 hq

def box331 : LogBox := ⟨![(30533/8192 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data331 : S1TaylorBoxData := ⟨box331,![exp44,exp0,exp0],![exp46,exp2,exp2],![exp45,exp1,exp1]⟩
theorem data331_lower_valid : ∀ j, (data331.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data331_upper_valid : ∀ j, (data331.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp2_valid
  · exact exp2_valid
theorem data331_center_valid : ∀ j, (data331.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp45_valid
  · exact exp1_valid
  · exact exp1_valid
theorem margin331 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data331 25 := by decide +kernel
theorem positive331 {q : EdgeTriple} (hq : q ∈ box331.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data331 25
    data331_lower_valid data331_upper_valid data331_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin331 hq

def box332 : LogBox := ⟨![(30533/8192 : ℚ),(1607/8192 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data332 : S1TaylorBoxData := ⟨box332,![exp44,exp2,exp0],![exp46,exp4,exp4],![exp45,exp3,exp2]⟩
theorem data332_lower_valid : ∀ j, (data332.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp2_valid
  · exact exp0_valid
theorem data332_upper_valid : ∀ j, (data332.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data332_center_valid : ∀ j, (data332.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp45_valid
  · exact exp3_valid
  · exact exp2_valid
theorem margin332 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data332 25 := by decide +kernel
theorem positive332 {q : EdgeTriple} (hq : q ∈ box332.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data332 25
    data332_lower_valid data332_upper_valid data332_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin332 hq

def box333 : LogBox := ⟨![(14463/4096 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(30533/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data333 : S1TaylorBoxData := ⟨box333,![exp42,exp4,exp0],![exp44,exp6,exp4],![exp43,exp5,exp2]⟩
theorem data333_lower_valid : ∀ j, (data333.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data333_upper_valid : ∀ j, (data333.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data333_center_valid : ∀ j, (data333.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp43_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin333 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data333 25 := by decide +kernel
theorem positive333 {q : EdgeTriple} (hq : q ∈ box333.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data333 25
    data333_lower_valid data333_upper_valid data333_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin333 hq

def box334 : LogBox := ⟨![(14463/4096 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(30533/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data334 : S1TaylorBoxData := ⟨box334,![exp42,exp6,exp0],![exp44,exp10,exp4],![exp43,exp8,exp2]⟩
theorem data334_lower_valid : ∀ j, (data334.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data334_upper_valid : ∀ j, (data334.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data334_center_valid : ∀ j, (data334.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp43_valid
  · exact exp8_valid
  · exact exp2_valid
theorem margin334 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data334 25 := by decide +kernel
theorem positive334 {q : EdgeTriple} (hq : q ∈ box334.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data334 25
    data334_lower_valid data334_upper_valid data334_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin334 hq

def box335 : LogBox := ⟨![(30533/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data335 : S1TaylorBoxData := ⟨box335,![exp44,exp4,exp0],![exp46,exp6,exp4],![exp45,exp5,exp2]⟩
theorem data335_lower_valid : ∀ j, (data335.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data335_upper_valid : ∀ j, (data335.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data335_center_valid : ∀ j, (data335.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp45_valid
  · exact exp5_valid
  · exact exp2_valid
theorem margin335 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data335 25 := by decide +kernel
theorem positive335 {q : EdgeTriple} (hq : q ∈ box335.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data335 25
    data335_lower_valid data335_upper_valid data335_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin335 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

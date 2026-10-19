import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box240 : LogBox := ⟨![(4821/2048 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(20891/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data240 : S1TaylorBoxData := ⟨box240,![exp30,exp14,exp4],![exp32,exp18,exp10],![exp31,exp16,exp6]⟩
theorem data240_lower_valid : ∀ j, (data240.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data240_upper_valid : ∀ j, (data240.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data240_center_valid : ∀ j, (data240.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp31_valid
  · exact exp16_valid
  · exact exp6_valid
theorem margin240 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data240 25 := by decide +kernel
theorem positive240 {q : EdgeTriple} (hq : q ∈ box240.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data240 25
    data240_lower_valid data240_upper_valid data240_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin240 hq

def box241 : LogBox := ⟨![(20891/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data241 : S1TaylorBoxData := ⟨box241,![exp32,exp10,exp4],![exp34,exp14,exp10],![exp33,exp12,exp6]⟩
theorem data241_lower_valid : ∀ j, (data241.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data241_upper_valid : ∀ j, (data241.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data241_center_valid : ∀ j, (data241.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp12_valid
  · exact exp6_valid
theorem margin241 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data241 25 := by decide +kernel
theorem positive241 {q : EdgeTriple} (hq : q ∈ box241.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data241 25
    data241_lower_valid data241_upper_valid data241_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin241 hq

def box242 : LogBox := ⟨![(20891/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data242 : S1TaylorBoxData := ⟨box242,![exp32,exp14,exp4],![exp34,exp18,exp10],![exp33,exp16,exp6]⟩
theorem data242_lower_valid : ∀ j, (data242.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data242_upper_valid : ∀ j, (data242.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data242_center_valid : ∀ j, (data242.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp33_valid
  · exact exp16_valid
  · exact exp6_valid
theorem margin242 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data242 25 := by decide +kernel
theorem positive242 {q : EdgeTriple} (hq : q ∈ box242.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data242 25
    data242_lower_valid data242_upper_valid data242_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin242 hq

def box243 : LogBox := ⟨![(4821/2048 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(11249/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data243 : S1TaylorBoxData := ⟨box243,![exp30,exp18,exp0],![exp34,exp22,exp4],![exp32,exp20,exp2]⟩
theorem data243_lower_valid : ∀ j, (data243.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data243_upper_valid : ∀ j, (data243.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data243_center_valid : ∀ j, (data243.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin243 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data243 25 := by decide +kernel
theorem positive243 {q : EdgeTriple} (hq : q ∈ box243.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data243 25
    data243_lower_valid data243_upper_valid data243_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin243 hq

def box244 : LogBox := ⟨![(4821/2048 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(11249/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data244 : S1TaylorBoxData := ⟨box244,![exp30,exp18,exp4],![exp34,exp22,exp10],![exp32,exp20,exp6]⟩
theorem data244_lower_valid : ∀ j, (data244.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data244_upper_valid : ∀ j, (data244.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data244_center_valid : ∀ j, (data244.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin244 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data244 25 := by decide +kernel
theorem positive244 {q : EdgeTriple} (hq : q ∈ box244.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data244 25
    data244_lower_valid data244_upper_valid data244_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin244 hq

def box245 : LogBox := ⟨![(11249/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(24105/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data245 : S1TaylorBoxData := ⟨box245,![exp34,exp10,exp0],![exp36,exp14,exp4],![exp35,exp12,exp2]⟩
theorem data245_lower_valid : ∀ j, (data245.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data245_upper_valid : ∀ j, (data245.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data245_center_valid : ∀ j, (data245.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin245 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data245 25 := by decide +kernel
theorem positive245 {q : EdgeTriple} (hq : q ∈ box245.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data245 25
    data245_lower_valid data245_upper_valid data245_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin245 hq

def box246 : LogBox := ⟨![(11249/4096 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(24105/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data246 : S1TaylorBoxData := ⟨box246,![exp34,exp14,exp0],![exp36,exp18,exp4],![exp35,exp16,exp2]⟩
theorem data246_lower_valid : ∀ j, (data246.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data246_upper_valid : ∀ j, (data246.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data246_center_valid : ∀ j, (data246.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin246 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data246 25 := by decide +kernel
theorem positive246 {q : EdgeTriple} (hq : q ∈ box246.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data246 25
    data246_lower_valid data246_upper_valid data246_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin246 hq

def box247 : LogBox := ⟨![(24105/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data247 : S1TaylorBoxData := ⟨box247,![exp36,exp10,exp0],![exp38,exp14,exp4],![exp37,exp12,exp2]⟩
theorem data247_lower_valid : ∀ j, (data247.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data247_upper_valid : ∀ j, (data247.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data247_center_valid : ∀ j, (data247.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin247 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data247 25 := by decide +kernel
theorem positive247 {q : EdgeTriple} (hq : q ∈ box247.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data247 25
    data247_lower_valid data247_upper_valid data247_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin247 hq

def box248 : LogBox := ⟨![(24105/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data248 : S1TaylorBoxData := ⟨box248,![exp36,exp14,exp0],![exp38,exp18,exp4],![exp37,exp16,exp2]⟩
theorem data248_lower_valid : ∀ j, (data248.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data248_upper_valid : ∀ j, (data248.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data248_center_valid : ∀ j, (data248.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin248 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data248 25 := by decide +kernel
theorem positive248 {q : EdgeTriple} (hq : q ∈ box248.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data248 25
    data248_lower_valid data248_upper_valid data248_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin248 hq

def box249 : LogBox := ⟨![(11249/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(24105/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data249 : S1TaylorBoxData := ⟨box249,![exp34,exp10,exp4],![exp36,exp14,exp10],![exp35,exp12,exp6]⟩
theorem data249_lower_valid : ∀ j, (data249.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data249_upper_valid : ∀ j, (data249.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data249_center_valid : ∀ j, (data249.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp12_valid
  · exact exp6_valid
theorem margin249 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data249 25 := by decide +kernel
theorem positive249 {q : EdgeTriple} (hq : q ∈ box249.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data249 25
    data249_lower_valid data249_upper_valid data249_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin249 hq

def box250 : LogBox := ⟨![(11249/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(24105/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data250 : S1TaylorBoxData := ⟨box250,![exp34,exp14,exp4],![exp36,exp18,exp10],![exp35,exp16,exp6]⟩
theorem data250_lower_valid : ∀ j, (data250.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data250_upper_valid : ∀ j, (data250.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data250_center_valid : ∀ j, (data250.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp35_valid
  · exact exp16_valid
  · exact exp6_valid
theorem margin250 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data250 25 := by decide +kernel
theorem positive250 {q : EdgeTriple} (hq : q ∈ box250.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data250 25
    data250_lower_valid data250_upper_valid data250_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin250 hq

def box251 : LogBox := ⟨![(24105/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data251 : S1TaylorBoxData := ⟨box251,![exp36,exp10,exp4],![exp38,exp14,exp10],![exp37,exp12,exp6]⟩
theorem data251_lower_valid : ∀ j, (data251.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data251_upper_valid : ∀ j, (data251.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data251_center_valid : ∀ j, (data251.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp12_valid
  · exact exp6_valid
theorem margin251 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data251 25 := by decide +kernel
theorem positive251 {q : EdgeTriple} (hq : q ∈ box251.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data251 25
    data251_lower_valid data251_upper_valid data251_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin251 hq

def box252 : LogBox := ⟨![(24105/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data252 : S1TaylorBoxData := ⟨box252,![exp36,exp14,exp4],![exp38,exp18,exp10],![exp37,exp16,exp6]⟩
theorem data252_lower_valid : ∀ j, (data252.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data252_upper_valid : ∀ j, (data252.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data252_center_valid : ∀ j, (data252.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp37_valid
  · exact exp16_valid
  · exact exp6_valid
theorem margin252 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data252 25 := by decide +kernel
theorem positive252 {q : EdgeTriple} (hq : q ∈ box252.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data252 25
    data252_lower_valid data252_upper_valid data252_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin252 hq

def box253 : LogBox := ⟨![(11249/4096 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data253 : S1TaylorBoxData := ⟨box253,![exp34,exp18,exp0],![exp38,exp22,exp4],![exp36,exp20,exp2]⟩
theorem data253_lower_valid : ∀ j, (data253.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data253_upper_valid : ∀ j, (data253.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data253_center_valid : ∀ j, (data253.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin253 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data253 25 := by decide +kernel
theorem positive253 {q : EdgeTriple} (hq : q ∈ box253.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data253 25
    data253_lower_valid data253_upper_valid data253_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin253 hq

def box254 : LogBox := ⟨![(11249/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data254 : S1TaylorBoxData := ⟨box254,![exp34,exp18,exp4],![exp38,exp22,exp10],![exp36,exp20,exp6]⟩
theorem data254_lower_valid : ∀ j, (data254.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data254_upper_valid : ∀ j, (data254.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data254_center_valid : ∀ j, (data254.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin254 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data254 25 := by decide +kernel
theorem positive254 {q : EdgeTriple} (hq : q ∈ box254.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data254 25
    data254_lower_valid data254_upper_valid data254_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin254 hq

def box255 : LogBox := ⟨![(4821/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(11249/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data255 : S1TaylorBoxData := ⟨box255,![exp30,exp10,exp10],![exp34,exp18,exp18],![exp32,exp14,exp14]⟩
theorem data255_lower_valid : ∀ j, (data255.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data255_upper_valid : ∀ j, (data255.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data255_center_valid : ∀ j, (data255.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin255 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data255 25 := by decide +kernel
theorem positive255 {q : EdgeTriple} (hq : q ∈ box255.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data255 25
    data255_lower_valid data255_upper_valid data255_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin255 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

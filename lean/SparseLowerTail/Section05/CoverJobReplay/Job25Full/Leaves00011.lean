import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box176 : LogBox := ⟨![(8035/4096 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(17677/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data176 : S1TaylorBoxData := ⟨box176,![exp26,exp14,exp0],![exp28,exp18,exp4],![exp27,exp16,exp2]⟩
theorem data176_lower_valid : ∀ j, (data176.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data176_upper_valid : ∀ j, (data176.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data176_center_valid : ∀ j, (data176.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin176 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data176 25 := by decide +kernel
theorem positive176 {q : EdgeTriple} (hq : q ∈ box176.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data176 25
    data176_lower_valid data176_upper_valid data176_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin176 hq

def box177 : LogBox := ⟨![(17677/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data177 : S1TaylorBoxData := ⟨box177,![exp28,exp10,exp0],![exp30,exp14,exp4],![exp29,exp12,exp2]⟩
theorem data177_lower_valid : ∀ j, (data177.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data177_upper_valid : ∀ j, (data177.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data177_center_valid : ∀ j, (data177.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin177 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data177 25 := by decide +kernel
theorem positive177 {q : EdgeTriple} (hq : q ∈ box177.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data177 25
    data177_lower_valid data177_upper_valid data177_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin177 hq

def box178 : LogBox := ⟨![(17677/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data178 : S1TaylorBoxData := ⟨box178,![exp28,exp14,exp0],![exp30,exp18,exp4],![exp29,exp16,exp2]⟩
theorem data178_lower_valid : ∀ j, (data178.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data178_upper_valid : ∀ j, (data178.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data178_center_valid : ∀ j, (data178.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin178 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data178 25 := by decide +kernel
theorem positive178 {q : EdgeTriple} (hq : q ∈ box178.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data178 25
    data178_lower_valid data178_upper_valid data178_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin178 hq

def box179 : LogBox := ⟨![(8035/4096 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(17677/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data179 : S1TaylorBoxData := ⟨box179,![exp26,exp10,exp4],![exp28,exp14,exp10],![exp27,exp12,exp6]⟩
theorem data179_lower_valid : ∀ j, (data179.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data179_upper_valid : ∀ j, (data179.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data179_center_valid : ∀ j, (data179.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp12_valid
  · exact exp6_valid
theorem margin179 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data179 25 := by decide +kernel
theorem positive179 {q : EdgeTriple} (hq : q ∈ box179.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data179 25
    data179_lower_valid data179_upper_valid data179_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin179 hq

def box180 : LogBox := ⟨![(8035/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(17677/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data180 : S1TaylorBoxData := ⟨box180,![exp26,exp14,exp4],![exp28,exp18,exp10],![exp27,exp16,exp6]⟩
theorem data180_lower_valid : ∀ j, (data180.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data180_upper_valid : ∀ j, (data180.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data180_center_valid : ∀ j, (data180.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp16_valid
  · exact exp6_valid
theorem margin180 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data180 25 := by decide +kernel
theorem positive180 {q : EdgeTriple} (hq : q ∈ box180.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data180 25
    data180_lower_valid data180_upper_valid data180_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin180 hq

def box181 : LogBox := ⟨![(17677/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(4821/2048 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data181 : S1TaylorBoxData := ⟨box181,![exp28,exp10,exp4],![exp30,exp14,exp10],![exp29,exp12,exp6]⟩
theorem data181_lower_valid : ∀ j, (data181.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data181_upper_valid : ∀ j, (data181.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data181_center_valid : ∀ j, (data181.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp12_valid
  · exact exp6_valid
theorem margin181 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data181 25 := by decide +kernel
theorem positive181 {q : EdgeTriple} (hq : q ∈ box181.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data181 25
    data181_lower_valid data181_upper_valid data181_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin181 hq

def box182 : LogBox := ⟨![(17677/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(4821/2048 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data182 : S1TaylorBoxData := ⟨box182,![exp28,exp14,exp4],![exp30,exp18,exp10],![exp29,exp16,exp6]⟩
theorem data182_lower_valid : ∀ j, (data182.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data182_upper_valid : ∀ j, (data182.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data182_center_valid : ∀ j, (data182.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp16_valid
  · exact exp6_valid
theorem margin182 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data182 25 := by decide +kernel
theorem positive182 {q : EdgeTriple} (hq : q ∈ box182.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data182 25
    data182_lower_valid data182_upper_valid data182_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin182 hq

def box183 : LogBox := ⟨![(8035/4096 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(17677/8192 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data183 : S1TaylorBoxData := ⟨box183,![exp26,exp18,exp0],![exp28,exp22,exp4],![exp27,exp20,exp2]⟩
theorem data183_lower_valid : ∀ j, (data183.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data183_upper_valid : ∀ j, (data183.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data183_center_valid : ∀ j, (data183.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin183 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data183 25 := by decide +kernel
theorem positive183 {q : EdgeTriple} (hq : q ∈ box183.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data183 25
    data183_lower_valid data183_upper_valid data183_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin183 hq

def box184 : LogBox := ⟨![(17677/8192 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data184 : S1TaylorBoxData := ⟨box184,![exp28,exp18,exp0],![exp30,exp22,exp4],![exp29,exp20,exp2]⟩
theorem data184_lower_valid : ∀ j, (data184.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data184_upper_valid : ∀ j, (data184.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data184_center_valid : ∀ j, (data184.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp20_valid
  · exact exp2_valid
theorem margin184 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data184 25 := by decide +kernel
theorem positive184 {q : EdgeTriple} (hq : q ∈ box184.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data184 25
    data184_lower_valid data184_upper_valid data184_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin184 hq

def box185 : LogBox := ⟨![(8035/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(17677/8192 : ℚ),(11249/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data185 : S1TaylorBoxData := ⟨box185,![exp26,exp18,exp4],![exp28,exp20,exp10],![exp27,exp19,exp6]⟩
theorem data185_lower_valid : ∀ j, (data185.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data185_upper_valid : ∀ j, (data185.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp20_valid
  · exact exp10_valid
theorem data185_center_valid : ∀ j, (data185.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp19_valid
  · exact exp6_valid
theorem margin185 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data185 25 := by decide +kernel
theorem positive185 {q : EdgeTriple} (hq : q ∈ box185.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data185 25
    data185_lower_valid data185_upper_valid data185_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin185 hq

def box186 : LogBox := ⟨![(8035/4096 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)],![(17677/8192 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data186 : S1TaylorBoxData := ⟨box186,![exp26,exp20,exp4],![exp28,exp22,exp10],![exp27,exp21,exp6]⟩
theorem data186_lower_valid : ∀ j, (data186.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data186_upper_valid : ∀ j, (data186.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data186_center_valid : ∀ j, (data186.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp21_valid
  · exact exp6_valid
theorem margin186 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data186 25 := by decide +kernel
theorem positive186 {q : EdgeTriple} (hq : q ∈ box186.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data186 25
    data186_lower_valid data186_upper_valid data186_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin186 hq

def box187 : LogBox := ⟨![(17677/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(4821/2048 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data187 : S1TaylorBoxData := ⟨box187,![exp28,exp18,exp4],![exp30,exp22,exp10],![exp29,exp20,exp6]⟩
theorem data187_lower_valid : ∀ j, (data187.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data187_upper_valid : ∀ j, (data187.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data187_center_valid : ∀ j, (data187.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp20_valid
  · exact exp6_valid
theorem margin187 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data187 25 := by decide +kernel
theorem positive187 {q : EdgeTriple} (hq : q ∈ box187.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data187 25
    data187_lower_valid data187_upper_valid data187_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin187 hq

def box188 : LogBox := ⟨![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(14463/8192 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data188 : S1TaylorBoxData := ⟨box188,![exp22,exp10,exp10],![exp24,exp14,exp14],![exp23,exp12,exp12]⟩
theorem data188_lower_valid : ∀ j, (data188.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data188_upper_valid : ∀ j, (data188.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data188_center_valid : ∀ j, (data188.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp12_valid
  · exact exp12_valid
theorem margin188 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data188 25 := by decide +kernel
theorem positive188 {q : EdgeTriple} (hq : q ∈ box188.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data188 25
    data188_lower_valid data188_upper_valid data188_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin188 hq

def box189 : LogBox := ⟨![(1607/1024 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)],![(14463/8192 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data189 : S1TaylorBoxData := ⟨box189,![exp22,exp14,exp10],![exp24,exp18,exp18],![exp23,exp16,exp14]⟩
theorem data189_lower_valid : ∀ j, (data189.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data189_upper_valid : ∀ j, (data189.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data189_center_valid : ∀ j, (data189.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp16_valid
  · exact exp14_valid
theorem margin189 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data189 25 := by decide +kernel
theorem positive189 {q : EdgeTriple} (hq : q ∈ box189.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data189 25
    data189_lower_valid data189_upper_valid data189_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin189 hq

def box190 : LogBox := ⟨![(14463/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(8035/4096 : ℚ),(8035/8192 : ℚ),(8035/8192 : ℚ)]⟩
def data190 : S1TaylorBoxData := ⟨box190,![exp24,exp10,exp10],![exp26,exp14,exp14],![exp25,exp12,exp12]⟩
theorem data190_lower_valid : ∀ j, (data190.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data190_upper_valid : ∀ j, (data190.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp14_valid
theorem data190_center_valid : ∀ j, (data190.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp12_valid
  · exact exp12_valid
theorem margin190 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data190 25 := by decide +kernel
theorem positive190 {q : EdgeTriple} (hq : q ∈ box190.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data190 25
    data190_lower_valid data190_upper_valid data190_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin190 hq

def box191 : LogBox := ⟨![(14463/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)],![(8035/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data191 : S1TaylorBoxData := ⟨box191,![exp24,exp14,exp10],![exp26,exp18,exp18],![exp25,exp16,exp14]⟩
theorem data191_lower_valid : ∀ j, (data191.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data191_upper_valid : ∀ j, (data191.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data191_center_valid : ∀ j, (data191.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp16_valid
  · exact exp14_valid
theorem margin191 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data191 25 := by decide +kernel
theorem positive191 {q : EdgeTriple} (hq : q ∈ box191.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data191 25
    data191_lower_valid data191_upper_valid data191_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin191 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

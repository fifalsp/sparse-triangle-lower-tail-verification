import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box160 : LogBox := ⟨![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(14463/8192 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data160 : S1TaylorBoxData := ⟨box160,![exp22,exp10,exp4],![exp24,exp14,exp6],![exp23,exp12,exp5]⟩
theorem data160_lower_valid : ∀ j, (data160.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data160_upper_valid : ∀ j, (data160.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data160_center_valid : ∀ j, (data160.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp12_valid
  · exact exp5_valid
theorem margin160 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data160 25 := by decide +kernel
theorem positive160 {q : EdgeTriple} (hq : q ∈ box160.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data160 25
    data160_lower_valid data160_upper_valid data160_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin160 hq

def box161 : LogBox := ⟨![(1607/1024 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(14463/8192 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data161 : S1TaylorBoxData := ⟨box161,![exp22,exp10,exp6],![exp24,exp14,exp10],![exp23,exp12,exp8]⟩
theorem data161_lower_valid : ∀ j, (data161.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data161_upper_valid : ∀ j, (data161.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data161_center_valid : ∀ j, (data161.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp12_valid
  · exact exp8_valid
theorem margin161 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data161 25 := by decide +kernel
theorem positive161 {q : EdgeTriple} (hq : q ∈ box161.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data161 25
    data161_lower_valid data161_upper_valid data161_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin161 hq

def box162 : LogBox := ⟨![(1607/1024 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(14463/8192 : ℚ),(4821/4096 : ℚ),(4821/8192 : ℚ)]⟩
def data162 : S1TaylorBoxData := ⟨box162,![exp22,exp14,exp4],![exp24,exp18,exp6],![exp23,exp16,exp5]⟩
theorem data162_lower_valid : ∀ j, (data162.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data162_upper_valid : ∀ j, (data162.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp18_valid
  · exact exp6_valid
theorem data162_center_valid : ∀ j, (data162.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp16_valid
  · exact exp5_valid
theorem margin162 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data162 25 := by decide +kernel
theorem positive162 {q : EdgeTriple} (hq : q ∈ box162.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data162 25
    data162_lower_valid data162_upper_valid data162_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin162 hq

def box163 : LogBox := ⟨![(1607/1024 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)],![(14463/8192 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data163 : S1TaylorBoxData := ⟨box163,![exp22,exp14,exp6],![exp24,exp18,exp10],![exp23,exp16,exp8]⟩
theorem data163_lower_valid : ∀ j, (data163.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data163_upper_valid : ∀ j, (data163.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data163_center_valid : ∀ j, (data163.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp16_valid
  · exact exp8_valid
theorem margin163 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data163 25 := by decide +kernel
theorem positive163 {q : EdgeTriple} (hq : q ∈ box163.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data163 25
    data163_lower_valid data163_upper_valid data163_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin163 hq

def box164 : LogBox := ⟨![(14463/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)],![(8035/4096 : ℚ),(8035/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data164 : S1TaylorBoxData := ⟨box164,![exp24,exp10,exp4],![exp26,exp14,exp6],![exp25,exp12,exp5]⟩
theorem data164_lower_valid : ∀ j, (data164.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data164_upper_valid : ∀ j, (data164.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp6_valid
theorem data164_center_valid : ∀ j, (data164.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp12_valid
  · exact exp5_valid
theorem margin164 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data164 25 := by decide +kernel
theorem positive164 {q : EdgeTriple} (hq : q ∈ box164.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data164 25
    data164_lower_valid data164_upper_valid data164_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin164 hq

def box165 : LogBox := ⟨![(14463/8192 : ℚ),(1607/2048 : ℚ),(4821/8192 : ℚ)],![(8035/4096 : ℚ),(8035/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data165 : S1TaylorBoxData := ⟨box165,![exp24,exp10,exp6],![exp26,exp14,exp10],![exp25,exp12,exp8]⟩
theorem data165_lower_valid : ∀ j, (data165.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp6_valid
theorem data165_upper_valid : ∀ j, (data165.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp10_valid
theorem data165_center_valid : ∀ j, (data165.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp12_valid
  · exact exp8_valid
theorem margin165 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data165 25 := by decide +kernel
theorem positive165 {q : EdgeTriple} (hq : q ∈ box165.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data165 25
    data165_lower_valid data165_upper_valid data165_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin165 hq

def box166 : LogBox := ⟨![(14463/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)],![(8035/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data166 : S1TaylorBoxData := ⟨box166,![exp24,exp14,exp4],![exp26,exp18,exp10],![exp25,exp16,exp6]⟩
theorem data166_lower_valid : ∀ j, (data166.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data166_upper_valid : ∀ j, (data166.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data166_center_valid : ∀ j, (data166.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp16_valid
  · exact exp6_valid
theorem margin166 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data166 25 := by decide +kernel
theorem positive166 {q : EdgeTriple} (hq : q ∈ box166.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data166 25
    data166_lower_valid data166_upper_valid data166_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin166 hq

def box167 : LogBox := ⟨![(1607/1024 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data167 : S1TaylorBoxData := ⟨box167,![exp22,exp18,exp0],![exp24,exp20,exp4],![exp23,exp19,exp2]⟩
theorem data167_lower_valid : ∀ j, (data167.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data167_upper_valid : ∀ j, (data167.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data167_center_valid : ∀ j, (data167.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp19_valid
  · exact exp2_valid
theorem margin167 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data167 25 := by decide +kernel
theorem positive167 {q : EdgeTriple} (hq : q ∈ box167.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data167 25
    data167_lower_valid data167_upper_valid data167_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin167 hq

def box168 : LogBox := ⟨![(1607/1024 : ℚ),(11249/8192 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data168 : S1TaylorBoxData := ⟨box168,![exp22,exp20,exp0],![exp24,exp22,exp4],![exp23,exp21,exp2]⟩
theorem data168_lower_valid : ∀ j, (data168.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp20_valid
  · exact exp0_valid
theorem data168_upper_valid : ∀ j, (data168.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data168_center_valid : ∀ j, (data168.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp21_valid
  · exact exp2_valid
theorem margin168 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data168 25 := by decide +kernel
theorem positive168 {q : EdgeTriple} (hq : q ∈ box168.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data168 25
    data168_lower_valid data168_upper_valid data168_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin168 hq

def box169 : LogBox := ⟨![(14463/8192 : ℚ),(4821/4096 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data169 : S1TaylorBoxData := ⟨box169,![exp24,exp18,exp0],![exp26,exp20,exp4],![exp25,exp19,exp2]⟩
theorem data169_lower_valid : ∀ j, (data169.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp18_valid
  · exact exp0_valid
theorem data169_upper_valid : ∀ j, (data169.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data169_center_valid : ∀ j, (data169.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp19_valid
  · exact exp2_valid
theorem margin169 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data169 25 := by decide +kernel
theorem positive169 {q : EdgeTriple} (hq : q ∈ box169.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data169 25
    data169_lower_valid data169_upper_valid data169_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin169 hq

def box170 : LogBox := ⟨![(14463/8192 : ℚ),(11249/8192 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)]⟩
def data170 : S1TaylorBoxData := ⟨box170,![exp24,exp20,exp0],![exp26,exp22,exp4],![exp25,exp21,exp2]⟩
theorem data170_lower_valid : ∀ j, (data170.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp20_valid
  · exact exp0_valid
theorem data170_upper_valid : ∀ j, (data170.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data170_center_valid : ∀ j, (data170.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp21_valid
  · exact exp2_valid
theorem margin170 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data170 25 := by decide +kernel
theorem positive170 {q : EdgeTriple} (hq : q ∈ box170.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data170 25
    data170_lower_valid data170_upper_valid data170_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin170 hq

def box171 : LogBox := ⟨![(1607/1024 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(14463/8192 : ℚ),(11249/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data171 : S1TaylorBoxData := ⟨box171,![exp22,exp18,exp4],![exp24,exp20,exp10],![exp23,exp19,exp6]⟩
theorem data171_lower_valid : ∀ j, (data171.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data171_upper_valid : ∀ j, (data171.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp20_valid
  · exact exp10_valid
theorem data171_center_valid : ∀ j, (data171.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp19_valid
  · exact exp6_valid
theorem margin171 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data171 25 := by decide +kernel
theorem positive171 {q : EdgeTriple} (hq : q ∈ box171.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data171 25
    data171_lower_valid data171_upper_valid data171_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin171 hq

def box172 : LogBox := ⟨![(1607/1024 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)],![(14463/8192 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data172 : S1TaylorBoxData := ⟨box172,![exp22,exp20,exp4],![exp24,exp22,exp10],![exp23,exp21,exp6]⟩
theorem data172_lower_valid : ∀ j, (data172.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data172_upper_valid : ∀ j, (data172.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data172_center_valid : ∀ j, (data172.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp21_valid
  · exact exp6_valid
theorem margin172 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data172 25 := by decide +kernel
theorem positive172 {q : EdgeTriple} (hq : q ∈ box172.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data172 25
    data172_lower_valid data172_upper_valid data172_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin172 hq

def box173 : LogBox := ⟨![(14463/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)],![(8035/4096 : ℚ),(11249/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data173 : S1TaylorBoxData := ⟨box173,![exp24,exp18,exp4],![exp26,exp20,exp10],![exp25,exp19,exp6]⟩
theorem data173_lower_valid : ∀ j, (data173.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data173_upper_valid : ∀ j, (data173.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp20_valid
  · exact exp10_valid
theorem data173_center_valid : ∀ j, (data173.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp19_valid
  · exact exp6_valid
theorem margin173 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data173 25 := by decide +kernel
theorem positive173 {q : EdgeTriple} (hq : q ∈ box173.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data173 25
    data173_lower_valid data173_upper_valid data173_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin173 hq

def box174 : LogBox := ⟨![(14463/8192 : ℚ),(11249/8192 : ℚ),(1607/4096 : ℚ)],![(8035/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)]⟩
def data174 : S1TaylorBoxData := ⟨box174,![exp24,exp20,exp4],![exp26,exp22,exp10],![exp25,exp21,exp6]⟩
theorem data174_lower_valid : ∀ j, (data174.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp20_valid
  · exact exp4_valid
theorem data174_upper_valid : ∀ j, (data174.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data174_center_valid : ∀ j, (data174.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp21_valid
  · exact exp6_valid
theorem margin174 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data174 25 := by decide +kernel
theorem positive174 {q : EdgeTriple} (hq : q ∈ box174.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data174 25
    data174_lower_valid data174_upper_valid data174_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin174 hq

def box175 : LogBox := ⟨![(8035/4096 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(17677/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data175 : S1TaylorBoxData := ⟨box175,![exp26,exp10,exp0],![exp28,exp14,exp4],![exp27,exp12,exp2]⟩
theorem data175_lower_valid : ∀ j, (data175.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data175_upper_valid : ∀ j, (data175.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data175_center_valid : ∀ j, (data175.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp12_valid
  · exact exp2_valid
theorem margin175 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data175 25 := by decide +kernel
theorem positive175 {q : EdgeTriple} (hq : q ∈ box175.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data175 25
    data175_lower_valid data175_upper_valid data175_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin175 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

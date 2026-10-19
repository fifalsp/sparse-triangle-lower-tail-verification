import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box144 : LogBox := ⟨![(8035/4096 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(17677/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data144 : S1TaylorBoxData := ⟨box144,![exp26,exp6,exp0],![exp28,exp10,exp2],![exp27,exp8,exp1]⟩
theorem data144_lower_valid : ∀ j, (data144.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data144_upper_valid : ∀ j, (data144.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data144_center_valid : ∀ j, (data144.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin144 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data144 25 := by decide +kernel
theorem positive144 {q : EdgeTriple} (hq : q ∈ box144.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data144 25
    data144_lower_valid data144_upper_valid data144_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin144 hq

def box145 : LogBox := ⟨![(8035/4096 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(17677/8192 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data145 : S1TaylorBoxData := ⟨box145,![exp26,exp6,exp2],![exp28,exp10,exp4],![exp27,exp8,exp3]⟩
theorem data145_lower_valid : ∀ j, (data145.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data145_upper_valid : ∀ j, (data145.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data145_center_valid : ∀ j, (data145.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin145 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data145 25 := by decide +kernel
theorem positive145 {q : EdgeTriple} (hq : q ∈ box145.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data145 25
    data145_lower_valid data145_upper_valid data145_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin145 hq

def box146 : LogBox := ⟨![(17677/8192 : ℚ),(1607/4096 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data146 : S1TaylorBoxData := ⟨box146,![exp28,exp4,exp0],![exp30,exp6,exp2],![exp29,exp5,exp1]⟩
theorem data146_lower_valid : ∀ j, (data146.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp4_valid
  · exact exp0_valid
theorem data146_upper_valid : ∀ j, (data146.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data146_center_valid : ∀ j, (data146.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp5_valid
  · exact exp1_valid
theorem margin146 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data146 25 := by decide +kernel
theorem positive146 {q : EdgeTriple} (hq : q ∈ box146.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data146 25
    data146_lower_valid data146_upper_valid data146_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin146 hq

def box147 : LogBox := ⟨![(17677/8192 : ℚ),(1607/4096 : ℚ),(1607/8192 : ℚ)],![(4821/2048 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data147 : S1TaylorBoxData := ⟨box147,![exp28,exp4,exp2],![exp30,exp6,exp4],![exp29,exp5,exp3]⟩
theorem data147_lower_valid : ∀ j, (data147.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp4_valid
  · exact exp2_valid
theorem data147_upper_valid : ∀ j, (data147.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data147_center_valid : ∀ j, (data147.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp5_valid
  · exact exp3_valid
theorem margin147 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data147 25 := by decide +kernel
theorem positive147 {q : EdgeTriple} (hq : q ∈ box147.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data147 25
    data147_lower_valid data147_upper_valid data147_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin147 hq

def box148 : LogBox := ⟨![(17677/8192 : ℚ),(4821/8192 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)]⟩
def data148 : S1TaylorBoxData := ⟨box148,![exp28,exp6,exp0],![exp30,exp10,exp2],![exp29,exp8,exp1]⟩
theorem data148_lower_valid : ∀ j, (data148.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp6_valid
  · exact exp0_valid
theorem data148_upper_valid : ∀ j, (data148.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data148_center_valid : ∀ j, (data148.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp8_valid
  · exact exp1_valid
theorem margin148 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data148 25 := by decide +kernel
theorem positive148 {q : EdgeTriple} (hq : q ∈ box148.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data148 25
    data148_lower_valid data148_upper_valid data148_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin148 hq

def box149 : LogBox := ⟨![(17677/8192 : ℚ),(4821/8192 : ℚ),(1607/8192 : ℚ)],![(4821/2048 : ℚ),(1607/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data149 : S1TaylorBoxData := ⟨box149,![exp28,exp6,exp2],![exp30,exp10,exp4],![exp29,exp8,exp3]⟩
theorem data149_lower_valid : ∀ j, (data149.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp6_valid
  · exact exp2_valid
theorem data149_upper_valid : ∀ j, (data149.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp10_valid
  · exact exp4_valid
theorem data149_center_valid : ∀ j, (data149.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp8_valid
  · exact exp3_valid
theorem margin149 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data149 25 := by decide +kernel
theorem positive149 {q : EdgeTriple} (hq : q ∈ box149.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data149 25
    data149_lower_valid data149_upper_valid data149_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin149 hq

def box150 : LogBox := ⟨![(8035/4096 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(17677/8192 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data150 : S1TaylorBoxData := ⟨box150,![exp26,exp4,exp4],![exp28,exp6,exp6],![exp27,exp5,exp5]⟩
theorem data150_lower_valid : ∀ j, (data150.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data150_upper_valid : ∀ j, (data150.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data150_center_valid : ∀ j, (data150.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin150 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data150 25 := by decide +kernel
theorem positive150 {q : EdgeTriple} (hq : q ∈ box150.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data150 25
    data150_lower_valid data150_upper_valid data150_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin150 hq

def box151 : LogBox := ⟨![(8035/4096 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(17677/8192 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data151 : S1TaylorBoxData := ⟨box151,![exp26,exp6,exp4],![exp28,exp10,exp10],![exp27,exp8,exp6]⟩
theorem data151_lower_valid : ∀ j, (data151.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data151_upper_valid : ∀ j, (data151.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data151_center_valid : ∀ j, (data151.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp27_valid
  · exact exp8_valid
  · exact exp6_valid
theorem margin151 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data151 25 := by decide +kernel
theorem positive151 {q : EdgeTriple} (hq : q ∈ box151.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data151 25
    data151_lower_valid data151_upper_valid data151_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin151 hq

def box152 : LogBox := ⟨![(17677/8192 : ℚ),(1607/4096 : ℚ),(1607/4096 : ℚ)],![(4821/2048 : ℚ),(4821/8192 : ℚ),(4821/8192 : ℚ)]⟩
def data152 : S1TaylorBoxData := ⟨box152,![exp28,exp4,exp4],![exp30,exp6,exp6],![exp29,exp5,exp5]⟩
theorem data152_lower_valid : ∀ j, (data152.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp4_valid
  · exact exp4_valid
theorem data152_upper_valid : ∀ j, (data152.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp6_valid
  · exact exp6_valid
theorem data152_center_valid : ∀ j, (data152.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp5_valid
  · exact exp5_valid
theorem margin152 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data152 25 := by decide +kernel
theorem positive152 {q : EdgeTriple} (hq : q ∈ box152.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data152 25
    data152_lower_valid data152_upper_valid data152_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin152 hq

def box153 : LogBox := ⟨![(17677/8192 : ℚ),(4821/8192 : ℚ),(1607/4096 : ℚ)],![(4821/2048 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data153 : S1TaylorBoxData := ⟨box153,![exp28,exp6,exp4],![exp30,exp10,exp10],![exp29,exp8,exp6]⟩
theorem data153_lower_valid : ∀ j, (data153.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp6_valid
  · exact exp4_valid
theorem data153_upper_valid : ∀ j, (data153.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data153_center_valid : ∀ j, (data153.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp29_valid
  · exact exp8_valid
  · exact exp6_valid
theorem margin153 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data153 25 := by decide +kernel
theorem positive153 {q : EdgeTriple} (hq : q ∈ box153.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data153 25
    data153_lower_valid data153_upper_valid data153_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin153 hq

def box154 : LogBox := ⟨![(1607/1024 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data154 : S1TaylorBoxData := ⟨box154,![exp22,exp10,exp0],![exp24,exp14,exp2],![exp23,exp12,exp1]⟩
theorem data154_lower_valid : ∀ j, (data154.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data154_upper_valid : ∀ j, (data154.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data154_center_valid : ∀ j, (data154.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp12_valid
  · exact exp1_valid
theorem margin154 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data154 25 := by decide +kernel
theorem positive154 {q : EdgeTriple} (hq : q ∈ box154.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data154 25
    data154_lower_valid data154_upper_valid data154_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin154 hq

def box155 : LogBox := ⟨![(1607/1024 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)],![(14463/8192 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data155 : S1TaylorBoxData := ⟨box155,![exp22,exp10,exp2],![exp24,exp14,exp4],![exp23,exp12,exp3]⟩
theorem data155_lower_valid : ∀ j, (data155.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data155_upper_valid : ∀ j, (data155.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data155_center_valid : ∀ j, (data155.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp12_valid
  · exact exp3_valid
theorem margin155 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data155 25 := by decide +kernel
theorem positive155 {q : EdgeTriple} (hq : q ∈ box155.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data155 25
    data155_lower_valid data155_upper_valid data155_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin155 hq

def box156 : LogBox := ⟨![(1607/1024 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data156 : S1TaylorBoxData := ⟨box156,![exp22,exp14,exp0],![exp24,exp18,exp4],![exp23,exp16,exp2]⟩
theorem data156_lower_valid : ∀ j, (data156.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data156_upper_valid : ∀ j, (data156.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data156_center_valid : ∀ j, (data156.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin156 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data156 25 := by decide +kernel
theorem positive156 {q : EdgeTriple} (hq : q ∈ box156.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data156 25
    data156_lower_valid data156_upper_valid data156_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin156 hq

def box157 : LogBox := ⟨![(14463/8192 : ℚ),(1607/2048 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(8035/8192 : ℚ),(1607/8192 : ℚ)]⟩
def data157 : S1TaylorBoxData := ⟨box157,![exp24,exp10,exp0],![exp26,exp14,exp2],![exp25,exp12,exp1]⟩
theorem data157_lower_valid : ∀ j, (data157.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp0_valid
theorem data157_upper_valid : ∀ j, (data157.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp2_valid
theorem data157_center_valid : ∀ j, (data157.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp12_valid
  · exact exp1_valid
theorem margin157 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data157 25 := by decide +kernel
theorem positive157 {q : EdgeTriple} (hq : q ∈ box157.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data157 25
    data157_lower_valid data157_upper_valid data157_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin157 hq

def box158 : LogBox := ⟨![(14463/8192 : ℚ),(1607/2048 : ℚ),(1607/8192 : ℚ)],![(8035/4096 : ℚ),(8035/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data158 : S1TaylorBoxData := ⟨box158,![exp24,exp10,exp2],![exp26,exp14,exp4],![exp25,exp12,exp3]⟩
theorem data158_lower_valid : ∀ j, (data158.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp10_valid
  · exact exp2_valid
theorem data158_upper_valid : ∀ j, (data158.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp14_valid
  · exact exp4_valid
theorem data158_center_valid : ∀ j, (data158.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp12_valid
  · exact exp3_valid
theorem margin158 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data158 25 := by decide +kernel
theorem positive158 {q : EdgeTriple} (hq : q ∈ box158.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data158 25
    data158_lower_valid data158_upper_valid data158_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin158 hq

def box159 : LogBox := ⟨![(14463/8192 : ℚ),(8035/8192 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(4821/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data159 : S1TaylorBoxData := ⟨box159,![exp24,exp14,exp0],![exp26,exp18,exp4],![exp25,exp16,exp2]⟩
theorem data159_lower_valid : ∀ j, (data159.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp14_valid
  · exact exp0_valid
theorem data159_upper_valid : ∀ j, (data159.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp18_valid
  · exact exp4_valid
theorem data159_center_valid : ∀ j, (data159.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp16_valid
  · exact exp2_valid
theorem margin159 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data159 25 := by decide +kernel
theorem positive159 {q : EdgeTriple} (hq : q ∈ box159.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data159 25
    data159_lower_valid data159_upper_valid data159_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin159 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

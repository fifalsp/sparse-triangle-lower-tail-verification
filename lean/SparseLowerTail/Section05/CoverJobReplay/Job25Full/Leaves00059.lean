import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box944 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(4821/1024 : ℚ)]⟩
def data944 : S1TaylorBoxData := ⟨box944,![exp62,exp54,exp46],![exp70,exp62,exp54],![exp66,exp58,exp50]⟩
theorem data944_lower_valid : ∀ j, (data944.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data944_upper_valid : ∀ j, (data944.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp54_valid
theorem data944_center_valid : ∀ j, (data944.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp50_valid
theorem margin944 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data944 25 := by decide +kernel
theorem positive944 {q : EdgeTriple} (hq : q ∈ box944.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data944 25
    data944_lower_valid data944_upper_valid data944_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin944 hq

def box945 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/512 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(8035/2048 : ℚ)]⟩
def data945 : S1TaylorBoxData := ⟨box945,![exp62,exp62,exp38],![exp70,exp70,exp46],![exp66,exp66,exp42]⟩
theorem data945_lower_valid : ∀ j, (data945.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp38_valid
theorem data945_upper_valid : ∀ j, (data945.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp46_valid
theorem data945_center_valid : ∀ j, (data945.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp42_valid
theorem margin945 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data945 25 := by decide +kernel
theorem positive945 {q : EdgeTriple} (hq : q ∈ box945.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data945 25
    data945_lower_valid data945_upper_valid data945_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin945 hq

def box946 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(8035/2048 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(4821/1024 : ℚ)]⟩
def data946 : S1TaylorBoxData := ⟨box946,![exp62,exp62,exp46],![exp70,exp70,exp54],![exp66,exp66,exp50]⟩
theorem data946_lower_valid : ∀ j, (data946.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp46_valid
theorem data946_upper_valid : ∀ j, (data946.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp54_valid
theorem data946_center_valid : ∀ j, (data946.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp50_valid
theorem margin946 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data946 25 := by decide +kernel
theorem positive946 {q : EdgeTriple} (hq : q ∈ box946.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data946 25
    data946_lower_valid data946_upper_valid data946_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin946 hq

def box947 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(20891/4096 : ℚ)]⟩
def data947 : S1TaylorBoxData := ⟨box947,![exp54,exp54,exp54],![exp58,exp58,exp58],![exp56,exp56,exp56]⟩
theorem data947_lower_valid : ∀ j, (data947.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data947_upper_valid : ∀ j, (data947.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp58_valid
theorem data947_center_valid : ∀ j, (data947.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp56_valid
theorem margin947 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data947 25 := by decide +kernel
theorem positive947 {q : EdgeTriple} (hq : q ∈ box947.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data947 25
    data947_lower_valid data947_upper_valid data947_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin947 hq

def box948 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(11249/2048 : ℚ)]⟩
def data948 : S1TaylorBoxData := ⟨box948,![exp58,exp54,exp54],![exp62,exp62,exp62],![exp60,exp58,exp58]⟩
theorem data948_lower_valid : ∀ j, (data948.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data948_upper_valid : ∀ j, (data948.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp62_valid
theorem data948_center_valid : ∀ j, (data948.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp58_valid
  · exact exp58_valid
theorem margin948 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data948 25 := by decide +kernel
theorem positive948 {q : EdgeTriple} (hq : q ∈ box948.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data948 25
    data948_lower_valid data948_upper_valid data948_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin948 hq

def box949 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(11249/2048 : ℚ)]⟩
def data949 : S1TaylorBoxData := ⟨box949,![exp62,exp54,exp54],![exp70,exp62,exp62],![exp66,exp58,exp58]⟩
theorem data949_lower_valid : ∀ j, (data949.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data949_upper_valid : ∀ j, (data949.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp62_valid
theorem data949_center_valid : ∀ j, (data949.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp58_valid
theorem margin949 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data949 25 := by decide +kernel
theorem positive949 {q : EdgeTriple} (hq : q ∈ box949.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data949 25
    data949_lower_valid data949_upper_valid data949_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin949 hq

def box950 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(4821/1024 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(11249/2048 : ℚ)]⟩
def data950 : S1TaylorBoxData := ⟨box950,![exp62,exp62,exp54],![exp70,exp70,exp62],![exp66,exp66,exp58]⟩
theorem data950_lower_valid : ∀ j, (data950.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp54_valid
theorem data950_upper_valid : ∀ j, (data950.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp62_valid
theorem data950_center_valid : ∀ j, (data950.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp58_valid
theorem margin950 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data950 25 := by decide +kernel
theorem positive950 {q : EdgeTriple} (hq : q ∈ box950.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data950 25
    data950_lower_valid data950_upper_valid data950_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin950 hq

def box951 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(11249/2048 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/256 : ℚ)]⟩
def data951 : S1TaylorBoxData := ⟨box951,![exp62,exp62,exp62],![exp70,exp70,exp70],![exp66,exp66,exp66]⟩
theorem data951_lower_valid : ∀ j, (data951.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp62_valid
theorem data951_upper_valid : ∀ j, (data951.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp70_valid
theorem data951_center_valid : ∀ j, (data951.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp66_valid
theorem margin951 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data951 25 := by decide +kernel
theorem positive951 {q : EdgeTriple} (hq : q ∈ box951.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data951 25
    data951_lower_valid data951_upper_valid data951_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin951 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

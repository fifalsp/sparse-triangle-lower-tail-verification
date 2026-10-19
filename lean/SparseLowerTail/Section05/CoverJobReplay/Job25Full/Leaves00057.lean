import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box912 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data912 : S1TaylorBoxData := ⟨box912,![exp58,exp46,exp38],![exp62,exp50,exp42],![exp60,exp48,exp40]⟩
theorem data912_lower_valid : ∀ j, (data912.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data912_upper_valid : ∀ j, (data912.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp42_valid
theorem data912_center_valid : ∀ j, (data912.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp40_valid
theorem margin912 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data912 25 := by decide +kernel
theorem positive912 {q : EdgeTriple} (hq : q ∈ box912.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data912 25
    data912_lower_valid data912_upper_valid data912_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin912 hq

def box913 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data913 : S1TaylorBoxData := ⟨box913,![exp58,exp46,exp42],![exp62,exp50,exp46],![exp60,exp48,exp44]⟩
theorem data913_lower_valid : ∀ j, (data913.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data913_upper_valid : ∀ j, (data913.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data913_center_valid : ∀ j, (data913.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp44_valid
theorem margin913 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data913 25 := by decide +kernel
theorem positive913 {q : EdgeTriple} (hq : q ∈ box913.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data913 25
    data913_lower_valid data913_upper_valid data913_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin913 hq

def box914 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(14463/4096 : ℚ)]⟩
def data914 : S1TaylorBoxData := ⟨box914,![exp58,exp50,exp38],![exp62,exp54,exp42],![exp60,exp52,exp40]⟩
theorem data914_lower_valid : ∀ j, (data914.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data914_upper_valid : ∀ j, (data914.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp42_valid
theorem data914_center_valid : ∀ j, (data914.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp40_valid
theorem margin914 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data914 25 := by decide +kernel
theorem positive914 {q : EdgeTriple} (hq : q ∈ box914.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data914 25
    data914_lower_valid data914_upper_valid data914_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin914 hq

def box915 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(14463/4096 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)]⟩
def data915 : S1TaylorBoxData := ⟨box915,![exp58,exp50,exp42],![exp62,exp54,exp46],![exp60,exp52,exp44]⟩
theorem data915_lower_valid : ∀ j, (data915.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp42_valid
theorem data915_upper_valid : ∀ j, (data915.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data915_center_valid : ∀ j, (data915.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp44_valid
theorem margin915 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data915 25 := by decide +kernel
theorem positive915 {q : EdgeTriple} (hq : q ∈ box915.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data915 25
    data915_lower_valid data915_upper_valid data915_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin915 hq

def box916 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(17677/4096 : ℚ)]⟩
def data916 : S1TaylorBoxData := ⟨box916,![exp54,exp46,exp46],![exp58,exp50,exp50],![exp56,exp48,exp48]⟩
theorem data916_lower_valid : ∀ j, (data916.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data916_upper_valid : ∀ j, (data916.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp50_valid
theorem data916_center_valid : ∀ j, (data916.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp48_valid
theorem margin916 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data916 25 := by decide +kernel
theorem positive916 {q : EdgeTriple} (hq : q ∈ box916.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data916 25
    data916_lower_valid data916_upper_valid data916_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin916 hq

def box917 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(17677/4096 : ℚ)]⟩
def data917 : S1TaylorBoxData := ⟨box917,![exp54,exp50,exp46],![exp58,exp54,exp50],![exp56,exp52,exp48]⟩
theorem data917_lower_valid : ∀ j, (data917.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data917_upper_valid : ∀ j, (data917.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp50_valid
theorem data917_center_valid : ∀ j, (data917.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp48_valid
theorem margin917 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data917 25 := by decide +kernel
theorem positive917 {q : EdgeTriple} (hq : q ∈ box917.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data917 25
    data917_lower_valid data917_upper_valid data917_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin917 hq

def box918 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(17677/4096 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)]⟩
def data918 : S1TaylorBoxData := ⟨box918,![exp54,exp50,exp50],![exp58,exp54,exp54],![exp56,exp52,exp52]⟩
theorem data918_lower_valid : ∀ j, (data918.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp50_valid
theorem data918_upper_valid : ∀ j, (data918.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data918_center_valid : ∀ j, (data918.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp52_valid
theorem margin918 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data918 25 := by decide +kernel
theorem positive918 {q : EdgeTriple} (hq : q ∈ box918.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data918 25
    data918_lower_valid data918_upper_valid data918_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin918 hq

def box919 : LogBox := ⟨![(20891/4096 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)],![(11249/2048 : ℚ),(17677/4096 : ℚ),(17677/4096 : ℚ)]⟩
def data919 : S1TaylorBoxData := ⟨box919,![exp58,exp46,exp46],![exp62,exp50,exp50],![exp60,exp48,exp48]⟩
theorem data919_lower_valid : ∀ j, (data919.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data919_upper_valid : ∀ j, (data919.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp50_valid
theorem data919_center_valid : ∀ j, (data919.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp48_valid
  · exact exp48_valid
theorem margin919 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data919 25 := by decide +kernel
theorem positive919 {q : EdgeTriple} (hq : q ∈ box919.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data919 25
    data919_lower_valid data919_upper_valid data919_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin919 hq

def box920 : LogBox := ⟨![(20891/4096 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)],![(11249/2048 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)]⟩
def data920 : S1TaylorBoxData := ⟨box920,![exp58,exp50,exp46],![exp62,exp54,exp54],![exp60,exp52,exp50]⟩
theorem data920_lower_valid : ∀ j, (data920.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data920_upper_valid : ∀ j, (data920.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data920_center_valid : ∀ j, (data920.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp52_valid
  · exact exp50_valid
theorem margin920 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data920 25 := by decide +kernel
theorem positive920 {q : EdgeTriple} (hq : q ∈ box920.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data920 25
    data920_lower_valid data920_upper_valid data920_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin920 hq

def box921 : LogBox := ⟨![(11249/2048 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(24105/4096 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data921 : S1TaylorBoxData := ⟨box921,![exp62,exp38,exp38],![exp66,exp42,exp42],![exp64,exp40,exp40]⟩
theorem data921_lower_valid : ∀ j, (data921.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data921_upper_valid : ∀ j, (data921.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data921_center_valid : ∀ j, (data921.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin921 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data921 25 := by decide +kernel
theorem positive921 {q : EdgeTriple} (hq : q ∈ box921.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data921 25
    data921_lower_valid data921_upper_valid data921_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin921 hq

def box922 : LogBox := ⟨![(11249/2048 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)],![(24105/4096 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data922 : S1TaylorBoxData := ⟨box922,![exp62,exp42,exp38],![exp66,exp46,exp46],![exp64,exp44,exp42]⟩
theorem data922_lower_valid : ∀ j, (data922.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data922_upper_valid : ∀ j, (data922.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data922_center_valid : ∀ j, (data922.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp44_valid
  · exact exp42_valid
theorem margin922 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data922 25 := by decide +kernel
theorem positive922 {q : EdgeTriple} (hq : q ∈ box922.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data922 25
    data922_lower_valid data922_upper_valid data922_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin922 hq

def box923 : LogBox := ⟨![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(1607/256 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data923 : S1TaylorBoxData := ⟨box923,![exp66,exp38,exp38],![exp70,exp42,exp42],![exp68,exp40,exp40]⟩
theorem data923_lower_valid : ∀ j, (data923.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data923_upper_valid : ∀ j, (data923.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data923_center_valid : ∀ j, (data923.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin923 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data923 25 := by decide +kernel
theorem positive923 {q : EdgeTriple} (hq : q ∈ box923.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data923 25
    data923_lower_valid data923_upper_valid data923_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin923 hq

def box924 : LogBox := ⟨![(24105/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)],![(1607/256 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data924 : S1TaylorBoxData := ⟨box924,![exp66,exp42,exp38],![exp70,exp46,exp46],![exp68,exp44,exp42]⟩
theorem data924_lower_valid : ∀ j, (data924.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data924_upper_valid : ∀ j, (data924.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data924_center_valid : ∀ j, (data924.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp44_valid
  · exact exp42_valid
theorem margin924 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data924 25 := by decide +kernel
theorem positive924 {q : EdgeTriple} (hq : q ∈ box924.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data924 25
    data924_lower_valid data924_upper_valid data924_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin924 hq

def box925 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data925 : S1TaylorBoxData := ⟨box925,![exp62,exp46,exp38],![exp66,exp50,exp46],![exp64,exp48,exp42]⟩
theorem data925_lower_valid : ∀ j, (data925.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data925_upper_valid : ∀ j, (data925.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data925_center_valid : ∀ j, (data925.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp42_valid
theorem margin925 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data925 25 := by decide +kernel
theorem positive925 {q : EdgeTriple} (hq : q ∈ box925.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data925 25
    data925_lower_valid data925_upper_valid data925_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin925 hq

def box926 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)]⟩
def data926 : S1TaylorBoxData := ⟨box926,![exp62,exp50,exp38],![exp66,exp54,exp46],![exp64,exp52,exp42]⟩
theorem data926_lower_valid : ∀ j, (data926.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data926_upper_valid : ∀ j, (data926.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data926_center_valid : ∀ j, (data926.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp42_valid
theorem margin926 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data926 25 := by decide +kernel
theorem positive926 {q : EdgeTriple} (hq : q ∈ box926.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data926 25
    data926_lower_valid data926_upper_valid data926_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin926 hq

def box927 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)]⟩
def data927 : S1TaylorBoxData := ⟨box927,![exp66,exp46,exp38],![exp70,exp54,exp46],![exp68,exp50,exp42]⟩
theorem data927_lower_valid : ∀ j, (data927.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data927_upper_valid : ∀ j, (data927.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data927_center_valid : ∀ j, (data927.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp50_valid
  · exact exp42_valid
theorem margin927 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data927 25 := by decide +kernel
theorem positive927 {q : EdgeTriple} (hq : q ∈ box927.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data927 25
    data927_lower_valid data927_upper_valid data927_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin927 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box928 : LogBox := ⟨![(11249/2048 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)],![(24105/4096 : ℚ),(17677/4096 : ℚ),(17677/4096 : ℚ)]⟩
def data928 : S1TaylorBoxData := ⟨box928,![exp62,exp46,exp46],![exp66,exp50,exp50],![exp64,exp48,exp48]⟩
theorem data928_lower_valid : ∀ j, (data928.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data928_upper_valid : ∀ j, (data928.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp50_valid
  · exact exp50_valid
theorem data928_center_valid : ∀ j, (data928.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp48_valid
  · exact exp48_valid
theorem margin928 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data928 25 := by decide +kernel
theorem positive928 {q : EdgeTriple} (hq : q ∈ box928.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data928 25
    data928_lower_valid data928_upper_valid data928_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin928 hq

def box929 : LogBox := ⟨![(11249/2048 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)],![(24105/4096 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)]⟩
def data929 : S1TaylorBoxData := ⟨box929,![exp62,exp50,exp46],![exp66,exp54,exp54],![exp64,exp52,exp50]⟩
theorem data929_lower_valid : ∀ j, (data929.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data929_upper_valid : ∀ j, (data929.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data929_center_valid : ∀ j, (data929.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp52_valid
  · exact exp50_valid
theorem margin929 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data929 25 := by decide +kernel
theorem positive929 {q : EdgeTriple} (hq : q ∈ box929.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data929 25
    data929_lower_valid data929_upper_valid data929_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin929 hq

def box930 : LogBox := ⟨![(24105/4096 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)],![(1607/256 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)]⟩
def data930 : S1TaylorBoxData := ⟨box930,![exp66,exp46,exp46],![exp70,exp54,exp54],![exp68,exp50,exp50]⟩
theorem data930_lower_valid : ∀ j, (data930.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data930_upper_valid : ∀ j, (data930.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data930_center_valid : ∀ j, (data930.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp50_valid
  · exact exp50_valid
theorem margin930 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data930 25 := by decide +kernel
theorem positive930 {q : EdgeTriple} (hq : q ∈ box930.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data930 25
    data930_lower_valid data930_upper_valid data930_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin930 hq

def box931 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data931 : S1TaylorBoxData := ⟨box931,![exp54,exp54,exp38],![exp58,exp58,exp42],![exp56,exp56,exp40]⟩
theorem data931_lower_valid : ∀ j, (data931.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data931_upper_valid : ∀ j, (data931.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp42_valid
theorem data931_center_valid : ∀ j, (data931.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp40_valid
theorem margin931 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data931 25 := by decide +kernel
theorem positive931 {q : EdgeTriple} (hq : q ∈ box931.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data931 25
    data931_lower_valid data931_upper_valid data931_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin931 hq

def box932 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(14463/4096 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data932 : S1TaylorBoxData := ⟨box932,![exp54,exp54,exp42],![exp58,exp58,exp46],![exp56,exp56,exp44]⟩
theorem data932_lower_valid : ∀ j, (data932.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp42_valid
theorem data932_upper_valid : ∀ j, (data932.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp46_valid
theorem data932_center_valid : ∀ j, (data932.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp44_valid
theorem margin932 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data932 25 := by decide +kernel
theorem positive932 {q : EdgeTriple} (hq : q ∈ box932.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data932 25
    data932_lower_valid data932_upper_valid data932_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin932 hq

def box933 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data933 : S1TaylorBoxData := ⟨box933,![exp58,exp54,exp38],![exp62,exp58,exp42],![exp60,exp56,exp40]⟩
theorem data933_lower_valid : ∀ j, (data933.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data933_upper_valid : ∀ j, (data933.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp42_valid
theorem data933_center_valid : ∀ j, (data933.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp40_valid
theorem margin933 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data933 25 := by decide +kernel
theorem positive933 {q : EdgeTriple} (hq : q ∈ box933.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data933 25
    data933_lower_valid data933_upper_valid data933_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin933 hq

def box934 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(14463/4096 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data934 : S1TaylorBoxData := ⟨box934,![exp58,exp54,exp42],![exp62,exp58,exp46],![exp60,exp56,exp44]⟩
theorem data934_lower_valid : ∀ j, (data934.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp42_valid
theorem data934_upper_valid : ∀ j, (data934.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp46_valid
theorem data934_center_valid : ∀ j, (data934.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp44_valid
theorem margin934 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data934 25 := by decide +kernel
theorem positive934 {q : EdgeTriple} (hq : q ∈ box934.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data934 25
    data934_lower_valid data934_upper_valid data934_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin934 hq

def box935 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(1607/512 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(14463/4096 : ℚ)]⟩
def data935 : S1TaylorBoxData := ⟨box935,![exp58,exp58,exp38],![exp62,exp62,exp42],![exp60,exp60,exp40]⟩
theorem data935_lower_valid : ∀ j, (data935.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp38_valid
theorem data935_upper_valid : ∀ j, (data935.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp42_valid
theorem data935_center_valid : ∀ j, (data935.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp40_valid
theorem margin935 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data935 25 := by decide +kernel
theorem positive935 {q : EdgeTriple} (hq : q ∈ box935.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data935 25
    data935_lower_valid data935_upper_valid data935_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin935 hq

def box936 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(14463/4096 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data936 : S1TaylorBoxData := ⟨box936,![exp58,exp58,exp42],![exp62,exp62,exp46],![exp60,exp60,exp44]⟩
theorem data936_lower_valid : ∀ j, (data936.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp42_valid
theorem data936_upper_valid : ∀ j, (data936.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp46_valid
theorem data936_center_valid : ∀ j, (data936.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp44_valid
theorem margin936 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data936 25 := by decide +kernel
theorem positive936 {q : EdgeTriple} (hq : q ∈ box936.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data936 25
    data936_lower_valid data936_upper_valid data936_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin936 hq

def box937 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(17677/4096 : ℚ)]⟩
def data937 : S1TaylorBoxData := ⟨box937,![exp54,exp54,exp46],![exp58,exp58,exp50],![exp56,exp56,exp48]⟩
theorem data937_lower_valid : ∀ j, (data937.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data937_upper_valid : ∀ j, (data937.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp50_valid
theorem data937_center_valid : ∀ j, (data937.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp48_valid
theorem margin937 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data937 25 := by decide +kernel
theorem positive937 {q : EdgeTriple} (hq : q ∈ box937.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data937 25
    data937_lower_valid data937_upper_valid data937_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin937 hq

def box938 : LogBox := ⟨![(4821/1024 : ℚ),(4821/1024 : ℚ),(17677/4096 : ℚ)],![(20891/4096 : ℚ),(20891/4096 : ℚ),(4821/1024 : ℚ)]⟩
def data938 : S1TaylorBoxData := ⟨box938,![exp54,exp54,exp50],![exp58,exp58,exp54],![exp56,exp56,exp52]⟩
theorem data938_lower_valid : ∀ j, (data938.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp50_valid
theorem data938_upper_valid : ∀ j, (data938.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp54_valid
theorem data938_center_valid : ∀ j, (data938.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp56_valid
  · exact exp52_valid
theorem margin938 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data938 25 := by decide +kernel
theorem positive938 {q : EdgeTriple} (hq : q ∈ box938.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data938 25
    data938_lower_valid data938_upper_valid data938_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin938 hq

def box939 : LogBox := ⟨![(20891/4096 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)],![(11249/2048 : ℚ),(20891/4096 : ℚ),(4821/1024 : ℚ)]⟩
def data939 : S1TaylorBoxData := ⟨box939,![exp58,exp54,exp46],![exp62,exp58,exp54],![exp60,exp56,exp50]⟩
theorem data939_lower_valid : ∀ j, (data939.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data939_upper_valid : ∀ j, (data939.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp54_valid
theorem data939_center_valid : ∀ j, (data939.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp56_valid
  · exact exp50_valid
theorem margin939 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data939 25 := by decide +kernel
theorem positive939 {q : EdgeTriple} (hq : q ∈ box939.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data939 25
    data939_lower_valid data939_upper_valid data939_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin939 hq

def box940 : LogBox := ⟨![(20891/4096 : ℚ),(20891/4096 : ℚ),(8035/2048 : ℚ)],![(11249/2048 : ℚ),(11249/2048 : ℚ),(4821/1024 : ℚ)]⟩
def data940 : S1TaylorBoxData := ⟨box940,![exp58,exp58,exp46],![exp62,exp62,exp54],![exp60,exp60,exp50]⟩
theorem data940_lower_valid : ∀ j, (data940.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp58_valid
  · exact exp46_valid
theorem data940_upper_valid : ∀ j, (data940.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp54_valid
theorem data940_center_valid : ∀ j, (data940.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp60_valid
  · exact exp50_valid
theorem margin940 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data940 25 := by decide +kernel
theorem positive940 {q : EdgeTriple} (hq : q ∈ box940.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data940 25
    data940_lower_valid data940_upper_valid data940_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin940 hq

def box941 : LogBox := ⟨![(11249/2048 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)],![(24105/4096 : ℚ),(20891/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data941 : S1TaylorBoxData := ⟨box941,![exp62,exp54,exp38],![exp66,exp58,exp46],![exp64,exp56,exp42]⟩
theorem data941_lower_valid : ∀ j, (data941.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data941_upper_valid : ∀ j, (data941.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp58_valid
  · exact exp46_valid
theorem data941_center_valid : ∀ j, (data941.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp56_valid
  · exact exp42_valid
theorem margin941 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data941 25 := by decide +kernel
theorem positive941 {q : EdgeTriple} (hq : q ∈ box941.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data941 25
    data941_lower_valid data941_upper_valid data941_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin941 hq

def box942 : LogBox := ⟨![(11249/2048 : ℚ),(20891/4096 : ℚ),(1607/512 : ℚ)],![(24105/4096 : ℚ),(11249/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data942 : S1TaylorBoxData := ⟨box942,![exp62,exp58,exp38],![exp66,exp62,exp46],![exp64,exp60,exp42]⟩
theorem data942_lower_valid : ∀ j, (data942.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp58_valid
  · exact exp38_valid
theorem data942_upper_valid : ∀ j, (data942.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp62_valid
  · exact exp46_valid
theorem data942_center_valid : ∀ j, (data942.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp60_valid
  · exact exp42_valid
theorem margin942 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data942 25 := by decide +kernel
theorem positive942 {q : EdgeTriple} (hq : q ∈ box942.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data942 25
    data942_lower_valid data942_upper_valid data942_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin942 hq

def box943 : LogBox := ⟨![(24105/4096 : ℚ),(4821/1024 : ℚ),(1607/512 : ℚ)],![(1607/256 : ℚ),(11249/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data943 : S1TaylorBoxData := ⟨box943,![exp66,exp54,exp38],![exp70,exp62,exp46],![exp68,exp58,exp42]⟩
theorem data943_lower_valid : ∀ j, (data943.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp54_valid
  · exact exp38_valid
theorem data943_upper_valid : ∀ j, (data943.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp62_valid
  · exact exp46_valid
theorem data943_center_valid : ∀ j, (data943.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp58_valid
  · exact exp42_valid
theorem margin943 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data943 25 := by decide +kernel
theorem positive943 {q : EdgeTriple} (hq : q ∈ box943.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data943 25
    data943_lower_valid data943_upper_valid data943_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin943 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

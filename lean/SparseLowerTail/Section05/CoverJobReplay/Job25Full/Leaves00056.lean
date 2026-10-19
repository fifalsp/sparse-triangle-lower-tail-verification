import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box896 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(14463/4096 : ℚ)]⟩
def data896 : S1TaylorBoxData := ⟨box896,![exp50,exp50,exp38],![exp54,exp54,exp42],![exp52,exp52,exp40]⟩
theorem data896_lower_valid : ∀ j, (data896.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data896_upper_valid : ∀ j, (data896.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp42_valid
theorem data896_center_valid : ∀ j, (data896.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp40_valid
theorem margin896 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data896 25 := by decide +kernel
theorem positive896 {q : EdgeTriple} (hq : q ∈ box896.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data896 25
    data896_lower_valid data896_upper_valid data896_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin896 hq

def box897 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(14463/4096 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)]⟩
def data897 : S1TaylorBoxData := ⟨box897,![exp50,exp50,exp42],![exp54,exp54,exp46],![exp52,exp52,exp44]⟩
theorem data897_lower_valid : ∀ j, (data897.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp42_valid
theorem data897_upper_valid : ∀ j, (data897.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data897_center_valid : ∀ j, (data897.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp44_valid
theorem margin897 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data897 25 := by decide +kernel
theorem positive897 {q : EdgeTriple} (hq : q ∈ box897.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data897 25
    data897_lower_valid data897_upper_valid data897_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin897 hq

def box898 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(17677/4096 : ℚ)]⟩
def data898 : S1TaylorBoxData := ⟨box898,![exp46,exp46,exp46],![exp50,exp50,exp50],![exp48,exp48,exp48]⟩
theorem data898_lower_valid : ∀ j, (data898.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data898_upper_valid : ∀ j, (data898.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp50_valid
theorem data898_center_valid : ∀ j, (data898.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp48_valid
theorem margin898 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data898 25 := by decide +kernel
theorem positive898 {q : EdgeTriple} (hq : q ∈ box898.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data898 25
    data898_lower_valid data898_upper_valid data898_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin898 hq

def box899 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(17677/4096 : ℚ)]⟩
def data899 : S1TaylorBoxData := ⟨box899,![exp50,exp46,exp46],![exp54,exp50,exp50],![exp52,exp48,exp48]⟩
theorem data899_lower_valid : ∀ j, (data899.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data899_upper_valid : ∀ j, (data899.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp50_valid
theorem data899_center_valid : ∀ j, (data899.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp48_valid
theorem margin899 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data899 25 := by decide +kernel
theorem positive899 {q : EdgeTriple} (hq : q ∈ box899.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data899 25
    data899_lower_valid data899_upper_valid data899_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin899 hq

def box900 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(17677/4096 : ℚ)]⟩
def data900 : S1TaylorBoxData := ⟨box900,![exp50,exp50,exp46],![exp54,exp54,exp50],![exp52,exp52,exp48]⟩
theorem data900_lower_valid : ∀ j, (data900.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data900_upper_valid : ∀ j, (data900.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp50_valid
theorem data900_center_valid : ∀ j, (data900.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp48_valid
theorem margin900 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data900 25 := by decide +kernel
theorem positive900 {q : EdgeTriple} (hq : q ∈ box900.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data900 25
    data900_lower_valid data900_upper_valid data900_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin900 hq

def box901 : LogBox := ⟨![(17677/4096 : ℚ),(17677/4096 : ℚ),(17677/4096 : ℚ)],![(4821/1024 : ℚ),(4821/1024 : ℚ),(4821/1024 : ℚ)]⟩
def data901 : S1TaylorBoxData := ⟨box901,![exp50,exp50,exp50],![exp54,exp54,exp54],![exp52,exp52,exp52]⟩
theorem data901_lower_valid : ∀ j, (data901.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp50_valid
theorem data901_upper_valid : ∀ j, (data901.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp54_valid
  · exact exp54_valid
theorem data901_center_valid : ∀ j, (data901.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp52_valid
  · exact exp52_valid
theorem margin901 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data901 25 := by decide +kernel
theorem positive901 {q : EdgeTriple} (hq : q ∈ box901.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data901 25
    data901_lower_valid data901_upper_valid data901_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin901 hq

def box902 : LogBox := ⟨![(4821/1024 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(20891/4096 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data902 : S1TaylorBoxData := ⟨box902,![exp54,exp38,exp38],![exp58,exp42,exp42],![exp56,exp40,exp40]⟩
theorem data902_lower_valid : ∀ j, (data902.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data902_upper_valid : ∀ j, (data902.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data902_center_valid : ∀ j, (data902.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin902 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data902 25 := by decide +kernel
theorem positive902 {q : EdgeTriple} (hq : q ∈ box902.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data902 25
    data902_lower_valid data902_upper_valid data902_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin902 hq

def box903 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)]⟩
def data903 : S1TaylorBoxData := ⟨box903,![exp54,exp42,exp38],![exp58,exp46,exp42],![exp56,exp44,exp40]⟩
theorem data903_lower_valid : ∀ j, (data903.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data903_upper_valid : ∀ j, (data903.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data903_center_valid : ∀ j, (data903.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp40_valid
theorem margin903 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data903 25 := by decide +kernel
theorem positive903 {q : EdgeTriple} (hq : q ∈ box903.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data903 25
    data903_lower_valid data903_upper_valid data903_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin903 hq

def box904 : LogBox := ⟨![(4821/1024 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)],![(20891/4096 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data904 : S1TaylorBoxData := ⟨box904,![exp54,exp42,exp42],![exp58,exp46,exp46],![exp56,exp44,exp44]⟩
theorem data904_lower_valid : ∀ j, (data904.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data904_upper_valid : ∀ j, (data904.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data904_center_valid : ∀ j, (data904.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp44_valid
  · exact exp44_valid
theorem margin904 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data904 25 := by decide +kernel
theorem positive904 {q : EdgeTriple} (hq : q ∈ box904.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data904 25
    data904_lower_valid data904_upper_valid data904_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin904 hq

def box905 : LogBox := ⟨![(20891/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(11249/2048 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data905 : S1TaylorBoxData := ⟨box905,![exp58,exp38,exp38],![exp62,exp42,exp42],![exp60,exp40,exp40]⟩
theorem data905_lower_valid : ∀ j, (data905.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data905_upper_valid : ∀ j, (data905.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data905_center_valid : ∀ j, (data905.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin905 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data905 25 := by decide +kernel
theorem positive905 {q : EdgeTriple} (hq : q ∈ box905.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data905 25
    data905_lower_valid data905_upper_valid data905_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin905 hq

def box906 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)]⟩
def data906 : S1TaylorBoxData := ⟨box906,![exp58,exp42,exp38],![exp62,exp46,exp42],![exp60,exp44,exp40]⟩
theorem data906_lower_valid : ∀ j, (data906.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data906_upper_valid : ∀ j, (data906.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data906_center_valid : ∀ j, (data906.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp40_valid
theorem margin906 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data906 25 := by decide +kernel
theorem positive906 {q : EdgeTriple} (hq : q ∈ box906.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data906 25
    data906_lower_valid data906_upper_valid data906_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin906 hq

def box907 : LogBox := ⟨![(20891/4096 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)],![(11249/2048 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data907 : S1TaylorBoxData := ⟨box907,![exp58,exp42,exp42],![exp62,exp46,exp46],![exp60,exp44,exp44]⟩
theorem data907_lower_valid : ∀ j, (data907.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data907_upper_valid : ∀ j, (data907.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data907_center_valid : ∀ j, (data907.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp60_valid
  · exact exp44_valid
  · exact exp44_valid
theorem margin907 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data907 25 := by decide +kernel
theorem positive907 {q : EdgeTriple} (hq : q ∈ box907.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data907 25
    data907_lower_valid data907_upper_valid data907_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin907 hq

def box908 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data908 : S1TaylorBoxData := ⟨box908,![exp54,exp46,exp38],![exp58,exp50,exp42],![exp56,exp48,exp40]⟩
theorem data908_lower_valid : ∀ j, (data908.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data908_upper_valid : ∀ j, (data908.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp42_valid
theorem data908_center_valid : ∀ j, (data908.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp40_valid
theorem margin908 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data908 25 := by decide +kernel
theorem positive908 {q : EdgeTriple} (hq : q ∈ box908.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data908 25
    data908_lower_valid data908_upper_valid data908_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin908 hq

def box909 : LogBox := ⟨![(4821/1024 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)],![(20891/4096 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data909 : S1TaylorBoxData := ⟨box909,![exp54,exp46,exp42],![exp58,exp50,exp46],![exp56,exp48,exp44]⟩
theorem data909_lower_valid : ∀ j, (data909.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data909_upper_valid : ∀ j, (data909.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data909_center_valid : ∀ j, (data909.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp48_valid
  · exact exp44_valid
theorem margin909 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data909 25 := by decide +kernel
theorem positive909 {q : EdgeTriple} (hq : q ∈ box909.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data909 25
    data909_lower_valid data909_upper_valid data909_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin909 hq

def box910 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(1607/512 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(14463/4096 : ℚ)]⟩
def data910 : S1TaylorBoxData := ⟨box910,![exp54,exp50,exp38],![exp58,exp54,exp42],![exp56,exp52,exp40]⟩
theorem data910_lower_valid : ∀ j, (data910.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp38_valid
theorem data910_upper_valid : ∀ j, (data910.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp42_valid
theorem data910_center_valid : ∀ j, (data910.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp40_valid
theorem margin910 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data910 25 := by decide +kernel
theorem positive910 {q : EdgeTriple} (hq : q ∈ box910.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data910 25
    data910_lower_valid data910_upper_valid data910_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin910 hq

def box911 : LogBox := ⟨![(4821/1024 : ℚ),(17677/4096 : ℚ),(14463/4096 : ℚ)],![(20891/4096 : ℚ),(4821/1024 : ℚ),(8035/2048 : ℚ)]⟩
def data911 : S1TaylorBoxData := ⟨box911,![exp54,exp50,exp42],![exp58,exp54,exp46],![exp56,exp52,exp44]⟩
theorem data911_lower_valid : ∀ j, (data911.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp42_valid
theorem data911_upper_valid : ∀ j, (data911.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp58_valid
  · exact exp54_valid
  · exact exp46_valid
theorem data911_center_valid : ∀ j, (data911.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp56_valid
  · exact exp52_valid
  · exact exp44_valid
theorem margin911 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data911 25 := by decide +kernel
theorem positive911 {q : EdgeTriple} (hq : q ∈ box911.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data911 25
    data911_lower_valid data911_upper_valid data911_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin911 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

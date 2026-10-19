import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box880 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(4821/2048 : ℚ)]⟩
def data880 : S1TaylorBoxData := ⟨box880,![exp62,exp62,exp22],![exp70,exp70,exp30],![exp66,exp66,exp26]⟩
theorem data880_lower_valid : ∀ j, (data880.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp22_valid
theorem data880_upper_valid : ∀ j, (data880.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp30_valid
theorem data880_center_valid : ∀ j, (data880.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp26_valid
theorem margin880 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data880 25 := by decide +kernel
theorem positive880 {q : EdgeTriple} (hq : q ∈ box880.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data880 25
    data880_lower_valid data880_upper_valid data880_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin880 hq

def box881 : LogBox := ⟨![(11249/2048 : ℚ),(11249/2048 : ℚ),(4821/2048 : ℚ)],![(1607/256 : ℚ),(1607/256 : ℚ),(1607/512 : ℚ)]⟩
def data881 : S1TaylorBoxData := ⟨box881,![exp62,exp62,exp30],![exp70,exp70,exp38],![exp66,exp66,exp34]⟩
theorem data881_lower_valid : ∀ j, (data881.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp62_valid
  · exact exp30_valid
theorem data881_upper_valid : ∀ j, (data881.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp70_valid
  · exact exp38_valid
theorem data881_center_valid : ∀ j, (data881.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp66_valid
  · exact exp34_valid
theorem margin881 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data881 25 := by decide +kernel
theorem positive881 {q : EdgeTriple} (hq : q ∈ box881.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data881 25
    data881_lower_valid data881_upper_valid data881_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin881 hq

def box882 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data882 : S1TaylorBoxData := ⟨box882,![exp38,exp38,exp38],![exp42,exp42,exp42],![exp40,exp40,exp40]⟩
theorem data882_lower_valid : ∀ j, (data882.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data882_upper_valid : ∀ j, (data882.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data882_center_valid : ∀ j, (data882.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin882 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data882 25 := by decide +kernel
theorem positive882 {q : EdgeTriple} (hq : q ∈ box882.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data882 25
    data882_lower_valid data882_upper_valid data882_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin882 hq

def box883 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data883 : S1TaylorBoxData := ⟨box883,![exp42,exp38,exp38],![exp46,exp42,exp42],![exp44,exp40,exp40]⟩
theorem data883_lower_valid : ∀ j, (data883.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data883_upper_valid : ∀ j, (data883.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data883_center_valid : ∀ j, (data883.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin883 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data883 25 := by decide +kernel
theorem positive883 {q : EdgeTriple} (hq : q ∈ box883.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data883 25
    data883_lower_valid data883_upper_valid data883_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin883 hq

def box884 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)]⟩
def data884 : S1TaylorBoxData := ⟨box884,![exp42,exp42,exp38],![exp46,exp46,exp42],![exp44,exp44,exp40]⟩
theorem data884_lower_valid : ∀ j, (data884.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data884_upper_valid : ∀ j, (data884.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data884_center_valid : ∀ j, (data884.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp40_valid
theorem margin884 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data884 25 := by decide +kernel
theorem positive884 {q : EdgeTriple} (hq : q ∈ box884.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data884 25
    data884_lower_valid data884_upper_valid data884_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin884 hq

def box885 : LogBox := ⟨![(14463/4096 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)],![(8035/2048 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data885 : S1TaylorBoxData := ⟨box885,![exp42,exp42,exp42],![exp46,exp46,exp46],![exp44,exp44,exp44]⟩
theorem data885_lower_valid : ∀ j, (data885.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data885_upper_valid : ∀ j, (data885.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data885_center_valid : ∀ j, (data885.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp44_valid
  · exact exp44_valid
theorem margin885 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data885 25 := by decide +kernel
theorem positive885 {q : EdgeTriple} (hq : q ∈ box885.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data885 25
    data885_lower_valid data885_upper_valid data885_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin885 hq

def box886 : LogBox := ⟨![(8035/2048 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(17677/4096 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data886 : S1TaylorBoxData := ⟨box886,![exp46,exp38,exp38],![exp50,exp42,exp42],![exp48,exp40,exp40]⟩
theorem data886_lower_valid : ∀ j, (data886.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data886_upper_valid : ∀ j, (data886.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data886_center_valid : ∀ j, (data886.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin886 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data886 25 := by decide +kernel
theorem positive886 {q : EdgeTriple} (hq : q ∈ box886.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data886 25
    data886_lower_valid data886_upper_valid data886_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin886 hq

def box887 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)]⟩
def data887 : S1TaylorBoxData := ⟨box887,![exp46,exp42,exp38],![exp50,exp46,exp42],![exp48,exp44,exp40]⟩
theorem data887_lower_valid : ∀ j, (data887.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data887_upper_valid : ∀ j, (data887.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data887_center_valid : ∀ j, (data887.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp40_valid
theorem margin887 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data887 25 := by decide +kernel
theorem positive887 {q : EdgeTriple} (hq : q ∈ box887.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data887 25
    data887_lower_valid data887_upper_valid data887_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin887 hq

def box888 : LogBox := ⟨![(8035/2048 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)],![(17677/4096 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data888 : S1TaylorBoxData := ⟨box888,![exp46,exp42,exp42],![exp50,exp46,exp46],![exp48,exp44,exp44]⟩
theorem data888_lower_valid : ∀ j, (data888.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data888_upper_valid : ∀ j, (data888.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data888_center_valid : ∀ j, (data888.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp44_valid
  · exact exp44_valid
theorem margin888 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data888 25 := by decide +kernel
theorem positive888 {q : EdgeTriple} (hq : q ∈ box888.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data888 25
    data888_lower_valid data888_upper_valid data888_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin888 hq

def box889 : LogBox := ⟨![(17677/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)],![(4821/1024 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data889 : S1TaylorBoxData := ⟨box889,![exp50,exp38,exp38],![exp54,exp42,exp42],![exp52,exp40,exp40]⟩
theorem data889_lower_valid : ∀ j, (data889.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data889_upper_valid : ∀ j, (data889.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data889_center_valid : ∀ j, (data889.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp40_valid
  · exact exp40_valid
theorem margin889 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data889 25 := by decide +kernel
theorem positive889 {q : EdgeTriple} (hq : q ∈ box889.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data889 25
    data889_lower_valid data889_upper_valid data889_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin889 hq

def box890 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(1607/512 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)]⟩
def data890 : S1TaylorBoxData := ⟨box890,![exp50,exp42,exp38],![exp54,exp46,exp42],![exp52,exp44,exp40]⟩
theorem data890_lower_valid : ∀ j, (data890.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp38_valid
theorem data890_upper_valid : ∀ j, (data890.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data890_center_valid : ∀ j, (data890.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp40_valid
theorem margin890 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data890 25 := by decide +kernel
theorem positive890 {q : EdgeTriple} (hq : q ∈ box890.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data890 25
    data890_lower_valid data890_upper_valid data890_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin890 hq

def box891 : LogBox := ⟨![(17677/4096 : ℚ),(14463/4096 : ℚ),(14463/4096 : ℚ)],![(4821/1024 : ℚ),(8035/2048 : ℚ),(8035/2048 : ℚ)]⟩
def data891 : S1TaylorBoxData := ⟨box891,![exp50,exp42,exp42],![exp54,exp46,exp46],![exp52,exp44,exp44]⟩
theorem data891_lower_valid : ∀ j, (data891.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp42_valid
  · exact exp42_valid
theorem data891_upper_valid : ∀ j, (data891.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp46_valid
  · exact exp46_valid
theorem data891_center_valid : ∀ j, (data891.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp44_valid
  · exact exp44_valid
theorem margin891 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data891 25 := by decide +kernel
theorem positive891 {q : EdgeTriple} (hq : q ∈ box891.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data891 25
    data891_lower_valid data891_upper_valid data891_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin891 hq

def box892 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data892 : S1TaylorBoxData := ⟨box892,![exp46,exp46,exp38],![exp50,exp50,exp42],![exp48,exp48,exp40]⟩
theorem data892_lower_valid : ∀ j, (data892.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data892_upper_valid : ∀ j, (data892.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp42_valid
theorem data892_center_valid : ∀ j, (data892.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp40_valid
theorem margin892 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data892 25 := by decide +kernel
theorem positive892 {q : EdgeTriple} (hq : q ∈ box892.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data892 25
    data892_lower_valid data892_upper_valid data892_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin892 hq

def box893 : LogBox := ⟨![(8035/2048 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)],![(17677/4096 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data893 : S1TaylorBoxData := ⟨box893,![exp46,exp46,exp42],![exp50,exp50,exp46],![exp48,exp48,exp44]⟩
theorem data893_lower_valid : ∀ j, (data893.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data893_upper_valid : ∀ j, (data893.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data893_center_valid : ∀ j, (data893.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp48_valid
  · exact exp48_valid
  · exact exp44_valid
theorem margin893 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data893 25 := by decide +kernel
theorem positive893 {q : EdgeTriple} (hq : q ∈ box893.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data893 25
    data893_lower_valid data893_upper_valid data893_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin893 hq

def box894 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(1607/512 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(14463/4096 : ℚ)]⟩
def data894 : S1TaylorBoxData := ⟨box894,![exp50,exp46,exp38],![exp54,exp50,exp42],![exp52,exp48,exp40]⟩
theorem data894_lower_valid : ∀ j, (data894.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp38_valid
theorem data894_upper_valid : ∀ j, (data894.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp42_valid
theorem data894_center_valid : ∀ j, (data894.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp40_valid
theorem margin894 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data894 25 := by decide +kernel
theorem positive894 {q : EdgeTriple} (hq : q ∈ box894.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data894 25
    data894_lower_valid data894_upper_valid data894_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin894 hq

def box895 : LogBox := ⟨![(17677/4096 : ℚ),(8035/2048 : ℚ),(14463/4096 : ℚ)],![(4821/1024 : ℚ),(17677/4096 : ℚ),(8035/2048 : ℚ)]⟩
def data895 : S1TaylorBoxData := ⟨box895,![exp50,exp46,exp42],![exp54,exp50,exp46],![exp52,exp48,exp44]⟩
theorem data895_lower_valid : ∀ j, (data895.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp50_valid
  · exact exp46_valid
  · exact exp42_valid
theorem data895_upper_valid : ∀ j, (data895.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp54_valid
  · exact exp50_valid
  · exact exp46_valid
theorem data895_center_valid : ∀ j, (data895.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp52_valid
  · exact exp48_valid
  · exact exp44_valid
theorem margin895 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data895 25 := by decide +kernel
theorem positive895 {q : EdgeTriple} (hq : q ∈ box895.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data895 25
    data895_lower_valid data895_upper_valid data895_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin895 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

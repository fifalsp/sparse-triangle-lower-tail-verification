import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box400 : LogBox := ⟨![(14463/4096 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data400 : S1TaylorBoxData := ⟨box400,![exp42,exp22,exp0],![exp46,exp26,exp4],![exp44,exp24,exp2]⟩
theorem data400_lower_valid : ∀ j, (data400.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data400_upper_valid : ∀ j, (data400.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data400_center_valid : ∀ j, (data400.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin400 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data400 25 := by decide +kernel
theorem positive400 {q : EdgeTriple} (hq : q ∈ box400.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data400 25
    data400_lower_valid data400_upper_valid data400_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin400 hq

def box401 : LogBox := ⟨![(14463/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data401 : S1TaylorBoxData := ⟨box401,![exp42,exp22,exp4],![exp46,exp26,exp10],![exp44,exp24,exp6]⟩
theorem data401_lower_valid : ∀ j, (data401.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data401_upper_valid : ∀ j, (data401.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data401_center_valid : ∀ j, (data401.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin401 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data401 25 := by decide +kernel
theorem positive401 {q : EdgeTriple} (hq : q ∈ box401.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data401 25
    data401_lower_valid data401_upper_valid data401_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin401 hq

def box402 : LogBox := ⟨![(14463/4096 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data402 : S1TaylorBoxData := ⟨box402,![exp42,exp26,exp0],![exp46,exp30,exp4],![exp44,exp28,exp2]⟩
theorem data402_lower_valid : ∀ j, (data402.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data402_upper_valid : ∀ j, (data402.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data402_center_valid : ∀ j, (data402.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin402 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data402 25 := by decide +kernel
theorem positive402 {q : EdgeTriple} (hq : q ∈ box402.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data402 25
    data402_lower_valid data402_upper_valid data402_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin402 hq

def box403 : LogBox := ⟨![(14463/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data403 : S1TaylorBoxData := ⟨box403,![exp42,exp26,exp4],![exp46,exp30,exp10],![exp44,exp28,exp6]⟩
theorem data403_lower_valid : ∀ j, (data403.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data403_upper_valid : ∀ j, (data403.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data403_center_valid : ∀ j, (data403.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin403 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data403 25 := by decide +kernel
theorem positive403 {q : EdgeTriple} (hq : q ∈ box403.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data403 25
    data403_lower_valid data403_upper_valid data403_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin403 hq

def box404 : LogBox := ⟨![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(14463/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data404 : S1TaylorBoxData := ⟨box404,![exp38,exp22,exp10],![exp42,exp26,exp18],![exp40,exp24,exp14]⟩
theorem data404_lower_valid : ∀ j, (data404.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data404_upper_valid : ∀ j, (data404.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data404_center_valid : ∀ j, (data404.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin404 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data404 25 := by decide +kernel
theorem positive404 {q : EdgeTriple} (hq : q ∈ box404.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data404 25
    data404_lower_valid data404_upper_valid data404_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin404 hq

def box405 : LogBox := ⟨![(1607/512 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(14463/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data405 : S1TaylorBoxData := ⟨box405,![exp38,exp22,exp18],![exp42,exp26,exp22],![exp40,exp24,exp20]⟩
theorem data405_lower_valid : ∀ j, (data405.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data405_upper_valid : ∀ j, (data405.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data405_center_valid : ∀ j, (data405.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin405 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data405 25 := by decide +kernel
theorem positive405 {q : EdgeTriple} (hq : q ∈ box405.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data405 25
    data405_lower_valid data405_upper_valid data405_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin405 hq

def box406 : LogBox := ⟨![(1607/512 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(14463/4096 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data406 : S1TaylorBoxData := ⟨box406,![exp38,exp26,exp10],![exp42,exp30,exp18],![exp40,exp28,exp14]⟩
theorem data406_lower_valid : ∀ j, (data406.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data406_upper_valid : ∀ j, (data406.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data406_center_valid : ∀ j, (data406.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin406 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data406 25 := by decide +kernel
theorem positive406 {q : EdgeTriple} (hq : q ∈ box406.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data406 25
    data406_lower_valid data406_upper_valid data406_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin406 hq

def box407 : LogBox := ⟨![(1607/512 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(14463/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data407 : S1TaylorBoxData := ⟨box407,![exp38,exp26,exp18],![exp42,exp30,exp22],![exp40,exp28,exp20]⟩
theorem data407_lower_valid : ∀ j, (data407.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data407_upper_valid : ∀ j, (data407.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data407_center_valid : ∀ j, (data407.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin407 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data407 25 := by decide +kernel
theorem positive407 {q : EdgeTriple} (hq : q ∈ box407.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data407 25
    data407_lower_valid data407_upper_valid data407_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin407 hq

def box408 : LogBox := ⟨![(14463/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data408 : S1TaylorBoxData := ⟨box408,![exp42,exp22,exp10],![exp46,exp26,exp18],![exp44,exp24,exp14]⟩
theorem data408_lower_valid : ∀ j, (data408.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data408_upper_valid : ∀ j, (data408.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data408_center_valid : ∀ j, (data408.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin408 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data408 25 := by decide +kernel
theorem positive408 {q : EdgeTriple} (hq : q ∈ box408.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data408 25
    data408_lower_valid data408_upper_valid data408_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin408 hq

def box409 : LogBox := ⟨![(14463/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(8035/2048 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data409 : S1TaylorBoxData := ⟨box409,![exp42,exp22,exp18],![exp46,exp26,exp22],![exp44,exp24,exp20]⟩
theorem data409_lower_valid : ∀ j, (data409.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data409_upper_valid : ∀ j, (data409.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data409_center_valid : ∀ j, (data409.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin409 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data409 25 := by decide +kernel
theorem positive409 {q : EdgeTriple} (hq : q ∈ box409.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data409 25
    data409_lower_valid data409_upper_valid data409_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin409 hq

def box410 : LogBox := ⟨![(14463/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)],![(8035/2048 : ℚ),(4821/2048 : ℚ),(4821/4096 : ℚ)]⟩
def data410 : S1TaylorBoxData := ⟨box410,![exp42,exp26,exp10],![exp46,exp30,exp18],![exp44,exp28,exp14]⟩
theorem data410_lower_valid : ∀ j, (data410.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data410_upper_valid : ∀ j, (data410.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp18_valid
theorem data410_center_valid : ∀ j, (data410.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp28_valid
  · exact exp14_valid
theorem margin410 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data410 25 := by decide +kernel
theorem positive410 {q : EdgeTriple} (hq : q ∈ box410.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data410 25
    data410_lower_valid data410_upper_valid data410_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin410 hq

def box411 : LogBox := ⟨![(14463/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)],![(8035/2048 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)]⟩
def data411 : S1TaylorBoxData := ⟨box411,![exp42,exp26,exp18],![exp46,exp30,exp22],![exp44,exp28,exp20]⟩
theorem data411_lower_valid : ∀ j, (data411.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data411_upper_valid : ∀ j, (data411.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data411_center_valid : ∀ j, (data411.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp28_valid
  · exact exp20_valid
theorem margin411 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data411 25 := by decide +kernel
theorem positive411 {q : EdgeTriple} (hq : q ∈ box411.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data411 25
    data411_lower_valid data411_upper_valid data411_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin411 hq

def box412 : LogBox := ⟨![(1607/512 : ℚ),(4821/2048 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data412 : S1TaylorBoxData := ⟨box412,![exp38,exp30,exp0],![exp42,exp34,exp4],![exp40,exp32,exp2]⟩
theorem data412_lower_valid : ∀ j, (data412.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp0_valid
theorem data412_upper_valid : ∀ j, (data412.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data412_center_valid : ∀ j, (data412.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp32_valid
  · exact exp2_valid
theorem margin412 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data412 25 := by decide +kernel
theorem positive412 {q : EdgeTriple} (hq : q ∈ box412.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data412 25
    data412_lower_valid data412_upper_valid data412_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin412 hq

def box413 : LogBox := ⟨![(1607/512 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(11249/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data413 : S1TaylorBoxData := ⟨box413,![exp38,exp30,exp4],![exp42,exp34,exp10],![exp40,exp32,exp6]⟩
theorem data413_lower_valid : ∀ j, (data413.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data413_upper_valid : ∀ j, (data413.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp34_valid
  · exact exp10_valid
theorem data413_center_valid : ∀ j, (data413.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp32_valid
  · exact exp6_valid
theorem margin413 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data413 25 := by decide +kernel
theorem positive413 {q : EdgeTriple} (hq : q ∈ box413.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data413 25
    data413_lower_valid data413_upper_valid data413_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin413 hq

def box414 : LogBox := ⟨![(1607/512 : ℚ),(11249/4096 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)]⟩
def data414 : S1TaylorBoxData := ⟨box414,![exp38,exp34,exp0],![exp42,exp38,exp4],![exp40,exp36,exp2]⟩
theorem data414_lower_valid : ∀ j, (data414.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp0_valid
theorem data414_upper_valid : ∀ j, (data414.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data414_center_valid : ∀ j, (data414.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp36_valid
  · exact exp2_valid
theorem margin414 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data414 25 := by decide +kernel
theorem positive414 {q : EdgeTriple} (hq : q ∈ box414.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data414 25
    data414_lower_valid data414_upper_valid data414_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin414 hq

def box415 : LogBox := ⟨![(1607/512 : ℚ),(11249/4096 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/2048 : ℚ)]⟩
def data415 : S1TaylorBoxData := ⟨box415,![exp38,exp34,exp4],![exp42,exp38,exp10],![exp40,exp36,exp6]⟩
theorem data415_lower_valid : ∀ j, (data415.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp34_valid
  · exact exp4_valid
theorem data415_upper_valid : ∀ j, (data415.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp10_valid
theorem data415_center_valid : ∀ j, (data415.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp36_valid
  · exact exp6_valid
theorem margin415 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data415 25 := by decide +kernel
theorem positive415 {q : EdgeTriple} (hq : q ∈ box415.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data415 25
    data415_lower_valid data415_upper_valid data415_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin415 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

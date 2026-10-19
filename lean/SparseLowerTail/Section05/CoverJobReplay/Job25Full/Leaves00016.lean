import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box256 : LogBox := ⟨![(4821/2048 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(11249/4096 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data256 : S1TaylorBoxData := ⟨box256,![exp30,exp18,exp10],![exp34,exp22,exp18],![exp32,exp20,exp14]⟩
theorem data256_lower_valid : ∀ j, (data256.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data256_upper_valid : ∀ j, (data256.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data256_center_valid : ∀ j, (data256.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin256 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data256 25 := by decide +kernel
theorem positive256 {q : EdgeTriple} (hq : q ∈ box256.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data256 25
    data256_lower_valid data256_upper_valid data256_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin256 hq

def box257 : LogBox := ⟨![(4821/2048 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(11249/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data257 : S1TaylorBoxData := ⟨box257,![exp30,exp18,exp18],![exp34,exp22,exp22],![exp32,exp20,exp20]⟩
theorem data257_lower_valid : ∀ j, (data257.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data257_upper_valid : ∀ j, (data257.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data257_center_valid : ∀ j, (data257.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin257 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data257 25 := by decide +kernel
theorem positive257 {q : EdgeTriple} (hq : q ∈ box257.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data257 25
    data257_lower_valid data257_upper_valid data257_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin257 hq

def box258 : LogBox := ⟨![(11249/4096 : ℚ),(1607/2048 : ℚ),(1607/2048 : ℚ)],![(1607/512 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data258 : S1TaylorBoxData := ⟨box258,![exp34,exp10,exp10],![exp38,exp18,exp18],![exp36,exp14,exp14]⟩
theorem data258_lower_valid : ∀ j, (data258.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp10_valid
  · exact exp10_valid
theorem data258_upper_valid : ∀ j, (data258.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data258_center_valid : ∀ j, (data258.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp14_valid
  · exact exp14_valid
theorem margin258 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data258 25 := by decide +kernel
theorem positive258 {q : EdgeTriple} (hq : q ∈ box258.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data258 25
    data258_lower_valid data258_upper_valid data258_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin258 hq

def box259 : LogBox := ⟨![(11249/4096 : ℚ),(4821/4096 : ℚ),(1607/2048 : ℚ)],![(1607/512 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)]⟩
def data259 : S1TaylorBoxData := ⟨box259,![exp34,exp18,exp10],![exp38,exp22,exp18],![exp36,exp20,exp14]⟩
theorem data259_lower_valid : ∀ j, (data259.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp18_valid
  · exact exp10_valid
theorem data259_upper_valid : ∀ j, (data259.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data259_center_valid : ∀ j, (data259.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp20_valid
  · exact exp14_valid
theorem margin259 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data259 25 := by decide +kernel
theorem positive259 {q : EdgeTriple} (hq : q ∈ box259.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data259 25
    data259_lower_valid data259_upper_valid data259_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin259 hq

def box260 : LogBox := ⟨![(11249/4096 : ℚ),(4821/4096 : ℚ),(4821/4096 : ℚ)],![(1607/512 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)]⟩
def data260 : S1TaylorBoxData := ⟨box260,![exp34,exp18,exp18],![exp38,exp22,exp22],![exp36,exp20,exp20]⟩
theorem data260_lower_valid : ∀ j, (data260.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp34_valid
  · exact exp18_valid
  · exact exp18_valid
theorem data260_upper_valid : ∀ j, (data260.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data260_center_valid : ∀ j, (data260.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp36_valid
  · exact exp20_valid
  · exact exp20_valid
theorem margin260 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data260 25 := by decide +kernel
theorem positive260 {q : EdgeTriple} (hq : q ∈ box260.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data260 25
    data260_lower_valid data260_upper_valid data260_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin260 hq

def box261 : LogBox := ⟨![(1607/1024 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(14463/8192 : ℚ),(14463/8192 : ℚ),(1607/4096 : ℚ)]⟩
def data261 : S1TaylorBoxData := ⟨box261,![exp22,exp22,exp0],![exp24,exp24,exp4],![exp23,exp23,exp2]⟩
theorem data261_lower_valid : ∀ j, (data261.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data261_upper_valid : ∀ j, (data261.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp24_valid
  · exact exp4_valid
theorem data261_center_valid : ∀ j, (data261.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp23_valid
  · exact exp2_valid
theorem margin261 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data261 25 := by decide +kernel
theorem positive261 {q : EdgeTriple} (hq : q ∈ box261.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data261 25
    data261_lower_valid data261_upper_valid data261_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin261 hq

def box262 : LogBox := ⟨![(14463/8192 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(8035/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data262 : S1TaylorBoxData := ⟨box262,![exp24,exp22,exp0],![exp26,exp26,exp4],![exp25,exp24,exp2]⟩
theorem data262_lower_valid : ∀ j, (data262.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data262_upper_valid : ∀ j, (data262.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data262_center_valid : ∀ j, (data262.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin262 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data262 25 := by decide +kernel
theorem positive262 {q : EdgeTriple} (hq : q ∈ box262.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data262 25
    data262_lower_valid data262_upper_valid data262_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin262 hq

def box263 : LogBox := ⟨![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(14463/8192 : ℚ),(14463/8192 : ℚ),(1607/2048 : ℚ)]⟩
def data263 : S1TaylorBoxData := ⟨box263,![exp22,exp22,exp4],![exp24,exp24,exp10],![exp23,exp23,exp6]⟩
theorem data263_lower_valid : ∀ j, (data263.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data263_upper_valid : ∀ j, (data263.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp24_valid
  · exact exp10_valid
theorem data263_center_valid : ∀ j, (data263.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp23_valid
  · exact exp23_valid
  · exact exp6_valid
theorem margin263 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data263 25 := by decide +kernel
theorem positive263 {q : EdgeTriple} (hq : q ∈ box263.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data263 25
    data263_lower_valid data263_upper_valid data263_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin263 hq

def box264 : LogBox := ⟨![(14463/8192 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(8035/4096 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data264 : S1TaylorBoxData := ⟨box264,![exp24,exp22,exp4],![exp26,exp26,exp10],![exp25,exp24,exp6]⟩
theorem data264_lower_valid : ∀ j, (data264.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data264_upper_valid : ∀ j, (data264.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data264_center_valid : ∀ j, (data264.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp25_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin264 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data264 25 := by decide +kernel
theorem positive264 {q : EdgeTriple} (hq : q ∈ box264.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data264 25
    data264_lower_valid data264_upper_valid data264_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin264 hq

def box265 : LogBox := ⟨![(8035/4096 : ℚ),(1607/1024 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data265 : S1TaylorBoxData := ⟨box265,![exp26,exp22,exp0],![exp30,exp26,exp4],![exp28,exp24,exp2]⟩
theorem data265_lower_valid : ∀ j, (data265.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp0_valid
theorem data265_upper_valid : ∀ j, (data265.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data265_center_valid : ∀ j, (data265.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp24_valid
  · exact exp2_valid
theorem margin265 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data265 25 := by decide +kernel
theorem positive265 {q : EdgeTriple} (hq : q ∈ box265.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data265 25
    data265_lower_valid data265_upper_valid data265_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin265 hq

def box266 : LogBox := ⟨![(8035/4096 : ℚ),(1607/1024 : ℚ),(1607/4096 : ℚ)],![(4821/2048 : ℚ),(8035/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data266 : S1TaylorBoxData := ⟨box266,![exp26,exp22,exp4],![exp30,exp26,exp10],![exp28,exp24,exp6]⟩
theorem data266_lower_valid : ∀ j, (data266.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp4_valid
theorem data266_upper_valid : ∀ j, (data266.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp10_valid
theorem data266_center_valid : ∀ j, (data266.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp24_valid
  · exact exp6_valid
theorem margin266 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data266 25 := by decide +kernel
theorem positive266 {q : EdgeTriple} (hq : q ∈ box266.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data266 25
    data266_lower_valid data266_upper_valid data266_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin266 hq

def box267 : LogBox := ⟨![(8035/4096 : ℚ),(8035/4096 : ℚ),(0/1 : ℚ)],![(4821/2048 : ℚ),(4821/2048 : ℚ),(1607/4096 : ℚ)]⟩
def data267 : S1TaylorBoxData := ⟨box267,![exp26,exp26,exp0],![exp30,exp30,exp4],![exp28,exp28,exp2]⟩
theorem data267_lower_valid : ∀ j, (data267.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp0_valid
theorem data267_upper_valid : ∀ j, (data267.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp4_valid
theorem data267_center_valid : ∀ j, (data267.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp28_valid
  · exact exp2_valid
theorem margin267 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data267 25 := by decide +kernel
theorem positive267 {q : EdgeTriple} (hq : q ∈ box267.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data267 25
    data267_lower_valid data267_upper_valid data267_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin267 hq

def box268 : LogBox := ⟨![(8035/4096 : ℚ),(8035/4096 : ℚ),(1607/4096 : ℚ)],![(4821/2048 : ℚ),(4821/2048 : ℚ),(1607/2048 : ℚ)]⟩
def data268 : S1TaylorBoxData := ⟨box268,![exp26,exp26,exp4],![exp30,exp30,exp10],![exp28,exp28,exp6]⟩
theorem data268_lower_valid : ∀ j, (data268.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp4_valid
theorem data268_upper_valid : ∀ j, (data268.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp30_valid
  · exact exp10_valid
theorem data268_center_valid : ∀ j, (data268.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp28_valid
  · exact exp6_valid
theorem margin268 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data268 25 := by decide +kernel
theorem positive268 {q : EdgeTriple} (hq : q ∈ box268.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data268 25
    data268_lower_valid data268_upper_valid data268_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin268 hq

def box269 : LogBox := ⟨![(1607/1024 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(8035/4096 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data269 : S1TaylorBoxData := ⟨box269,![exp22,exp22,exp10],![exp26,exp26,exp18],![exp24,exp24,exp14]⟩
theorem data269_lower_valid : ∀ j, (data269.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data269_upper_valid : ∀ j, (data269.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data269_center_valid : ∀ j, (data269.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin269 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data269 25 := by decide +kernel
theorem positive269 {q : EdgeTriple} (hq : q ∈ box269.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data269 25
    data269_lower_valid data269_upper_valid data269_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin269 hq

def box270 : LogBox := ⟨![(1607/1024 : ℚ),(1607/1024 : ℚ),(4821/4096 : ℚ)],![(8035/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)]⟩
def data270 : S1TaylorBoxData := ⟨box270,![exp22,exp22,exp18],![exp26,exp26,exp22],![exp24,exp24,exp20]⟩
theorem data270_lower_valid : ∀ j, (data270.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp22_valid
  · exact exp22_valid
  · exact exp18_valid
theorem data270_upper_valid : ∀ j, (data270.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data270_center_valid : ∀ j, (data270.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp24_valid
  · exact exp24_valid
  · exact exp20_valid
theorem margin270 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data270 25 := by decide +kernel
theorem positive270 {q : EdgeTriple} (hq : q ∈ box270.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data270 25
    data270_lower_valid data270_upper_valid data270_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin270 hq

def box271 : LogBox := ⟨![(8035/4096 : ℚ),(1607/1024 : ℚ),(1607/2048 : ℚ)],![(4821/2048 : ℚ),(8035/4096 : ℚ),(4821/4096 : ℚ)]⟩
def data271 : S1TaylorBoxData := ⟨box271,![exp26,exp22,exp10],![exp30,exp26,exp18],![exp28,exp24,exp14]⟩
theorem data271_lower_valid : ∀ j, (data271.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp26_valid
  · exact exp22_valid
  · exact exp10_valid
theorem data271_upper_valid : ∀ j, (data271.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp30_valid
  · exact exp26_valid
  · exact exp18_valid
theorem data271_center_valid : ∀ j, (data271.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp28_valid
  · exact exp24_valid
  · exact exp14_valid
theorem margin271 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data271 25 := by decide +kernel
theorem positive271 {q : EdgeTriple} (hq : q ∈ box271.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data271 25
    data271_lower_valid data271_upper_valid data271_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin271 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

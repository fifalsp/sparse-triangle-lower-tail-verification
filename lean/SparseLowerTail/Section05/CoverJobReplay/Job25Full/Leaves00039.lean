import SparseLowerTail.Section05.CoverRefinedJobTaylorBox
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0000
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Endpoints0001

/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace SparseLowerTail.Section05.CoverJobReplay.Job25Full
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def box624 : LogBox := ⟨![(11249/2048 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data624 : S1TaylorBoxData := ⟨box624,![exp62,exp22,exp22],![exp66,exp26,exp26],![exp64,exp24,exp24]⟩
theorem data624_lower_valid : ∀ j, (data624.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data624_upper_valid : ∀ j, (data624.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data624_center_valid : ∀ j, (data624.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin624 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data624 25 := by decide +kernel
theorem positive624 {q : EdgeTriple} (hq : q ∈ box624.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data624 25
    data624_lower_valid data624_upper_valid data624_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin624 hq

def box625 : LogBox := ⟨![(11249/2048 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data625 : S1TaylorBoxData := ⟨box625,![exp62,exp26,exp22],![exp66,exp30,exp30],![exp64,exp28,exp26]⟩
theorem data625_lower_valid : ∀ j, (data625.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data625_upper_valid : ∀ j, (data625.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data625_center_valid : ∀ j, (data625.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin625 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data625 25 := by decide +kernel
theorem positive625 {q : EdgeTriple} (hq : q ∈ box625.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data625 25
    data625_lower_valid data625_upper_valid data625_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin625 hq

def box626 : LogBox := ⟨![(24105/4096 : ℚ),(1607/1024 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(8035/4096 : ℚ),(8035/4096 : ℚ)]⟩
def data626 : S1TaylorBoxData := ⟨box626,![exp66,exp22,exp22],![exp70,exp26,exp26],![exp68,exp24,exp24]⟩
theorem data626_lower_valid : ∀ j, (data626.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp22_valid
  · exact exp22_valid
theorem data626_upper_valid : ∀ j, (data626.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp26_valid
  · exact exp26_valid
theorem data626_center_valid : ∀ j, (data626.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp24_valid
  · exact exp24_valid
theorem margin626 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data626 25 := by decide +kernel
theorem positive626 {q : EdgeTriple} (hq : q ∈ box626.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data626 25
    data626_lower_valid data626_upper_valid data626_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin626 hq

def box627 : LogBox := ⟨![(24105/4096 : ℚ),(8035/4096 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)]⟩
def data627 : S1TaylorBoxData := ⟨box627,![exp66,exp26,exp22],![exp70,exp30,exp30],![exp68,exp28,exp26]⟩
theorem data627_lower_valid : ∀ j, (data627.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp26_valid
  · exact exp22_valid
theorem data627_upper_valid : ∀ j, (data627.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data627_center_valid : ∀ j, (data627.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp28_valid
  · exact exp26_valid
theorem margin627 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data627 25 := by decide +kernel
theorem positive627 {q : EdgeTriple} (hq : q ∈ box627.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data627 25
    data627_lower_valid data627_upper_valid data627_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin627 hq

def box628 : LogBox := ⟨![(11249/2048 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data628 : S1TaylorBoxData := ⟨box628,![exp62,exp30,exp22],![exp66,exp34,exp30],![exp64,exp32,exp26]⟩
theorem data628_lower_valid : ∀ j, (data628.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data628_upper_valid : ∀ j, (data628.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data628_center_valid : ∀ j, (data628.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin628 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data628 25 := by decide +kernel
theorem positive628 {q : EdgeTriple} (hq : q ∈ box628.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data628 25
    data628_lower_valid data628_upper_valid data628_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin628 hq

def box629 : LogBox := ⟨![(11249/2048 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(24105/4096 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data629 : S1TaylorBoxData := ⟨box629,![exp62,exp34,exp22],![exp66,exp38,exp30],![exp64,exp36,exp26]⟩
theorem data629_lower_valid : ∀ j, (data629.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data629_upper_valid : ∀ j, (data629.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data629_center_valid : ∀ j, (data629.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin629 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data629 25 := by decide +kernel
theorem positive629 {q : EdgeTriple} (hq : q ∈ box629.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data629 25
    data629_lower_valid data629_upper_valid data629_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin629 hq

def box630 : LogBox := ⟨![(24105/4096 : ℚ),(4821/2048 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)]⟩
def data630 : S1TaylorBoxData := ⟨box630,![exp66,exp30,exp22],![exp70,exp34,exp30],![exp68,exp32,exp26]⟩
theorem data630_lower_valid : ∀ j, (data630.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp22_valid
theorem data630_upper_valid : ∀ j, (data630.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data630_center_valid : ∀ j, (data630.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp32_valid
  · exact exp26_valid
theorem margin630 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data630 25 := by decide +kernel
theorem positive630 {q : EdgeTriple} (hq : q ∈ box630.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data630 25
    data630_lower_valid data630_upper_valid data630_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin630 hq

def box631 : LogBox := ⟨![(24105/4096 : ℚ),(11249/4096 : ℚ),(1607/1024 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(4821/2048 : ℚ)]⟩
def data631 : S1TaylorBoxData := ⟨box631,![exp66,exp34,exp22],![exp70,exp38,exp30],![exp68,exp36,exp26]⟩
theorem data631_lower_valid : ∀ j, (data631.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp22_valid
theorem data631_upper_valid : ∀ j, (data631.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp38_valid
  · exact exp30_valid
theorem data631_center_valid : ∀ j, (data631.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp36_valid
  · exact exp26_valid
theorem margin631 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data631 25 := by decide +kernel
theorem positive631 {q : EdgeTriple} (hq : q ∈ box631.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data631 25
    data631_lower_valid data631_upper_valid data631_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin631 hq

def box632 : LogBox := ⟨![(11249/2048 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data632 : S1TaylorBoxData := ⟨box632,![exp62,exp30,exp30],![exp66,exp34,exp34],![exp64,exp32,exp32]⟩
theorem data632_lower_valid : ∀ j, (data632.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data632_upper_valid : ∀ j, (data632.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data632_center_valid : ∀ j, (data632.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin632 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data632 25 := by decide +kernel
theorem positive632 {q : EdgeTriple} (hq : q ∈ box632.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data632 25
    data632_lower_valid data632_upper_valid data632_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin632 hq

def box633 : LogBox := ⟨![(11249/2048 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(24105/4096 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data633 : S1TaylorBoxData := ⟨box633,![exp62,exp34,exp30],![exp66,exp38,exp38],![exp64,exp36,exp34]⟩
theorem data633_lower_valid : ∀ j, (data633.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp62_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data633_upper_valid : ∀ j, (data633.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data633_center_valid : ∀ j, (data633.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp64_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin633 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data633 25 := by decide +kernel
theorem positive633 {q : EdgeTriple} (hq : q ∈ box633.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data633 25
    data633_lower_valid data633_upper_valid data633_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin633 hq

def box634 : LogBox := ⟨![(24105/4096 : ℚ),(4821/2048 : ℚ),(4821/2048 : ℚ)],![(1607/256 : ℚ),(11249/4096 : ℚ),(11249/4096 : ℚ)]⟩
def data634 : S1TaylorBoxData := ⟨box634,![exp66,exp30,exp30],![exp70,exp34,exp34],![exp68,exp32,exp32]⟩
theorem data634_lower_valid : ∀ j, (data634.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp30_valid
  · exact exp30_valid
theorem data634_upper_valid : ∀ j, (data634.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp34_valid
  · exact exp34_valid
theorem data634_center_valid : ∀ j, (data634.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp32_valid
  · exact exp32_valid
theorem margin634 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data634 25 := by decide +kernel
theorem positive634 {q : EdgeTriple} (hq : q ∈ box634.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data634 25
    data634_lower_valid data634_upper_valid data634_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin634 hq

def box635 : LogBox := ⟨![(24105/4096 : ℚ),(11249/4096 : ℚ),(4821/2048 : ℚ)],![(1607/256 : ℚ),(1607/512 : ℚ),(1607/512 : ℚ)]⟩
def data635 : S1TaylorBoxData := ⟨box635,![exp66,exp34,exp30],![exp70,exp38,exp38],![exp68,exp36,exp34]⟩
theorem data635_lower_valid : ∀ j, (data635.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp66_valid
  · exact exp34_valid
  · exact exp30_valid
theorem data635_upper_valid : ∀ j, (data635.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp70_valid
  · exact exp38_valid
  · exact exp38_valid
theorem data635_center_valid : ∀ j, (data635.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp68_valid
  · exact exp36_valid
  · exact exp34_valid
theorem margin635 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data635 25 := by decide +kernel
theorem positive635 {q : EdgeTriple} (hq : q ∈ box635.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data635 25
    data635_lower_valid data635_upper_valid data635_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin635 hq

def box636 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data636 : S1TaylorBoxData := ⟨box636,![exp38,exp38,exp0],![exp42,exp42,exp4],![exp40,exp40,exp2]⟩
theorem data636_lower_valid : ∀ j, (data636.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data636_upper_valid : ∀ j, (data636.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data636_center_valid : ∀ j, (data636.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin636 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data636 25 := by decide +kernel
theorem positive636 {q : EdgeTriple} (hq : q ∈ box636.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data636 25
    data636_lower_valid data636_upper_valid data636_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin636 hq

def box637 : LogBox := ⟨![(1607/512 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(14463/4096 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data637 : S1TaylorBoxData := ⟨box637,![exp38,exp38,exp4],![exp42,exp42,exp10],![exp40,exp40,exp6]⟩
theorem data637_lower_valid : ∀ j, (data637.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp38_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data637_upper_valid : ∀ j, (data637.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data637_center_valid : ∀ j, (data637.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp40_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin637 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data637 25 := by decide +kernel
theorem positive637 {q : EdgeTriple} (hq : q ∈ box637.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data637 25
    data637_lower_valid data637_upper_valid data637_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin637 hq

def box638 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(0/1 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/4096 : ℚ)]⟩
def data638 : S1TaylorBoxData := ⟨box638,![exp42,exp38,exp0],![exp46,exp42,exp4],![exp44,exp40,exp2]⟩
theorem data638_lower_valid : ∀ j, (data638.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp0_valid
theorem data638_upper_valid : ∀ j, (data638.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp4_valid
theorem data638_center_valid : ∀ j, (data638.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp2_valid
theorem margin638 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data638 25 := by decide +kernel
theorem positive638 {q : EdgeTriple} (hq : q ∈ box638.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data638 25
    data638_lower_valid data638_upper_valid data638_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin638 hq

def box639 : LogBox := ⟨![(14463/4096 : ℚ),(1607/512 : ℚ),(1607/4096 : ℚ)],![(8035/2048 : ℚ),(14463/4096 : ℚ),(1607/2048 : ℚ)]⟩
def data639 : S1TaylorBoxData := ⟨box639,![exp42,exp38,exp4],![exp46,exp42,exp10],![exp44,exp40,exp6]⟩
theorem data639_lower_valid : ∀ j, (data639.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp42_valid
  · exact exp38_valid
  · exact exp4_valid
theorem data639_upper_valid : ∀ j, (data639.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp46_valid
  · exact exp42_valid
  · exact exp10_valid
theorem data639_center_valid : ∀ j, (data639.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp44_valid
  · exact exp40_valid
  · exact exp6_valid
theorem margin639 :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data639 25 := by decide +kernel
theorem positive639 {q : EdgeTriple} (hq : q ∈ box639.region) :
    0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell 25)) (CoverGeometry.cellLambda (CoverGeometry.nonapexCell 25)) (CoverGeometry.nonapexVertex 25) q :=
  RefinedCover.S1TaylorBoxData.job_positive data639 25
    data639_lower_valid data639_upper_valid data639_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin639 hq

end SparseLowerTail.Section05.CoverJobReplay.Job25Full

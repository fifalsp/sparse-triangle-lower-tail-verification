import SparseLowerTail.Section08.FamilyCompactReplay
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0000
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0001
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Endpoints0000

/-! Generated proposal data. Every theorem must pass the Lean kernel.
The full ABB neighborhood remains an explicit internal premise. -/
namespace SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def domain60 : ReplayBox 4 := ⟨![(39/10 : ℚ),(3/8 : ℚ),(9/16 : ℚ),(3/4 : ℚ)],![(23/5 : ℚ),(9/16 : ℚ),(3/4 : ℚ),(15/16 : ℚ)]⟩
def data60 : FamilyTaylorData :=
  ⟨parameter0,parameter1,![exp21,exp23,exp25],derivatives0,fun n => derivatives1 n.castSucc,(7/20 : ℚ)⟩
theorem data60_valid : data60.Valid := by
  refine {
    whole_valid := parameter0_valid, midpoint_valid := parameter1_valid,
    whole_checked := derivatives0_checked, center_checked := fun n => derivatives1_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp21_valid
    · exact exp23_valid
    · exact exp25_valid
  all_goals decide +kernel
def box60 : FamilyBoxCertificate := ⟨parameter0,derivatives0 0,![exp20,exp22,exp24],![exp22,exp24,exp26]⟩
theorem box60_valid : box60.Valid := by
  refine ⟨parameter0_valid,derivatives0_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp20_valid
    · exact exp22_valid
    · exact exp24_valid
  · intro j; fin_cases j
    · exact exp22_valid
    · exact exp24_valid
    · exact exp26_valid
def leaf60 : FamilyExteriorLeaf := ⟨data60,box60,![(3/32 : ℚ),(3/32 : ℚ),(3/32 : ℚ)],![(-19871250271112871807/1844674407370955161600 : ℚ),(-307507959406950030333/29514790517935282585600 : ℚ),(-37741126749669439251/3689348814741910323200 : ℚ)]⟩
theorem leaf60_valid : leaf60.Valid := by
  refine {
    data_valid := data60_valid, box_valid := box60_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion60 (_hABB : FamilyABBLocal) : ∀x,domain60.Contains x → familyCompactProperty x :=
  leaf60.compact_property leaf60_valid (by decide +kernel)

end SparseLowerTail.Section08.FamilyExteriorReplay.Smoke

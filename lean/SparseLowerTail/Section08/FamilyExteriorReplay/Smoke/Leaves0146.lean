import SparseLowerTail.Section08.FamilyCompactReplay
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0004
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0005
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Endpoints0000

/-! Generated proposal data. Every theorem must pass the Lean kernel.
The full ABB neighborhood remains an explicit internal premise. -/
namespace SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def domain2350 : ReplayBox 4 := ⟨![(39/10 : ℚ),(21/8 : ℚ),(3/1 : ℚ),(15/4 : ℚ)],![(163/40 : ℚ),(3/1 : ℚ),(15/4 : ℚ),(9/2 : ℚ)]⟩
def data2350 : FamilyTaylorData :=
  ⟨parameter4,parameter5,![exp28,exp30,exp36],derivatives4,fun n => derivatives5 n.castSucc,(7/80 : ℚ)⟩
theorem data2350_valid : data2350.Valid := by
  refine {
    whole_valid := parameter4_valid, midpoint_valid := parameter5_valid,
    whole_checked := derivatives4_checked, center_checked := fun n => derivatives5_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp28_valid
    · exact exp30_valid
    · exact exp36_valid
  all_goals decide +kernel
def box2350 : FamilyBoxCertificate := ⟨parameter4,derivatives4 0,![exp27,exp29,exp31],![exp29,exp31,exp38]⟩
theorem box2350_valid : box2350.Valid := by
  refine ⟨parameter4_valid,derivatives4_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp27_valid
    · exact exp29_valid
    · exact exp31_valid
  · intro j; fin_cases j
    · exact exp29_valid
    · exact exp31_valid
    · exact exp38_valid
def leaf2350 : FamilyExteriorLeaf := ⟨data2350,box2350,![(3/16 : ℚ),(3/8 : ℚ),(3/8 : ℚ)],![(-20839086985243918599/59029581035870565171200 : ℚ),(-430123806220840269/922337203685477580800 : ℚ),(-9365350242480250540833894777606095121/125150004838580702026867823720047575040000 : ℚ)]⟩
theorem leaf2350_valid : leaf2350.Valid := by
  refine {
    data_valid := data2350_valid, box_valid := box2350_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion2350 (_hABB : FamilyABBLocal) : ∀x,domain2350.Contains x → familyCompactProperty x :=
  leaf2350.compact_property leaf2350_valid (by decide +kernel)

end SparseLowerTail.Section08.FamilyExteriorReplay.Smoke

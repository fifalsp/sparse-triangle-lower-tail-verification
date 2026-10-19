import SparseLowerTail.Section08.FamilyCompactReplay
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0000
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0001
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0002
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0003
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Endpoints0000

/-! Generated proposal data. Every theorem must pass the Lean kernel.
The full ABB neighborhood remains an explicit internal premise. -/
namespace SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def domain0 : ReplayBox 4 := ⟨![(39/10 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(23/5 : ℚ),(3/16 : ℚ),(3/8 : ℚ),(3/8 : ℚ)]⟩
def data0 : FamilyTaylorData :=
  ⟨parameter0,parameter1,![exp5,exp17,exp17],derivatives0,fun n => derivatives1 n.castSucc,(7/20 : ℚ)⟩
theorem data0_valid : data0.Valid := by
  refine {
    whole_valid := parameter0_valid, midpoint_valid := parameter1_valid,
    whole_checked := derivatives0_checked, center_checked := fun n => derivatives1_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp5_valid
    · exact exp17_valid
    · exact exp17_valid
  all_goals decide +kernel
def box0 : FamilyBoxCertificate := ⟨parameter0,derivatives0 0,![exp0,exp0,exp0],![exp17,exp20,exp20]⟩
theorem box0_valid : box0.Valid := by
  refine ⟨parameter0_valid,derivatives0_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp0_valid
    · exact exp0_valid
    · exact exp0_valid
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp20_valid
    · exact exp20_valid
def leaf0 : FamilyExteriorLeaf := ⟨data0,box0,![(3/32 : ℚ),(3/16 : ℚ),(3/16 : ℚ)],![(-3905128296602659596417/59029581035870565171200 : ℚ),(-14926658134639932201/115292150460684697600 : ℚ),(-14926658134639932201/115292150460684697600 : ℚ)]⟩
theorem leaf0_valid : leaf0.Valid := by
  refine {
    data_valid := data0_valid, box_valid := box0_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion0 (_hABB : FamilyABBLocal) : ∀x,domain0.Contains x → familyCompactProperty x :=
  leaf0.compact_property leaf0_valid (by decide +kernel)

def domain1 : ReplayBox 4 := ⟨![(39/10 : ℚ),(3/16 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(23/5 : ℚ),(3/8 : ℚ),(3/8 : ℚ),(3/8 : ℚ)]⟩
def data1 : FamilyTaylorData :=
  ⟨parameter0,parameter1,![exp19,exp17,exp17],derivatives0,fun n => derivatives1 n.castSucc,(7/20 : ℚ)⟩
theorem data1_valid : data1.Valid := by
  refine {
    whole_valid := parameter0_valid, midpoint_valid := parameter1_valid,
    whole_checked := derivatives0_checked, center_checked := fun n => derivatives1_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp19_valid
    · exact exp17_valid
    · exact exp17_valid
  all_goals decide +kernel
def box1 : FamilyBoxCertificate := ⟨parameter0,derivatives0 0,![exp17,exp0,exp0],![exp20,exp20,exp20]⟩
theorem box1_valid : box1.Valid := by
  refine ⟨parameter0_valid,derivatives0_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp0_valid
    · exact exp0_valid
  · intro j; fin_cases j
    · exact exp20_valid
    · exact exp20_valid
    · exact exp20_valid
def leaf1 : FamilyExteriorLeaf := ⟨data1,box1,![(3/32 : ℚ),(3/16 : ℚ),(3/16 : ℚ)],![(-3075845856364917711423/59029581035870565171200 : ℚ),(-1528607944588845457899/14757395258967641292800 : ℚ),(-1528607944588845457899/14757395258967641292800 : ℚ)]⟩
theorem leaf1_valid : leaf1.Valid := by
  refine {
    data_valid := data1_valid, box_valid := box1_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion1 (_hABB : FamilyABBLocal) : ∀x,domain1.Contains x → familyCompactProperty x :=
  leaf1.compact_property leaf1_valid (by decide +kernel)

def domain2 : ReplayBox 4 := ⟨![(23/5 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(53/10 : ℚ),(3/16 : ℚ),(3/8 : ℚ),(3/8 : ℚ)]⟩
def data2 : FamilyTaylorData :=
  ⟨parameter2,parameter3,![exp5,exp17,exp17],derivatives2,fun n => derivatives3 n.castSucc,(7/20 : ℚ)⟩
theorem data2_valid : data2.Valid := by
  refine {
    whole_valid := parameter2_valid, midpoint_valid := parameter3_valid,
    whole_checked := derivatives2_checked, center_checked := fun n => derivatives3_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp5_valid
    · exact exp17_valid
    · exact exp17_valid
  all_goals decide +kernel
def box2 : FamilyBoxCertificate := ⟨parameter2,derivatives2 0,![exp0,exp0,exp0],![exp17,exp20,exp20]⟩
theorem box2_valid : box2.Valid := by
  refine ⟨parameter2_valid,derivatives2_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp0_valid
    · exact exp0_valid
    · exact exp0_valid
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp20_valid
    · exact exp20_valid
def leaf2 : FamilyExteriorLeaf := ⟨data2,box2,![(3/32 : ℚ),(3/16 : ℚ),(3/16 : ℚ)],![(-3772227968661783230469/59029581035870565171200 : ℚ),(-1833941604704579304657/14757395258967641292800 : ℚ),(-1833941604704579304657/14757395258967641292800 : ℚ)]⟩
theorem leaf2_valid : leaf2.Valid := by
  refine {
    data_valid := data2_valid, box_valid := box2_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion2 (_hABB : FamilyABBLocal) : ∀x,domain2.Contains x → familyCompactProperty x :=
  leaf2.compact_property leaf2_valid (by decide +kernel)

def domain3 : ReplayBox 4 := ⟨![(23/5 : ℚ),(3/16 : ℚ),(0/1 : ℚ),(0/1 : ℚ)],![(53/10 : ℚ),(3/8 : ℚ),(3/8 : ℚ),(3/8 : ℚ)]⟩
def data3 : FamilyTaylorData :=
  ⟨parameter2,parameter3,![exp19,exp17,exp17],derivatives2,fun n => derivatives3 n.castSucc,(7/20 : ℚ)⟩
theorem data3_valid : data3.Valid := by
  refine {
    whole_valid := parameter2_valid, midpoint_valid := parameter3_valid,
    whole_checked := derivatives2_checked, center_checked := fun n => derivatives3_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp19_valid
    · exact exp17_valid
    · exact exp17_valid
  all_goals decide +kernel
def box3 : FamilyBoxCertificate := ⟨parameter2,derivatives2 0,![exp17,exp0,exp0],![exp20,exp20,exp20]⟩
theorem box3_valid : box3.Valid := by
  refine ⟨parameter2_valid,derivatives2_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp0_valid
    · exact exp0_valid
  · intro j; fin_cases j
    · exact exp20_valid
    · exact exp20_valid
    · exact exp20_valid
def leaf3 : FamilyExteriorLeaf := ⟨data3,box3,![(3/32 : ℚ),(3/16 : ℚ),(3/16 : ℚ)],![(-2984614303352429678073/59029581035870565171200 : ℚ),(-366826151599626650889/3689348814741910323200 : ℚ),(-366826151599626650889/3689348814741910323200 : ℚ)]⟩
theorem leaf3_valid : leaf3.Valid := by
  refine {
    data_valid := data3_valid, box_valid := box3_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion3 (_hABB : FamilyABBLocal) : ∀x,domain3.Contains x → familyCompactProperty x :=
  leaf3.compact_property leaf3_valid (by decide +kernel)

def domain4 : ReplayBox 4 := ⟨![(39/10 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(3/8 : ℚ)],![(23/5 : ℚ),(3/16 : ℚ),(3/16 : ℚ),(3/4 : ℚ)]⟩
theorem conclusion4 (_hABB : FamilyABBLocal) : ∀x,domain4.Contains x → familyCompactProperty x :=
  familyCompactProperty_ordered_empty domain4 (by decide +kernel)

def domain5 : ReplayBox 4 := ⟨![(39/10 : ℚ),(0/1 : ℚ),(3/16 : ℚ),(3/8 : ℚ)],![(23/5 : ℚ),(3/16 : ℚ),(3/8 : ℚ),(3/4 : ℚ)]⟩
def data5 : FamilyTaylorData :=
  ⟨parameter0,parameter1,![exp5,exp19,exp22],derivatives0,fun n => derivatives1 n.castSucc,(7/20 : ℚ)⟩
theorem data5_valid : data5.Valid := by
  refine {
    whole_valid := parameter0_valid, midpoint_valid := parameter1_valid,
    whole_checked := derivatives0_checked, center_checked := fun n => derivatives1_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp5_valid
    · exact exp19_valid
    · exact exp22_valid
  all_goals decide +kernel
def box5 : FamilyBoxCertificate := ⟨parameter0,derivatives0 0,![exp0,exp17,exp20],![exp17,exp20,exp24]⟩
theorem box5_valid : box5.Valid := by
  refine ⟨parameter0_valid,derivatives0_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp0_valid
    · exact exp17_valid
    · exact exp20_valid
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp20_valid
    · exact exp24_valid
def leaf5 : FamilyExteriorLeaf := ⟨data5,box5,![(3/32 : ℚ),(3/32 : ℚ),(3/16 : ℚ)],![(-2224274860178810993241/59029581035870565171200 : ℚ),(-1087415205190253282331/29514790517935282585600 : ℚ),(-1053551479062478230957/14757395258967641292800 : ℚ)]⟩
theorem leaf5_valid : leaf5.Valid := by
  refine {
    data_valid := data5_valid, box_valid := box5_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion5 (_hABB : FamilyABBLocal) : ∀x,domain5.Contains x → familyCompactProperty x :=
  leaf5.compact_property leaf5_valid (by decide +kernel)

def domain6 : ReplayBox 4 := ⟨![(39/10 : ℚ),(3/16 : ℚ),(0/1 : ℚ),(3/8 : ℚ)],![(23/5 : ℚ),(3/8 : ℚ),(3/16 : ℚ),(3/4 : ℚ)]⟩
theorem conclusion6 (_hABB : FamilyABBLocal) : ∀x,domain6.Contains x → familyCompactProperty x :=
  familyCompactProperty_ordered_empty domain6 (by decide +kernel)

def domain7 : ReplayBox 4 := ⟨![(39/10 : ℚ),(3/16 : ℚ),(3/16 : ℚ),(3/8 : ℚ)],![(23/5 : ℚ),(3/8 : ℚ),(3/8 : ℚ),(3/4 : ℚ)]⟩
def data7 : FamilyTaylorData :=
  ⟨parameter0,parameter1,![exp19,exp19,exp22],derivatives0,fun n => derivatives1 n.castSucc,(7/20 : ℚ)⟩
theorem data7_valid : data7.Valid := by
  refine {
    whole_valid := parameter0_valid, midpoint_valid := parameter1_valid,
    whole_checked := derivatives0_checked, center_checked := fun n => derivatives1_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp19_valid
    · exact exp19_valid
    · exact exp22_valid
  all_goals decide +kernel
def box7 : FamilyBoxCertificate := ⟨parameter0,derivatives0 0,![exp17,exp17,exp20],![exp20,exp20,exp24]⟩
theorem box7_valid : box7.Valid := by
  refine ⟨parameter0_valid,derivatives0_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp17_valid
    · exact exp20_valid
  · intro j; fin_cases j
    · exact exp20_valid
    · exact exp20_valid
    · exact exp24_valid
def leaf7 : FamilyExteriorLeaf := ⟨data7,box7,![(3/32 : ℚ),(3/32 : ℚ),(3/16 : ℚ)],![(-872421184665547113189/29514790517935282585600 : ℚ),(-872421184665547113189/29514790517935282585600 : ℚ),(-842971226763319692963/14757395258967641292800 : ℚ)]⟩
theorem leaf7_valid : leaf7.Valid := by
  refine {
    data_valid := data7_valid, box_valid := box7_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion7 (_hABB : FamilyABBLocal) : ∀x,domain7.Contains x → familyCompactProperty x :=
  leaf7.compact_property leaf7_valid (by decide +kernel)

def domain8 : ReplayBox 4 := ⟨![(23/5 : ℚ),(0/1 : ℚ),(0/1 : ℚ),(3/8 : ℚ)],![(53/10 : ℚ),(3/16 : ℚ),(3/8 : ℚ),(3/4 : ℚ)]⟩
def data8 : FamilyTaylorData :=
  ⟨parameter2,parameter3,![exp5,exp17,exp22],derivatives2,fun n => derivatives3 n.castSucc,(7/20 : ℚ)⟩
theorem data8_valid : data8.Valid := by
  refine {
    whole_valid := parameter2_valid, midpoint_valid := parameter3_valid,
    whole_checked := derivatives2_checked, center_checked := fun n => derivatives3_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp5_valid
    · exact exp17_valid
    · exact exp22_valid
  all_goals decide +kernel
def box8 : FamilyBoxCertificate := ⟨parameter2,derivatives2 0,![exp0,exp0,exp20],![exp17,exp20,exp24]⟩
theorem box8_valid : box8.Valid := by
  refine ⟨parameter2_valid,derivatives2_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp0_valid
    · exact exp0_valid
    · exact exp20_valid
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp20_valid
    · exact exp24_valid
def leaf8 : FamilyExteriorLeaf := ⟨data8,box8,![(3/32 : ℚ),(3/16 : ℚ),(3/16 : ℚ)],![(-602677902791545599813/14757395258967641292800 : ℚ),(-1172995461295838182179/14757395258967641292800 : ℚ),(-578019998394394885641/7378697629483820646400 : ℚ)]⟩
theorem leaf8_valid : leaf8.Valid := by
  refine {
    data_valid := data8_valid, box_valid := box8_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion8 (_hABB : FamilyABBLocal) : ∀x,domain8.Contains x → familyCompactProperty x :=
  leaf8.compact_property leaf8_valid (by decide +kernel)

def domain9 : ReplayBox 4 := ⟨![(23/5 : ℚ),(3/16 : ℚ),(0/1 : ℚ),(3/8 : ℚ)],![(53/10 : ℚ),(3/8 : ℚ),(3/8 : ℚ),(3/4 : ℚ)]⟩
def data9 : FamilyTaylorData :=
  ⟨parameter2,parameter3,![exp19,exp17,exp22],derivatives2,fun n => derivatives3 n.castSucc,(7/20 : ℚ)⟩
theorem data9_valid : data9.Valid := by
  refine {
    whole_valid := parameter2_valid, midpoint_valid := parameter3_valid,
    whole_checked := derivatives2_checked, center_checked := fun n => derivatives3_checked n.castSucc,
    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  · intro j; fin_cases j
    · exact exp19_valid
    · exact exp17_valid
    · exact exp22_valid
  all_goals decide +kernel
def box9 : FamilyBoxCertificate := ⟨parameter2,derivatives2 0,![exp17,exp0,exp20],![exp20,exp20,exp24]⟩
theorem box9_valid : box9.Valid := by
  refine ⟨parameter2_valid,derivatives2_checked 0,?_,?_⟩
  · intro j; fin_cases j
    · exact exp17_valid
    · exact exp0_valid
    · exact exp20_valid
  · intro j; fin_cases j
    · exact exp20_valid
    · exact exp20_valid
    · exact exp24_valid
def leaf9 : FamilyExteriorLeaf := ⟨data9,box9,![(3/32 : ℚ),(3/16 : ℚ),(3/16 : ℚ)],![(-1898494623210176053689/59029581035870565171200 : ℚ),(-469580411332036202967/7378697629483820646400 : ℚ),(-921248702764886414583/14757395258967641292800 : ℚ)]⟩
theorem leaf9_valid : leaf9.Valid := by
  refine {
    data_valid := data9_valid, box_valid := box9_valid,
    same_parameter := rfl, center_lower := ?_, center_upper := ?_,
    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }
  all_goals decide +kernel
theorem conclusion9 (_hABB : FamilyABBLocal) : ∀x,domain9.Contains x → familyCompactProperty x :=
  leaf9.compact_property leaf9_valid (by decide +kernel)

end SparseLowerTail.Section08.FamilyExteriorReplay.Smoke

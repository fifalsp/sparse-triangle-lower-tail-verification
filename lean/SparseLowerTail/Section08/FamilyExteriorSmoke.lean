import SparseLowerTail.Section08.FamilyExteriorLeaf
import SparseLowerTail.Section08.FamilyParameterSmoke

/-! One checked exterior Taylor box. Not a complete cover. -/
namespace SparseLowerTail.Certificate.FamilyExteriorSmoke
open Numerics FamilyCoeff
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def midLog : ExpEndpointCertificate :=
  ⟨(4999/1280 : ℚ),20,(451608412923734231/576460752303423488 : ℚ),(903216825847468463/1152921504606846976 : ℚ),(23210057291627459/1152921504606846976 : ℚ),(5802514322906865/288230376151711744 : ℚ)⟩
theorem midLog_valid : midLog.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate :=
  ⟨(188818175126812347/1152921504606846976 : ℚ),20,(285295140116467195/288230376151711744 : ℚ),(1141180560465868781/1152921504606846976 : ℚ),(978754434568942253/1152921504606846976 : ℚ),(978754434568942267/1152921504606846976 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate :=
  ⟨(94409087563406179/576460752303423488 : ℚ),20,(1141180560465868779/1152921504606846976 : ℚ),(285295140116467195/288230376151711744 : ℚ),(978754434568942239/1152921504606846976 : ℚ),(489377217284471127/576460752303423488 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower : ExpEndpointCertificate :=
  ⟨(99/100 : ℚ),20,(541873325929236715/576460752303423488 : ℚ),(1083746651858473431/1152921504606846976 : ℚ),(428398757689970401/1152921504606846976 : ℚ),(53549844711246301/144115188075855872 : ℚ)⟩
theorem qLower_valid : qLower.Valid := by decide +kernel
def qUpper : ExpEndpointCertificate :=
  ⟨(101/100 : ℚ),20,(541196407434025103/576460752303423488 : ℚ),(1082392814868050207/1152921504606846976 : ℚ),(419915893933971121/1152921504606846976 : ℚ),(52489486741746391/144115188075855872 : ℚ)⟩
theorem qUpper_valid : qUpper.Valid := by decide +kernel
def qPoint : ExpEndpointCertificate :=
  ⟨(1/1 : ℚ),20,(1083069521826238951/1152921504606846976 : ℚ),(135383690228279869/144115188075855872 : ℚ),(26508507426831583/72057594037927936 : ℚ),(424136118829305335/1152921504606846976 : ℚ)⟩
theorem qPoint_valid : qPoint.Valid := by decide +kernel
def midpoint : FamilyParameterCertificate :=
  ⟨midLog,midLog,deltaLower,deltaUpper,⟨188818175126812347,188818175126812358⟩⟩
theorem midpoint_valid : midpoint.Valid := by
  refine ⟨midLog_valid,midLog_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel

def centerD : Fin 3 → Fin 7 → DyadicInterval :=
  ![![⟨-27370213303237615,-27370213303237604⟩,⟨55550853082939335,55550853082939350⟩,⟨2249005998065267,2249005998065269⟩,⟨-4663734980832402,-4663734980832399⟩,⟨26922810134806157,26922810134806162⟩,⟨-52644552828458923,-52644552828458906⟩,⟨303906484021396937,303906484021396972⟩],
    ![⟨9514010953160191,9514010953160217⟩,⟨-23807026699799935,-23807026699799895⟩,⟨-1963845384617658,-1963845384617654⟩,⟨2145542541477960,2145542541477966⟩,⟨-1842399762014717,-1842399762014700⟩,⟨26439388840179586,26439388840179630⟩,⟨-33614831883116825,-33614831883116676⟩],
    ![⟨6587679754258511,6587679754258582⟩,⟨-6023310529606820,-6023310529606708⟩,⟨1133220060789442,1133220060789453⟩,⟨765409102321674,765409102321689⟩,⟨-6721188802997125,-6721188802997061⟩,⟨-2472285295831489,-2472285295831366⟩,⟨-21759507975688718,-21759507975688064⟩]]
theorem centerD_checked (n : Fin 3) (i : Fin 7) :
    (derivativeExpr i n.val).dyadicEval midpoint.parameterBox=some (centerD n i) := by
  fin_cases n <;> fin_cases i <;> decide +kernel

def data : FamilyTaylorData :=
  ⟨FamilyScaledSmoke.Leaf0.parameter,midpoint,fun _ => qPoint,
    FamilyParameterSmoke.intervals,centerD,7/1280⟩
theorem data_valid : data.Valid := by
  refine {
    whole_valid := FamilyScaledSmoke.Leaf0.parameter_valid,
    midpoint_valid := midpoint_valid, q_valid := fun _ => qPoint_valid,
    whole_checked := FamilyParameterSmoke.intervals_checked,
    center_checked := centerD_checked, point := rfl,
    positive := ?_, center_lower := ?_, center_upper := ?_,
    width_nonneg := ?_, width_left := ?_, width_right := ?_ }
  all_goals decide +kernel

def box : FamilyBoxCertificate :=
  ⟨FamilyScaledSmoke.Leaf0.parameter,FamilyScaledSmoke.Leaf0.box.coefficient,
    fun _ => qLower,fun _ => qUpper⟩
theorem box_valid : box.Valid :=
  ⟨FamilyScaledSmoke.Leaf0.parameter_valid,FamilyScaledSmoke.Leaf0.box_valid.2.1,
    fun _ => qLower_valid,fun _ => qUpper_valid⟩

def leaf : FamilyExteriorLeaf :=
  ⟨data,box,fun _ => 1/100,fun i =>
    -data.gradientUpper i*(1/100)+
      min 0 (box.factoredHessianIntervals i i).toRational.lower*(1/100)^2/2⟩
theorem leaf_valid : leaf.Valid := by
  refine {
    data_valid := data_valid, box_valid := box_valid,
    same_parameter := rfl, choice := fun _ => Or.inl le_rfl,
    center_lower := ?_, center_upper := ?_, radius_left := ?_,
    radius_right := ?_, positive_margin := ?_ }
  all_goals decide +kernel

theorem margin_bound : (1/1000 : ℚ)<leaf.margin := by decide +kernel

theorem positive {t : ℝ} (ht : Bounds t (39/10) (2503/640))
    {q : FamilyVector} (hq : ∀i,Bounds (q i) (99/100) (101/100)) :
    0<familyPhi (Real.exp (-t)) q := by
  apply leaf.positive leaf_valid
  · norm_num [leaf,data,FamilyScaledSmoke.Leaf0.parameter,
      FamilyScaledSmoke.Leaf0.logLower,FamilyScaledSmoke.Leaf0.logUpper]
    exact ht
  · simpa [leaf,box,qLower,qUpper] using hq

end SparseLowerTail.Certificate.FamilyExteriorSmoke

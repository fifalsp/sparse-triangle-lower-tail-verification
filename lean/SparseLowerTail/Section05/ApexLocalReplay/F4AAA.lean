import SparseLowerTail.Section05.ApexFanBoxIntervals
import SparseLowerTail.Section05.ApexTaylorIntervals

/-! Full published contact radius. Every numerical assertion is kernel checked. -/
namespace SparseLowerTail.Section05.ApexLocalReplay.F4AAA
open Numerics Certificate CoverGeometry
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def centerLo0 : ExpEndpointCertificate := ⟨(101813570289/25000000000 : ℚ),20,(223458597731325597/288230376151711744 : ℚ),(893834390925302389/1152921504606846976 : ℚ),(19638886918825053/1152921504606846976 : ℚ),(19638886918825055/1152921504606846976 : ℚ)⟩
theorem centerLo0_valid : centerLo0.Valid := by decide +kernel
def centerHi0 : ExpEndpointCertificate := ⟨(397709259/97656250 : ℚ),20,(446917195445891799/576460752303423488 : ℚ),(893834390891783599/1152921504606846976 : ℚ),(19638886907041721/1152921504606846976 : ℚ),(9819443453520861/576460752303423488 : ℚ)⟩
theorem centerHi0_valid : centerHi0.Valid := by decide +kernel
def center : ApexFanBox := ⟨![centerLo0,centerLo0,centerLo0],![centerHi0,centerHi0,centerHi0]⟩
theorem center_valid : center.Valid := by
  constructor <;> intro j <;> fin_cases j
  · exact centerLo0_valid
  · exact centerLo0_valid
  · exact centerLo0_valid
  · exact centerHi0_valid
  · exact centerHi0_valid
  · exact centerHi0_valid

def cubeLo0 : ExpEndpointCertificate := ⟨(7111716523348005169778021/1759218604441600000000000 : ℚ),20,(447755951292004451/576460752303423488 : ℚ),(895511902584008903/1152921504606846976 : ℚ),(20236980067303689/1152921504606846976 : ℚ),(10118490033651845/576460752303423488 : ℚ)⟩
theorem cubeLo0_valid : cubeLo0.Valid := by decide +kernel
def cubeHi0 : ExpEndpointCertificate := ⟨(7217269640670032328536731/1759218604441600000000000 : ℚ),20,(446080010810295545/576460752303423488 : ℚ),(892160021620591091/1152921504606846976 : ℚ),(9529235041401457/576460752303423488 : ℚ),(4764617520700729/288230376151711744 : ℚ)⟩
theorem cubeHi0_valid : cubeHi0.Valid := by decide +kernel
def cube : ApexFanBox := ⟨![cubeLo0,cubeLo0,cubeLo0],![cubeHi0,cubeHi0,cubeHi0]⟩
theorem cube_valid : cube.Valid := by
  constructor <;> intro j <;> fin_cases j
  · exact cubeLo0_valid
  · exact cubeLo0_valid
  · exact cubeLo0_valid
  · exact cubeHi0_valid
  · exact cubeHi0_valid
  · exact cubeHi0_valid

def radius : ℚ := (1080863910568919/36028797018963968 : ℚ)
def ell : ℚ := (30217402572057/5000000000000000 : ℚ)
def transform : FamilyRationalMatrix := ![![(18009873/1000000 : ℚ),(765321/100000 : ℚ),(16398749/1000000 : ℚ)],![(0/1 : ℚ),(4892131/250000 : ℚ),(16398749/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(25531277/1000000 : ℚ)]]

theorem hessian_checked : FamilyIntervalPositive (familyIntervalCongruence
    (apexShiftedHessianInterval (apexHessianInterval (center.variableIntervals 3)) ell) transform) := by
  decide +kernel

theorem margin_checked : radius*((∑i,∑j,∑k,
    apexThirdIntervalBound (cube.variableIntervals 3) i j k : ℤ) : ℚ)/
    (DyadicInterval.scale : ℚ)<3*ell := by
  decide +kernel

theorem center_contains : ∀k,
    (center.variableIntervals 3 k).contains
      (apexVariables (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) apexContactAAA k) := by
  apply center.variableIntervals_contains center_valid 3
  intro j
  fin_cases j
  · have hc := apexPrimitiveBounds_contains 0
    norm_num [center,centerLo0,centerHi0,apexPrimitiveBounds,apexPrimitiveValues,apexContactAAA,RationalInterval.contains] at hc ⊢
    exact hc
  · have hc := apexPrimitiveBounds_contains 0
    norm_num [center,centerLo0,centerHi0,apexPrimitiveBounds,apexPrimitiveValues,apexContactAAA,RationalInterval.contains] at hc ⊢
    exact hc
  · have hc := apexPrimitiveBounds_contains 0
    norm_num [center,centerLo0,centerHi0,apexPrimitiveBounds,apexPrimitiveValues,apexContactAAA,RationalInterval.contains] at hc ⊢
    exact hc

theorem cube_contains {q : ApexVector}
    (hq : q∈familyCube apexContactAAA (radius : ℝ)) : ∀k,
    (cube.variableIntervals 3 k).contains
      (apexVariables (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) q k) := by
  apply cube.variableIntervals_contains cube_valid 3
  intro j
  fin_cases j
  · have hp : Bounds (apexContactAAA 0) ((101813570289/25000000000 : ℚ) : ℝ) ((397709259/97656250 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 0
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactAAA,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 0)
    change -(radius : ℝ)≤q 0-apexContactAAA 0 ∧ q 0-apexContactAAA 0≤(radius : ℝ) at hd
    change Bounds (q 0) ((7111716523348005169778021/1759218604441600000000000 : ℚ) : ℝ) ((7217269640670032328536731/1759218604441600000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactAAA 1) ((101813570289/25000000000 : ℚ) : ℝ) ((397709259/97656250 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 0
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactAAA,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 1)
    change -(radius : ℝ)≤q 1-apexContactAAA 1 ∧ q 1-apexContactAAA 1≤(radius : ℝ) at hd
    change Bounds (q 1) ((7111716523348005169778021/1759218604441600000000000 : ℚ) : ℝ) ((7217269640670032328536731/1759218604441600000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactAAA 2) ((101813570289/25000000000 : ℚ) : ℝ) ((397709259/97656250 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 0
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactAAA,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 2)
    change -(radius : ℝ)≤q 2-apexContactAAA 2 ∧ q 2-apexContactAAA 2≤(radius : ℝ) at hd
    change Bounds (q 2) ((7111716523348005169778021/1759218604441600000000000 : ℚ) : ℝ) ((7217269640670032328536731/1759218604441600000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]

/-- Positivity and the unique zero on the entire published contact cube. -/
theorem local_nonneg_zero_iff {q : ApexVector} (hq : q∈familyCube apexContactAAA (radius : ℝ)) :
    0≤apexPhi (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) q ∧
    (apexPhi (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) q=0 ↔ q=apexContactAAA) := by
  have hj := (apexFanTheta_contacts 3).1
  exact apexPhi_local_of_interval_taylor radius ell (by norm_num [radius]) (by norm_num [ell])
    hj.1 hj.2 (center.variableIntervals 3) (cube.variableIntervals 3) transform
    center_contains (fun _ hr => cube_contains hr) hessian_checked margin_checked hq

end SparseLowerTail.Section05.ApexLocalReplay.F4AAA

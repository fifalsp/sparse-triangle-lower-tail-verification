import SparseLowerTail.Section05.ApexFanBoxIntervals
import SparseLowerTail.Section05.ApexTaylorIntervals

/-! Full published contact radius. Every numerical assertion is kernel checked. -/
namespace SparseLowerTail.Section05.ApexLocalReplay.F6ABB
open Numerics Certificate CoverGeometry
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def centerLo0 : ExpEndpointCertificate := ⟨(101813570289/25000000000 : ℚ),20,(223458597731325597/288230376151711744 : ℚ),(893834390925302389/1152921504606846976 : ℚ),(19638886918825053/1152921504606846976 : ℚ),(19638886918825055/1152921504606846976 : ℚ)⟩
theorem centerLo0_valid : centerLo0.Valid := by decide +kernel
def centerHi0 : ExpEndpointCertificate := ⟨(397709259/97656250 : ℚ),20,(446917195445891799/576460752303423488 : ℚ),(893834390891783599/1152921504606846976 : ℚ),(19638886907041721/1152921504606846976 : ℚ),(9819443453520861/576460752303423488 : ℚ)⟩
theorem centerHi0_valid : centerHi0.Valid := by decide +kernel
def centerLo1 : ExpEndpointCertificate := ⟨(16328752549/100000000000 : ℚ),20,(1141215233984545551/1152921504606846976 : ℚ),(71325952124034097/72057594037927936 : ℚ),(489615178539307979/576460752303423488 : ℚ),(979230357078615973/1152921504606846976 : ℚ)⟩
theorem centerLo1_valid : centerLo1.Valid := by decide +kernel
def centerHi1 : ExpEndpointCertificate := ⟨(8164376281/50000000000 : ℚ),20,(570607616987636589/576460752303423488 : ℚ),(1141215233975273179/1152921504606846976 : ℚ),(489615178475658011/576460752303423488 : ℚ),(979230356951316037/1152921504606846976 : ℚ)⟩
theorem centerHi1_valid : centerHi1.Valid := by decide +kernel
def center : ApexFanBox := ⟨![centerLo0,centerLo1,centerLo1],![centerHi0,centerHi1,centerHi1]⟩
theorem center_valid : center.Valid := by
  constructor <;> intro j <;> fin_cases j
  · exact centerLo0_valid
  · exact centerLo1_valid
  · exact centerLo1_valid
  · exact centerHi0_valid
  · exact centerHi1_valid
  · exact centerHi1_valid

def cubeLo0 : ExpEndpointCertificate := ⟨(114575594308357919484026461/28147497671065600000000000 : ℚ),20,(111743265900942525/144115188075855872 : ℚ),(893946127207540201/1152921504606846976 : ℚ),(19678203996634821/1152921504606846976 : ℚ),(9839101998317411/576460752303423488 : ℚ)⟩
theorem cubeLo0_valid : cubeLo0.Valid := by decide +kernel
def cubeHi0 : ExpEndpointCertificate := ⟨(114688184315930680489009571/28147497671065600000000000 : ℚ),20,(893722668575712351/1152921504606846976 : ℚ),(27928833392991011/36028797018963968 : ℚ),(4899912096207339/288230376151711744 : ℚ),(9799824192414679/576460752303423488 : ℚ)⟩
theorem cubeHi0_valid : cubeHi0.Valid := by decide +kernel
def cubeLo1 : ExpEndpointCertificate := ⟨(4539840248101708594290269/28147497671065600000000000 : ℚ),20,(71334868425306821/72057594037927936 : ℚ),(1141357894804909137/1152921504606846976 : ℚ),(490595388779890455/576460752303423488 : ℚ),(245297694389945231/288230376151711744 : ℚ)⟩
theorem cubeLo1_valid : cubeLo1.Valid := by decide +kernel
def cubeHi1 : ExpEndpointCertificate := ⟨(4652430242445145693872547/28147497671065600000000000 : ℚ),20,(570536295493199403/576460752303423488 : ℚ),(1141072590986398807/1152921504606846976 : ℚ),(122159231674142421/144115188075855872 : ℚ),(977273853393139383/1152921504606846976 : ℚ)⟩
theorem cubeHi1_valid : cubeHi1.Valid := by decide +kernel
def cube : ApexFanBox := ⟨![cubeLo0,cubeLo1,cubeLo1],![cubeHi0,cubeHi1,cubeHi1]⟩
theorem cube_valid : cube.Valid := by
  constructor <;> intro j <;> fin_cases j
  · exact cubeLo0_valid
  · exact cubeLo1_valid
  · exact cubeLo1_valid
  · exact cubeHi0_valid
  · exact cubeHi1_valid
  · exact cubeHi1_valid

def radius : ℚ := (1152921504606847/576460752303423488 : ℚ)
def ell : ℚ := (15655232683787/2500000000000000 : ℚ)
def transform : FamilyRationalMatrix := ![![(1573533/200000 : ℚ),(-7541801/1000000 : ℚ),(-17483421/500000 : ℚ)],![(0/1 : ℚ),(2982719/1000000 : ℚ),(3296441/500000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(452263/62500 : ℚ)]]

theorem hessian_checked : FamilyIntervalPositive (familyIntervalCongruence
    (apexShiftedHessianInterval (apexHessianInterval (center.variableIntervals 5)) ell) transform) := by
  decide +kernel

theorem margin_checked : radius*((∑i,∑j,∑k,
    apexThirdIntervalBound (cube.variableIntervals 5) i j k : ℤ) : ℚ)/
    (DyadicInterval.scale : ℚ)<3*ell := by
  decide +kernel

theorem center_contains : ∀k,
    (center.variableIntervals 5 k).contains
      (apexVariables (apexFanTheta 5) (cellLambda ((5 : Fin 6).castAdd 6)) apexContactABB k) := by
  apply center.variableIntervals_contains center_valid 5
  intro j
  fin_cases j
  · have hc := apexPrimitiveBounds_contains 0
    norm_num [center,centerLo0,centerHi0,centerLo1,centerHi1,apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
    exact hc
  · have hc := apexPrimitiveBounds_contains 1
    norm_num [center,centerLo0,centerHi0,centerLo1,centerHi1,apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
    exact hc
  · have hc := apexPrimitiveBounds_contains 1
    norm_num [center,centerLo0,centerHi0,centerLo1,centerHi1,apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
    exact hc

theorem cube_contains {q : ApexVector}
    (hq : q∈familyCube apexContactABB (radius : ℝ)) : ∀k,
    (cube.variableIntervals 5 k).contains
      (apexVariables (apexFanTheta 5) (cellLambda ((5 : Fin 6).castAdd 6)) q k) := by
  apply cube.variableIntervals_contains cube_valid 5
  intro j
  fin_cases j
  · have hp : Bounds (apexContactABB 0) ((101813570289/25000000000 : ℚ) : ℝ) ((397709259/97656250 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 0
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 0)
    change -(radius : ℝ)≤q 0-apexContactABB 0 ∧ q 0-apexContactABB 0≤(radius : ℝ) at hd
    change Bounds (q 0) ((114575594308357919484026461/28147497671065600000000000 : ℚ) : ℝ) ((114688184315930680489009571/28147497671065600000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactABB 1) ((16328752549/100000000000 : ℚ) : ℝ) ((8164376281/50000000000 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 1
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 1)
    change -(radius : ℝ)≤q 1-apexContactABB 1 ∧ q 1-apexContactABB 1≤(radius : ℝ) at hd
    change Bounds (q 1) ((4539840248101708594290269/28147497671065600000000000 : ℚ) : ℝ) ((4652430242445145693872547/28147497671065600000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactABB 2) ((16328752549/100000000000 : ℚ) : ℝ) ((8164376281/50000000000 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 1
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 2)
    change -(radius : ℝ)≤q 2-apexContactABB 2 ∧ q 2-apexContactABB 2≤(radius : ℝ) at hd
    change Bounds (q 2) ((4539840248101708594290269/28147497671065600000000000 : ℚ) : ℝ) ((4652430242445145693872547/28147497671065600000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]

/-- Positivity and the unique zero on the entire published contact cube. -/
theorem local_nonneg_zero_iff {q : ApexVector} (hq : q∈familyCube apexContactABB (radius : ℝ)) :
    0≤apexPhi (apexFanTheta 5) (cellLambda ((5 : Fin 6).castAdd 6)) q ∧
    (apexPhi (apexFanTheta 5) (cellLambda ((5 : Fin 6).castAdd 6)) q=0 ↔ q=apexContactABB) := by
  have hj := (apexFanTheta_contacts 5).2
  exact apexPhi_local_of_interval_taylor radius ell (by norm_num [radius]) (by norm_num [ell])
    hj.1 hj.2 (center.variableIntervals 5) (cube.variableIntervals 5) transform
    center_contains (fun _ hr => cube_contains hr) hessian_checked margin_checked hq

end SparseLowerTail.Section05.ApexLocalReplay.F6ABB

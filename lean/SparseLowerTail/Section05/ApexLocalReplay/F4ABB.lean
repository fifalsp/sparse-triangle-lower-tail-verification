import SparseLowerTail.Section05.ApexFanBoxIntervals
import SparseLowerTail.Section05.ApexTaylorIntervals

/-! Full published contact radius. Every numerical assertion is kernel checked. -/
namespace SparseLowerTail.Section05.ApexLocalReplay.F4ABB
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

def cubeLo0 : ExpEndpointCertificate := ⟨(458471262219458071539621469/112589990684262400000000000 : ℚ),20,(893862323686465923/1152921504606846976 : ℚ),(223465580921616481/288230376151711744 : ℚ),(19648708817554525/1152921504606846976 : ℚ),(9824354408777263/576460752303423488 : ℚ)⟩
theorem cubeLo0_valid : cubeLo0.Valid := by decide +kernel
def cubeHi0 : ExpEndpointCertificate := ⟨(458583852277696328352522659/112589990684262400000000000 : ℚ),20,(893806459003506257/1152921504606846976 : ℚ),(446903229501753129/576460752303423488 : ℚ),(19629069918039971/1152921504606846976 : ℚ),(4907267479509993/288230376151711744 : ℚ)⟩
theorem cubeHi0_valid : cubeHi0.Valid := by decide +kernel
def cubeLo1 : ExpEndpointCertificate := ⟨(18328245978433227980676701/112589990684262400000000000 : ℚ),20,(570625448758923687/576460752303423488 : ℚ),(1141250897517847375/1152921504606846976 : ℚ),(979720094681353089/1152921504606846976 : ℚ),(61232505917584569/72057594037927936 : ℚ)⟩
theorem cubeLo1_valid : cubeLo1.Valid := by decide +kernel
def cubeHi1 : ExpEndpointCertificate := ⟨(18440835983754189171974563/112589990684262400000000000 : ℚ),20,(1141179571556439647/1152921504606846976 : ℚ),(35661861611138739/36028797018963968 : ℚ),(489370432078118449/576460752303423488 : ℚ),(61171304009764807/72057594037927936 : ℚ)⟩
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

def radius : ℚ := (1152921504606847/2305843009213693952 : ℚ)
def ell : ℚ := (9001293256039/10000000000000000 : ℚ)
def transform : FamilyRationalMatrix := ![![(7391469/1000000 : ℚ),(-40416153/1000000 : ℚ),(-909969/200000 : ℚ)],![(0/1 : ℚ),(15819427/1000000 : ℚ),(-69371347/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(35576109/500000 : ℚ)]]

theorem hessian_checked : FamilyIntervalPositive (familyIntervalCongruence
    (apexShiftedHessianInterval (apexHessianInterval (center.variableIntervals 3)) ell) transform) := by
  decide +kernel

theorem margin_checked : radius*((∑i,∑j,∑k,
    apexThirdIntervalBound (cube.variableIntervals 3) i j k : ℤ) : ℚ)/
    (DyadicInterval.scale : ℚ)<3*ell := by
  decide +kernel

theorem center_contains : ∀k,
    (center.variableIntervals 3 k).contains
      (apexVariables (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) apexContactABB k) := by
  apply center.variableIntervals_contains center_valid 3
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
    (cube.variableIntervals 3 k).contains
      (apexVariables (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) q k) := by
  apply cube.variableIntervals_contains cube_valid 3
  intro j
  fin_cases j
  · have hp : Bounds (apexContactABB 0) ((101813570289/25000000000 : ℚ) : ℝ) ((397709259/97656250 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 0
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 0)
    change -(radius : ℝ)≤q 0-apexContactABB 0 ∧ q 0-apexContactABB 0≤(radius : ℝ) at hd
    change Bounds (q 0) ((458471262219458071539621469/112589990684262400000000000 : ℚ) : ℝ) ((458583852277696328352522659/112589990684262400000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactABB 1) ((16328752549/100000000000 : ℚ) : ℝ) ((8164376281/50000000000 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 1
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 1)
    change -(radius : ℝ)≤q 1-apexContactABB 1 ∧ q 1-apexContactABB 1≤(radius : ℝ) at hd
    change Bounds (q 1) ((18328245978433227980676701/112589990684262400000000000 : ℚ) : ℝ) ((18440835983754189171974563/112589990684262400000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactABB 2) ((16328752549/100000000000 : ℚ) : ℝ) ((8164376281/50000000000 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 1
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 2)
    change -(radius : ℝ)≤q 2-apexContactABB 2 ∧ q 2-apexContactABB 2≤(radius : ℝ) at hd
    change Bounds (q 2) ((18328245978433227980676701/112589990684262400000000000 : ℚ) : ℝ) ((18440835983754189171974563/112589990684262400000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]

/-- Positivity and the unique zero on the entire published contact cube. -/
theorem local_nonneg_zero_iff {q : ApexVector} (hq : q∈familyCube apexContactABB (radius : ℝ)) :
    0≤apexPhi (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) q ∧
    (apexPhi (apexFanTheta 3) (cellLambda ((3 : Fin 6).castAdd 6)) q=0 ↔ q=apexContactABB) := by
  have hj := (apexFanTheta_contacts 3).2
  exact apexPhi_local_of_interval_taylor radius ell (by norm_num [radius]) (by norm_num [ell])
    hj.1 hj.2 (center.variableIntervals 3) (cube.variableIntervals 3) transform
    center_contains (fun _ hr => cube_contains hr) hessian_checked margin_checked hq

end SparseLowerTail.Section05.ApexLocalReplay.F4ABB

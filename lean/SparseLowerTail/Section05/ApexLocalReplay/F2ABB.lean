import SparseLowerTail.Section05.ApexFanBoxIntervals
import SparseLowerTail.Section05.ApexTaylorIntervals

/-! Full published contact radius. Every numerical assertion is kernel checked. -/
namespace SparseLowerTail.Section05.ApexLocalReplay.F2ABB
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

def cubeLo0 : ExpEndpointCertificate := ⟨(916998819434258274280414813/225179981368524800000000000 : ℚ),20,(893848357196771807/1152921504606846976 : ℚ),(27932761162399119/36028797018963968 : ℚ),(9821898627160561/576460752303423488 : ℚ),(19643797254321123/1152921504606846976 : ℚ)⟩
theorem cubeLo0_valid : cubeLo0.Valid := by decide +kernel
def cubeHi0 : ExpEndpointCertificate := ⟨(917111409560050525503873443/225179981368524800000000000 : ℚ),20,(893820424838535989/1152921504606846976 : ℚ),(446910212419267995/576460752303423488 : ℚ),(19633977798979037/1152921504606846976 : ℚ),(9816988899489519/576460752303423488 : ℚ)⟩
theorem cubeHi0_valid : cubeHi0.Valid := by decide +kernel
def cubeLo1 : ExpEndpointCertificate := ⟨(36712786952208587162525277/225179981368524800000000000 : ℚ),20,(570616532805942893/576460752303423488 : ℚ),(1141233065611885787/1152921504606846976 : ℚ),(489737597635692259/576460752303423488 : ℚ),(979475195271384533/1152921504606846976 : ℚ)⟩
theorem cubeLo1_valid : cubeLo1.Valid := by decide +kernel
def cubeHi1 : ExpEndpointCertificate := ⟨(36825376972166247142777251/225179981368524800000000000 : ℚ),20,(1141197402626550089/1152921504606846976 : ℚ),(570598701313275045/576460752303423488 : ℚ),(3824162421720613/4503599627370496 : ℚ),(489492789980238471/576460752303423488 : ℚ)⟩
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

def radius : ℚ := (1152921504606847/4611686018427387904 : ℚ)
def ell : ℚ := (9000953069047/10000000000000000 : ℚ)
def transform : FamilyRationalMatrix := ![![(1006783/100000 : ℚ),(-974513/40000 : ℚ),(-322339/250000 : ℚ)],![(0/1 : ℚ),(4671/625 : ℚ),(-70410359/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(14161177/200000 : ℚ)]]

theorem hessian_checked : FamilyIntervalPositive (familyIntervalCongruence
    (apexShiftedHessianInterval (apexHessianInterval (center.variableIntervals 1)) ell) transform) := by
  decide +kernel

theorem margin_checked : radius*((∑i,∑j,∑k,
    apexThirdIntervalBound (cube.variableIntervals 1) i j k : ℤ) : ℚ)/
    (DyadicInterval.scale : ℚ)<3*ell := by
  decide +kernel

theorem center_contains : ∀k,
    (center.variableIntervals 1 k).contains
      (apexVariables (apexFanTheta 1) (cellLambda ((1 : Fin 6).castAdd 6)) apexContactABB k) := by
  apply center.variableIntervals_contains center_valid 1
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
    (cube.variableIntervals 1 k).contains
      (apexVariables (apexFanTheta 1) (cellLambda ((1 : Fin 6).castAdd 6)) q k) := by
  apply cube.variableIntervals_contains cube_valid 1
  intro j
  fin_cases j
  · have hp : Bounds (apexContactABB 0) ((101813570289/25000000000 : ℚ) : ℝ) ((397709259/97656250 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 0
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 0)
    change -(radius : ℝ)≤q 0-apexContactABB 0 ∧ q 0-apexContactABB 0≤(radius : ℝ) at hd
    change Bounds (q 0) ((916998819434258274280414813/225179981368524800000000000 : ℚ) : ℝ) ((917111409560050525503873443/225179981368524800000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactABB 1) ((16328752549/100000000000 : ℚ) : ℝ) ((8164376281/50000000000 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 1
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 1)
    change -(radius : ℝ)≤q 1-apexContactABB 1 ∧ q 1-apexContactABB 1≤(radius : ℝ) at hd
    change Bounds (q 1) ((36712786952208587162525277/225179981368524800000000000 : ℚ) : ℝ) ((36825376972166247142777251/225179981368524800000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]
  · have hp : Bounds (apexContactABB 2) ((16328752549/100000000000 : ℚ) : ℝ) ((8164376281/50000000000 : ℚ) : ℝ) := by
      have hc := apexPrimitiveBounds_contains 1
      norm_num [apexPrimitiveBounds,apexPrimitiveValues,apexContactABB,RationalInterval.contains] at hc ⊢
      exact hc
    have hd := abs_le.mp (hq 2)
    change -(radius : ℝ)≤q 2-apexContactABB 2 ∧ q 2-apexContactABB 2≤(radius : ℝ) at hd
    change Bounds (q 2) ((36712786952208587162525277/225179981368524800000000000 : ℚ) : ℝ) ((36825376972166247142777251/225179981368524800000000000 : ℚ) : ℝ)
    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢
    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]

/-- Positivity and the unique zero on the entire published contact cube. -/
theorem local_nonneg_zero_iff {q : ApexVector} (hq : q∈familyCube apexContactABB (radius : ℝ)) :
    0≤apexPhi (apexFanTheta 1) (cellLambda ((1 : Fin 6).castAdd 6)) q ∧
    (apexPhi (apexFanTheta 1) (cellLambda ((1 : Fin 6).castAdd 6)) q=0 ↔ q=apexContactABB) := by
  have hj := (apexFanTheta_contacts 1).2
  exact apexPhi_local_of_interval_taylor radius ell (by norm_num [radius]) (by norm_num [ell])
    hj.1 hj.2 (center.variableIntervals 1) (cube.variableIntervals 1) transform
    center_contains (fun _ hr => cube_contains hr) hessian_checked margin_checked hq

end SparseLowerTail.Section05.ApexLocalReplay.F2ABB

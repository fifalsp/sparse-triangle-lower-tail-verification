import SparseLowerTail.Section04.Branch
import SparseLowerTail.Section04.EntropyGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Normalized balanced rays, following `lem:ray`. The scalar density and cost
identities combine with the graphon integral formulas in `Balanced.lean`.
Here κ is an actual real cube root, not a variable postulated to satisfy a cube
identity. -/
noncomputable section
namespace SparseLowerTail.Section04

/-- The manuscript's κ(z). -/
def kappa (z : ℝ) : ℝ := ((z ^ 3 + 3 * z) / 4) ^ (1 / 3 : ℝ)
/-- The two values of the normalized kernel Y_z. They need not be ≤ 1. -/
def rayA (z : ℝ) : ℝ := z / kappa z
def rayB (z : ℝ) : ℝ := 1 / kappa z
/-- The manuscript's A(z), the excess edge density of Y_z. -/
def rayExcess (z : ℝ) : ℝ := (rayA z + rayB z) / 2 - 1
/-- The manuscript's g_r(z). -/
def rayGap (r z : ℝ) : ℝ := rayExcess z * Real.log r + balancedCost (rayA z) (rayB z)
/-- The manuscript's ρ(z). -/
def branchRho (z : ℝ) : ℝ := kappa z * branchB z
/-- The manuscript's D(z). -/
def branchDifference (z : ℝ) : ℝ :=
  entropy (branchRho z) - balancedCost (branchA z) (branchB z)

theorem kappa_pos {z : ℝ} (hz : 0 < z) : 0 < kappa z := by
  unfold kappa
  apply Real.rpow_pos_of_pos
  positivity

theorem kappa_cube {z : ℝ} (hz : 0 ≤ z) : kappa z ^ 3 = (z ^ 3 + 3 * z) / 4 := by
  unfold kappa
  simpa only [one_div] using Real.rpow_inv_natCast_pow (n := 3)
    (x := (z ^ 3 + 3 * z) / 4) (by positivity) (by decide : (3 : ℕ) ≠ 0)

@[simp]theorem kappa_one : kappa 1 = 1 := by norm_num [kappa]

theorem kappa_lt_one {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : kappa z < 1 := by
  have hz3 : z ^ 3 < 1 := by
    simpa only [one_pow] using (show Odd (3 : ℕ) by decide).strictMono_pow hz1
  have hk3 := kappa_cube (le_of_lt hz)
  have hcube : kappa z ^ 3 < 1 ^ 3 := by nlinarith
  exact (show Odd (3 : ℕ) by decide).strictMono_pow.lt_iff_lt.mp hcube

theorem rayA_pos {z : ℝ} (hz : 0 < z) : 0 < rayA z := div_pos hz (kappa_pos hz)
theorem rayB_pos {z : ℝ} (hz : 0 < z) : 0 < rayB z := one_div_pos.mpr (kappa_pos hz)

/-- `lem:ray` (a): Y_z has triangle density exactly one. -/
theorem ray_triangle {z : ℝ} (hz : 0 < z) : balancedTriangle (rayA z) (rayB z) = 1 := by
  have hk : kappa z ≠ 0 := ne_of_gt (kappa_pos hz)
  have hc := kappa_cube (le_of_lt hz)
  unfold balancedTriangle rayA rayB
  field_simp
  nlinarith

/-- The density half of `lem:ray` (a), valid for any real scale. -/
theorem scaled_ray_triangle {z : ℝ} (hz : 0 < z) (r : ℝ) :
    balancedTriangle (r * rayA z) (r * rayB z) = r ^ 3 := by
  rw [balancedTriangle_scale, ray_triangle hz, mul_one]

/-- The entropy half of `lem:ray` (a). -/
theorem scaled_ray_cost {z r : ℝ} (hz : 0 < z) (hr : 0 < r) :
    balancedCost (r * rayA z) (r * rayB z) = entropy r + r * rayGap r z := by
  rw [balancedCost_scale hr (le_of_lt (rayA_pos hz)) (le_of_lt (rayB_pos hz))]
  unfold entropy rayGap rayExcess
  ring

/-- A saturated nonconstant ray with positive target cannot have within-block
value zero; this is the first step in the converse of `lem:ray` (a). -/
theorem saturated_pair_pos {a b r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (ht : balancedTriangle a b = r ^ 3) : 0 < a := by
  rcases eq_or_lt_of_le ha with he | hp
  · subst a
    simp [balancedTriangle] at ht
    have : 0 < r ^ 3 := pow_pos hr _
    linarith
  · exact hp

/-- Converse in `lem:ray` (a), identifying both scalar values of the kernel. -/
theorem saturated_pair_ray {a b r : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hr : 0 < r) (ht : balancedTriangle a b = r ^ 3) :
    0 < a ∧ 0 < a / b ∧ a / b < 1 ∧
    a = r * rayA (a / b) ∧ b = r * rayB (a / b) := by
  have hap := saturated_pair_pos ha hr ht
  have hbp : 0 < b := hap.trans hab
  have hz : 0 < a / b := div_pos hap hbp
  have hb0 : b ≠ 0 := ne_of_gt hbp
  have hk0 : kappa (a / b) ≠ 0 := ne_of_gt (kappa_pos hz)
  have hc := kappa_cube (le_of_lt hz)
  have hpow : (b * kappa (a / b)) ^ 3 = r ^ 3 := by
    rw [mul_pow, hc, ← ht]
    unfold balancedTriangle
    field_simp
  have hbr : b * kappa (a / b) = r :=
    (show Odd (3 : ℕ) by decide).strictMono_pow.injective hpow
  refine ⟨hap, hz, (div_lt_one hbp).mpr hab, ?_, ?_⟩
  · unfold rayA
    rw [← hbr]
    field_simp
  · unfold rayB
    rw [← hbr]
    field_simp

@[simp]theorem rayA_one : rayA 1 = 1 := by simp [rayA]
@[simp]theorem rayB_one : rayB 1 = 1 := by simp [rayB]
@[simp]theorem rayExcess_one : rayExcess 1 = 0 := by norm_num [rayExcess]
@[simp]theorem ray_cost_one : balancedCost (rayA 1) (rayB 1) = 0 := by simp
@[simp]theorem rayGap_one (r : ℝ) : rayGap r 1 = 0 := by simp [rayGap]

/-- The strict positivity claim in `lem:ray` (b), by the manuscript's mean-cube
identity. Differentiability and the derivative sign are separate results. -/
theorem rayExcess_pos {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : 0 < rayExcess z := by
  have hk := kappa_pos hz
  have hab : rayA z < rayB z := by
    exact (div_lt_div_iff_of_pos_right hk).mpr hz1
  have hc := mean_cube_sub_balancedTriangle (rayA z) (rayB z)
  rw [ray_triangle hz] at hc
  have hd : 0 < (rayB z - rayA z) ^ 3 := pow_pos (sub_pos.mpr hab) _
  have hm : 1 < (rayA z + rayB z) / 2 := by
    apply (show Odd (3 : ℕ) by decide).strictMono_pow.lt_iff_lt.mp
    nlinarith
  exact sub_pos.mpr hm

/-- The range assertion in `lem:ray` (d). -/
theorem branchRho_mem_Ioo {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    branchRho z ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact mul_pos (kappa_pos hz) (branchB_pos z)
  · have h := mul_lt_mul_of_pos_right (kappa_lt_one hz hz1) (branchB_pos z)
    dsimp [branchRho]
    linarith [branchB_lt_one hz hz1]

/-- The identity B_z = ρ(z)Y_z in `lem:ray` (d), at the level of its two values. -/
theorem branch_eq_scaled_ray {z : ℝ} (hz : 0 < z) :
    branchA z = branchRho z * rayA z ∧ branchB z = branchRho z * rayB z := by
  have hk : kappa z ≠ 0 := ne_of_gt (kappa_pos hz)
  constructor <;> simp only [branchA, branchRho, rayA, rayB] <;> field_simp

/-- The gap identity D(z) = -ρ(z)g_ρ(z)(z) in `lem:ray` (d). -/
theorem branchDifference_eq {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    branchDifference z = -branchRho z * rayGap (branchRho z) z := by
  have he := branch_eq_scaled_ray hz
  have hc := scaled_ray_cost hz (branchRho_mem_Ioo hz hz1).1
  unfold branchDifference
  rw [← he.1, ← he.2] at hc
  linarith

/-- Smoothness of the genuine cube-root normalization on the positive axis. -/
theorem contDiffAt_kappa {z : ℝ} (hz : 0 < z) : ContDiffAt ℝ 1 kappa z := by
  unfold kappa
  apply ContDiffAt.rpow_const_of_ne
  · fun_prop
  · positivity

/-- Implicit differentiation of κ³=(z³+3z)/4 avoids fractional-power algebra. -/
theorem hasDerivAt_kappa {z : ℝ} (hz : 0 < z) :
    HasDerivAt kappa ((z ^ 2 + 1) / (4 * kappa z ^ 2)) z := by
  have hk : DifferentiableAt ℝ kappa z := (contDiffAt_kappa hz).differentiableAt (by norm_num)
  have hp : HasDerivAt (fun x : ℝ => (x ^ 3 + 3 * x) / 4) ((3 * z ^ 2 + 3) / 4) z := by
    convert (((hasDerivAt_id z).pow 3).add ((hasDerivAt_id z).const_mul 3)).div_const 4 using 1
    norm_num
  have heq : (fun x : ℝ => kappa x ^ 3) =ᶠ[nhds z] (fun x : ℝ => (x ^ 3 + 3 * x) / 4) := by
    filter_upwards [eventually_gt_nhds hz] with x hx
    exact kappa_cube (le_of_lt hx)
  have hd := (hk.hasDerivAt.pow 3).unique (hp.congr_of_eventuallyEq heq)
  have hkn : kappa z ≠ 0 := ne_of_gt (kappa_pos hz)
  have hid : deriv kappa z = (z ^ 2 + 1) / (4 * kappa z ^ 2) := by
    simp only [Nat.cast_ofNat] at hd
    apply (eq_div_iff (by positivity : (4 : ℝ) * kappa z ^ 2 ≠ 0)).mpr
    nlinarith [hd]
  rw [← hid]
  exact hk.hasDerivAt

/-- The derivative of A has a particularly simple negative-square form. -/
theorem hasDerivAt_rayExcess {z : ℝ} (hz : 0 < z) :
    HasDerivAt rayExcess (-(1 - z) ^ 2 / (8 * kappa z ^ 4)) z := by
  have hk := hasDerivAt_kappa hz
  have hn := ne_of_gt (kappa_pos hz)
  have hu := (hasDerivAt_id z).div hk hn
  have hv := (hasDerivAt_const z (1 : ℝ)).div hk hn
  have hd := ((hu.add hv).div_const 2).sub_const 1
  convert hd using 1
  have hc := kappa_cube (le_of_lt hz)
  simp only [id_eq]
  field_simp
  nlinarith [hc]

/-- The derivative sign assertion in `lem:ray` (b). -/
theorem deriv_rayExcess_neg {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    deriv rayExcess z < 0 := by
  rw [(hasDerivAt_rayExcess hz).deriv]
  have hn : 0 < (1 - z) ^ 2 := sq_pos_of_pos (sub_pos.mpr hz1)
  have hk := kappa_pos hz
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hn) (by positivity)

/-- Smoothness of the two normalized values away from zero. -/
theorem contDiffAt_rayA {z : ℝ} (hz : 0 < z) : ContDiffAt ℝ 1 rayA z := by
  exact contDiffAt_id.div (contDiffAt_kappa hz) (ne_of_gt (kappa_pos hz))

theorem contDiffAt_rayB {z : ℝ} (hz : 0 < z) : ContDiffAt ℝ 1 rayB z := by
  exact contDiffAt_const.div (contDiffAt_kappa hz) (ne_of_gt (kappa_pos hz))

/-- Smoothness of the normalized cost and gap, including at z=1. -/
theorem contDiffAt_rayGap {z : ℝ} (hz : 0 < z) (r : ℝ) :
    ContDiffAt ℝ 1 (rayGap r) z := by
  have hu := contDiffAt_rayA hz
  have hv := contDiffAt_rayB hz
  have heu : ContDiffAt ℝ 1 (fun x => entropy (rayA x)) z := by
    unfold entropy
    exact ((hu.mul (hu.log (ne_of_gt (rayA_pos hz)))).sub hu).add contDiffAt_const
  have hev : ContDiffAt ℝ 1 (fun x => entropy (rayB x)) z := by
    unfold entropy
    exact ((hv.mul (hv.log (ne_of_gt (rayB_pos hz)))).sub hv).add contDiffAt_const
  exact ((((hu.add hv).div_const 2).sub contDiffAt_const).mul contDiffAt_const).add
    ((heu.add hev).div_const 2)

/-- Continuity on the full half-open interval in `lem:ray` (b). -/
theorem continuousOn_rayGap (r : ℝ) : ContinuousOn (rayGap r) (Set.Ioc (0 : ℝ) 1) := by
  intro z hz
  exact (contDiffAt_rayGap hz.1 r).continuousAt.continuousWithinAt

/-- Continuous differentiability on the open interval in `lem:ray` (b). -/
theorem contDiffOn_rayGap (r : ℝ) : ContDiffOn ℝ 1 (rayGap r) (Set.Ioo (0 : ℝ) 1) := by
  intro z hz
  exact (contDiffAt_rayGap hz.1 r).contDiffWithinAt

/-- Differentiating t(Y_z)=1 gives the constraint used in `lem:ray` (c). -/
theorem ray_derivative_constraint {z : ℝ} (hz : 0 < z) :
    (rayA z ^ 2 + rayB z ^ 2) * deriv rayA z +
      2 * rayA z * rayB z * deriv rayB z = 0 := by
  have hu := ((contDiffAt_rayA hz).differentiableAt (by norm_num)).hasDerivAt
  have hv := ((contDiffAt_rayB hz).differentiableAt (by norm_num)).hasDerivAt
  have hd := ((hu.pow 3).add (((hu.const_mul 3).mul (hv.pow 2)))).div_const 4
  have heq : (fun x => (rayA x ^ 3 + 3 * rayA x * rayB x ^ 2) / 4) =ᶠ[nhds z]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_gt_nhds hz] with x hx
    exact ray_triangle hx
  have he := hd.unique ((hasDerivAt_const z (1 : ℝ)).congr_of_eventuallyEq heq)
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] at he
  nlinarith [he]

/-- The entropy derivative on a normalized ray equals -A' log ρ.
This is the cancellation in the manuscript proof of `lem:ray` (c). -/
theorem hasDerivAt_rayCost {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasDerivAt (fun x => balancedCost (rayA x) (rayB x))
      (-deriv rayExcess z * Real.log (branchRho z)) z := by
  have hu := ((contDiffAt_rayA hz).differentiableAt (by norm_num)).hasDerivAt
  have hv := ((contDiffAt_rayB hz).differentiableAt (by norm_num)).hasDerivAt
  have hd := (((hasDerivAt_entropy (ne_of_gt (rayA_pos hz))).comp z hu).add
    ((hasDerivAt_entropy (ne_of_gt (rayB_pos hz))).comp z hv)).div_const 2
  have hAd := ((hu.add hv).div_const 2).sub_const 1
  have hA : deriv rayExcess z = (deriv rayA z + deriv rayB z) / 2 := hAd.deriv
  have hscale := branch_eq_scaled_ray hz
  have hel := branch_balancedEL hz hz1
  have hr := (branchRho_mem_Ioo hz hz1).1
  have hlu : Real.log (rayA z) = -Real.log (branchRho z) -
      branchMu z * branchRho z ^ 2 * (rayA z ^ 2 + rayB z ^ 2) / 2 := by
    have h := hel.1
    rw [hscale.1, hscale.2, Real.log_mul (ne_of_gt hr) (ne_of_gt (rayA_pos hz))] at h
    nlinarith [h]
  have hlv : Real.log (rayB z) = -Real.log (branchRho z) -
      branchMu z * branchRho z ^ 2 * rayA z * rayB z := by
    have h := hel.2
    rw [hscale.1, hscale.2, Real.log_mul (ne_of_gt hr) (ne_of_gt (rayB_pos hz))] at h
    nlinarith [h]
  convert hd using 1
  rw [hA, hlu, hlv]
  have hc := ray_derivative_constraint hz
  nlinarith [congrArg (fun v : ℝ => branchMu z * branchRho z ^ 2 * v) hc]

/-- `lem:ray` (c), following the paper's EL cancellation argument. -/
theorem hasDerivAt_rayGap {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (r : ℝ) :
    HasDerivAt (rayGap r)
      (deriv rayExcess z * (Real.log r - Real.log (branchRho z))) z := by
  have hA := (hasDerivAt_rayExcess hz).differentiableAt.hasDerivAt
  convert (hA.mul_const (Real.log r)).add (hasDerivAt_rayCost hz hz1) using 1
  ring

/-- The derivative identity stated literally in `lem:ray` (c). -/
theorem deriv_rayGap {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (r : ℝ) :
    deriv (rayGap r) z = deriv rayExcess z * (Real.log r - Real.log (branchRho z)) :=
  (hasDerivAt_rayGap hz hz1 r).deriv

end SparseLowerTail.Section04

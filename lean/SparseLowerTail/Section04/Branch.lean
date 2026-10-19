import SparseLowerTail.Basic

/-! Exact parametrization of the nonconstant balanced Euler--Lagrange branch.
Stable manuscript link: `lem:branch`, parts (a) and (b), and `eq:branch`.
The numerical numbering of these statements is intentionally not used. -/
noncomputable section
namespace SparseLowerTail.Section04

/-- `eq:branch`: the positive logarithmic branch coordinate. -/
def branchLog (z : ℝ) : ℝ := Real.log (1 / z)
def branchB (z : ℝ) : ℝ := Real.exp (-2 * z * branchLog z / (1 - z) ^ 2)
def branchA (z : ℝ) : ℝ := z * branchB z
def branchMu (z : ℝ) : ℝ := 2 * branchLog z / ((1 - z) ^ 2 * branchB z ^ 2)

/-- The two scalar equations `s4:eq:EL`, with the paper's normalization. -/
def BalancedEL (a b μ : ℝ) : Prop :=
  Real.log a = -μ * (a ^ 2 + b ^ 2) / 2 ∧ Real.log b = -μ * a * b

@[simp]theorem branchLog_eq_neg_log (z : ℝ) : branchLog z = -Real.log z := by
  simp [branchLog]

theorem branchLog_pos {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : 0 < branchLog z := by
  rw [branchLog_eq_neg_log]
  exact neg_pos.mpr (Real.log_neg hz hz1)

theorem branchB_pos (z : ℝ) : 0 < branchB z := Real.exp_pos _

theorem branchB_lt_one {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : branchB z < 1 := by
  rw [branchB, Real.exp_lt_one_iff]
  have hL := branchLog_pos hz hz1
  have hs : 0 < (1 - z) ^ 2 := sq_pos_of_pos (sub_pos.mpr hz1)
  exact div_neg_of_neg_of_pos (by nlinarith) hs

theorem branchA_pos {z : ℝ} (hz : 0 < z) : 0 < branchA z :=
  mul_pos hz (branchB_pos z)

theorem branchA_lt_branchB {z : ℝ} (hz1 : z < 1) : branchA z < branchB z := by
  simpa [branchA] using mul_lt_mul_of_pos_right hz1 (branchB_pos z)

theorem branchMu_pos {z : ℝ} (hz : 0 < z) (hz1 : z < 1) : 0 < branchMu z := by
  unfold branchMu
  have hL := branchLog_pos hz hz1
  have hs : 0 < (1 - z) ^ 2 := sq_pos_of_pos (sub_pos.mpr hz1)
  have hb := branchB_pos z
  positivity

@[simp]theorem log_branchB (z : ℝ) :
    Real.log (branchB z) = -2 * z * branchLog z / (1 - z) ^ 2 := by
  simp [branchB]

/-- `lem:branch` (a): the displayed parametrization solves both EL equations. -/
theorem branch_balancedEL {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    BalancedEL (branchA z) (branchB z) (branchMu z) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hd : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hb : branchB z ≠ 0 := ne_of_gt (branchB_pos z)
  have hl : Real.log z = -branchLog z := by simp
  constructor
  · rw [branchA, Real.log_mul hz0 hb, log_branchB, hl]
    unfold branchMu
    field_simp
    ring
  · rw [log_branchB]
    unfold branchMu branchA
    field_simp

/-- `lem:branch` (a), collecting the strict bounds and EL equations. -/
theorem branch_spec {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    0 < branchA z ∧ branchA z < branchB z ∧ branchB z < 1 ∧
    0 < branchMu z ∧ BalancedEL (branchA z) (branchB z) (branchMu z) :=
  ⟨branchA_pos hz, branchA_lt_branchB hz1, branchB_lt_one hz hz1,
    branchMu_pos hz hz1, branch_balancedEL hz hz1⟩

/-- First step of `lem:branch` (b): the triangle bound excludes μ ≤ 0. -/
theorem balancedEL_mu_pos {a b μ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : balancedTriangle a b < 1) (hel : BalancedEL a b μ) : 0 < μ := by
  by_contra h
  have hm : μ ≤ 0 := le_of_not_gt h
  have hnm : 0 ≤ -μ := neg_nonneg.mpr hm
  have hla : 0 ≤ Real.log a := by
    rw [hel.1]
    exact div_nonneg (mul_nonneg hnm (add_nonneg (sq_nonneg a) (sq_nonneg b))) (by norm_num)
  have hlb : 0 ≤ Real.log b := by
    rw [hel.2]
    exact mul_nonneg (mul_nonneg hnm (le_of_lt ha)) (le_of_lt hb)
  have ha1 : 1 ≤ a := (Real.log_nonneg_iff ha).mp hla
  have hb1 : 1 ≤ b := (Real.log_nonneg_iff hb).mp hlb
  have hb2 : 1 ≤ b ^ 2 := by nlinarith
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha1
  have hab : 1 ≤ a * b ^ 2 := by nlinarith
  unfold balancedTriangle at ht
  nlinarith

/-- Subtracting the two EL equations gives the branch's ratio identity. -/
theorem balancedEL_log_ratio {a b μ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hel : BalancedEL a b μ) :
    Real.log (a / b) = -μ * (b - a) ^ 2 / 2 := by
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb), hel.1, hel.2]
  ring

/-- The admissible nonconstant EL branch has the smaller value inside blocks. -/
theorem balancedEL_lt {a b μ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (ht : balancedTriangle a b < 1) (hel : BalancedEL a b μ) :
    a < b := by
  have hm := balancedEL_mu_pos ha hb ht hel
  have hs : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hne))
  have hl : Real.log (a / b) < 0 := by
    rw [balancedEL_log_ratio ha hb hel]
    nlinarith
  have hab : a / b < 1 := (Real.log_neg_iff (div_pos ha hb)).mp hl
  exact (div_lt_one hb).mp hab

/-- `lem:branch` (b): every nonconstant admissible solution is exactly the
parametrized branch, with its uniquely determined ratio z = a / b. -/
theorem balancedEL_parametrization {a b μ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (ht : balancedTriangle a b < 1) (hel : BalancedEL a b μ) :
    a < b ∧ 0 < a / b ∧ a / b < 1 ∧
    a = branchA (a / b) ∧ b = branchB (a / b) ∧ μ = branchMu (a / b) := by
  have hab := balancedEL_lt ha hb hne ht hel
  have hz : 0 < a / b := div_pos ha hb
  have hz1 : a / b < 1 := (div_lt_one hb).mpr hab
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hd : 1 - a / b ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hba0 : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hratio := balancedEL_log_ratio ha hb hel
  have hL : branchLog (a / b) = μ * (b - a) ^ 2 / 2 := by
    rw [branchLog_eq_neg_log, hratio]
    ring
  have hlogb : Real.log b = -2 * (a / b) * branchLog (a / b) / (1 - a / b) ^ 2 := by
    rw [hel.2, hL]
    field_simp [hba0]
  have hbeq : b = branchB (a / b) := by
    unfold branchB
    rw [← hlogb, Real.exp_log hb]
  refine ⟨hab, hz, hz1, ?_, hbeq, ?_⟩
  · rw [branchA, ← hbeq]
    field_simp
  · rw [branchMu, ← hbeq, hL]
    field_simp [hba0]

/-- The parametrization has its prescribed ratio; therefore its parameter is unique. -/
@[simp] theorem branch_ratio (z : ℝ) : branchA z / branchB z = z := by
  unfold branchA
  exact mul_div_cancel_right₀ z (ne_of_gt (branchB_pos z))

/-- Triangle density along `eq:branch`, before taking a real cube root. -/
theorem branch_triangle (z : ℝ) :
    balancedTriangle (branchA z) (branchB z) =
      branchB z ^ 3 * (z ^ 3 + 3 * z) / 4 := by
  unfold balancedTriangle branchA
  ring

end SparseLowerTail.Section04

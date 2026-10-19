import SparseLowerTail.Section08.CertificateBridge
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Signs of the certificate coefficients

Stable paper anchor: `lem:certcoef` (signs). The numerical logarithm bounds
are proved from mathlib's logarithm Taylor remainder and its proved log(2)
bounds. An affine upper bound for z log(1/z) replaces the monotonicity
calculation in the paper without adding any numerical assumptions.
-/
noncomputable section
namespace SparseLowerTail.Certificate
open Section04

/-- The numerical bounds on log(40) used in the manuscript, kernel-checked. -/
theorem log_forty_bounds : (368/100 : ℝ) < Real.log 40 ∧ Real.log 40 < 369/100 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/5 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have htwoL := Real.log_two_gt_d9
  have htwoU := Real.log_two_lt_d9
  have heq : Real.log (40 : ℝ) = 5*Real.log 2 - Real.log (4/5 : ℝ) := by
    calc
      Real.log (40 : ℝ) = Real.log ((2 : ℝ)^5 / (4/5)) := by norm_num
      _ = _ := by rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]; norm_num
  rw [heq]
  constructor <;> linarith

/-- A tangent-line bound: z log(1/z) ≤ (log40−1)z+1/40. -/
theorem branchLog_mul_affine {z : ℝ} (hz : 0 < z) :
    branchLog z*z ≤ (269/100 : ℝ)*z+1/40 := by
  have ht := Real.one_sub_inv_le_log_of_pos (show 0 < 40*z by positivity)
  rw [Real.log_mul (by norm_num : (40 : ℝ) ≠ 0) hz.ne'] at ht
  have ht' := mul_le_mul_of_nonneg_right ht hz.le
  have hc : (1-(40*z)⁻¹)*z = z-1/40 := by field_simp
  rw [hc] at ht'
  rw [branchLog_eq_neg_log]
  have hu := mul_lt_mul_of_pos_right log_forty_bounds.2 hz
  nlinarith

theorem branchLog_lower {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    (368/100 : ℝ) < branchLog z := by
  have hinv : (40 : ℝ) ≤ 1/z := (le_div_iff₀ hz).mpr (by nlinarith)
  exact log_forty_bounds.1.trans_le (Real.log_le_log (by norm_num) hinv)

theorem branchLog_mul_bounds {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    0 ≤ branchLog z*z ∧ branchLog z*z ≤ (369/4000 : ℝ) := by
  have hL := branchLog_lower hz hz40
  have ht := branchLog_mul_affine hz
  constructor
  · positivity
  · linarith

/-- Gamma is bounded strictly away from zero on the full stated interval. -/
theorem gamma_branch_lt {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    gamma z (branchLog z) < -(26/10 : ℝ) := by
  let L := branchLog z
  have hL : (368/100 : ℝ) < L := branchLog_lower hz hz40
  have hL0 : 0 ≤ L := by linarith
  have hm := branchLog_mul_bounds hz hz40
  change 0 ≤ L*z ∧ L*z ≤ (369/4000 : ℝ) at hm
  have hzsq : z^2 ≤ (1/1600 : ℝ) := by nlinarith
  have hmsq : (L*z)^2 ≤ (369/4000 : ℝ)^2 := by nlinarith
  have hmz := mul_le_mul hm.2 hzsq (sq_nonneg z) (by norm_num : (0 : ℝ) ≤ 369/4000)
  have hneg1 : 0 ≤ L*z^2 := mul_nonneg hL0 (sq_nonneg z)
  have hneg2 : 0 ≤ z^3 := pow_nonneg hz.le 3
  unfold gamma
  change 6*L^2*z^2+3*L*z^3-L*z^2-L*z-L-z^3+3*z^2-3*z+1 < _
  nlinarith [hm.1]

theorem gamma_branch_neg {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    gamma z (branchLog z) < 0 := lt_trans (gamma_branch_lt hz hz40) (by norm_num)

theorem coefficient_factor_neg {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    2*branchLog z*z+z^2-1 < 0 := by
  have hm := (branchLog_mul_bounds hz hz40).2
  have hzsq : z^2 ≤ (1/1600 : ℝ) := by nlinarith
  nlinarith

/-- The four normalized coefficient signs on 0<z≤1/40. -/
theorem normalized_coefficient_signs {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    0 < d1 z (branchLog z) ∧ 0 < d2 z (branchLog z) ∧
      d3 z (branchLog z) < 0 ∧ 0 < d4 z (branchLog z) := by
  have hL := branchLog_lower hz hz40
  have hL0 : 0 < branchLog z := by linarith
  have hz1 : z-1 < 0 := by linarith
  have hz1ne : z-1 ≠ 0 := hz1.ne
  have hzp : 0 < z+1 := by positivity
  have h1 : 0 < branchLog z+z-1 := by linarith
  have h2 : 0 < 2*branchLog z+z-1 := by linarith
  have h3 : 0 < 3*branchLog z*z+branchLog z+2*z^2-2 := by
    have hm : 0 ≤ branchLog z*z := mul_nonneg hL0.le hz.le
    nlinarith [sq_nonneg z]
  have hg := gamma_branch_neg hz hz40
  have hf := coefficient_factor_neg hz hz40
  have hs : 0 < (z-1)^2 := sq_pos_of_ne_zero hz1ne
  have hc : (z-1)^3 < 0 := by
    simpa only [pow_succ] using mul_neg_of_pos_of_neg hs hz1
  have hq : 0 < (z-1)^4 := by nlinarith [sq_pos_of_pos hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold d1
    exact div_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hz hz1) hzp) h1) h2)
      (mul_neg_of_pos_of_neg (by norm_num) hg)
  · unfold d2
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (mul_pos hz hs) hf)
      (mul_neg_of_pos_of_neg (by norm_num) hg)
  · unfold d3
    exact div_neg_of_pos_of_neg
      (mul_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hz) hc) h3)
      (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hzp) hg)
  · unfold d4
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hq hf)
      (mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hL0) hzp) hg)

theorem coefficient_signs {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    0 < c1 z ∧ 0 < c2 z ∧ c3 z < 0 ∧ 0 < c4 z := by
  obtain ⟨h1, h2, h3, h4⟩ := normalized_coefficient_signs hz hz40
  have hb := branchB_pos z
  exact ⟨mul_pos (pow_pos hb _) h1, mul_pos (pow_pos hb _) h2,
    mul_neg_of_pos_of_neg (pow_pos hb _) h3, mul_pos (pow_pos hb _) h4⟩

/-- Polynomial controlling the sign of c̄ in `lem:certcoef`. -/
def barPolynomial (z L : ℝ) :=
  2*L^2*z*(z+1)*(z^2+3) + L*(5*z^5-5*z^4+14*z^3-2*z^2-11*z-1) +
  2*z^6-4*z^5+6*z^4-10*z^2+4*z+2

def chi (z : ℝ) := (1+z)*(1+z^2/3)
def auxiliaryG (z : ℝ) :=
  6*branchLog z*z*chi z-11*z+14*z^3+5*z^5

theorem chi_bounds {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    0 ≤ chi z ∧ chi z ≤ (41/40 : ℝ)*(1+1/4800) := by
  have hzsq : z^2 ≤ (1/1600 : ℝ) := by nlinarith
  constructor
  · unfold chi; positivity
  · unfold chi
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)

/-- The paper's numerical g bound, using the affine logarithm estimate. -/
theorem auxiliaryG_lt {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    auxiliaryG z < (293/1000 : ℝ) := by
  have hchi := chi_bounds hz hz40
  have ht := branchLog_mul_affine hz
  have hp := mul_le_mul ht hchi.2 hchi.1
    (show 0 ≤ (269/100 : ℝ)*z+1/40 by positivity)
  have h3 : z^3 ≤ (1/40 : ℝ)^3 := pow_le_pow_left₀ hz.le hz40 3
  have h5 : z^5 ≤ (1/40 : ℝ)^5 := pow_le_pow_left₀ hz.le hz40 5
  unfold auxiliaryG
  nlinarith only [hp, h3, h5, hz40]

theorem barPolynomial_branch_lt {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    barPolynomial z (branchLog z) < -(1/2 : ℝ) := by
  have hL := branchLog_lower hz hz40
  have hL0 : 0 ≤ branchLog z := by linarith
  have hg := auxiliaryG_lt hz hz40
  have hgL := mul_lt_mul_of_pos_left hg (show 0 < branchLog z by linarith)
  have h4 : z^4 ≤ (1/40 : ℝ)^4 := pow_le_pow_left₀ hz.le hz40 4
  have h6 : z^6 ≤ (1/40 : ℝ)^6 := pow_le_pow_left₀ hz.le hz40 6
  have hdrop : barPolynomial z (branchLog z) ≤
      branchLog z*(auxiliaryG z-1)+2+4*z+6*z^4+2*z^6 := by
    have hid : branchLog z*(auxiliaryG z-1)+2+4*z+6*z^4+2*z^6 -
        barPolynomial z (branchLog z) =
        5*branchLog z*z^4+2*branchLog z*z^2+4*z^5+10*z^2 := by
      unfold barPolynomial auxiliaryG chi
      ring
    have hn : 0 ≤ 5*branchLog z*z^4+2*branchLog z*z^2+4*z^5+10*z^2 := by positivity
    linarith
  nlinarith only [hdrop, hgL, hL, hz40, h4, h6]

/-- Exact rational identity for the normalized c̄, with denominators exposed. -/
theorem normalized_bar_identity (z L : ℝ) (hz : z ≠ 0) (hp : z+1 ≠ 0)
    (hg : gamma z L ≠ 0) :
    d1 z L+d2 z L+(1+z)^2*d3 z L/(z^3+3*z) =
      (z-1)*barPolynomial z L/(2*(z^2+3)*gamma z L) := by
  have hs : z^2+3 ≠ 0 := by positivity
  have hd : z^3+3*z ≠ 0 := by
    rw [show z^3+3*z = z*(z^2+3) by ring]
    exact mul_ne_zero hz hs
  unfold d1 d2 d3 barPolynomial
  field_simp
  ring

theorem normalized_bar_neg {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    d1 z (branchLog z)+d2 z (branchLog z)+
      (1+z)^2*d3 z (branchLog z)/(z^3+3*z) < 0 := by
  have hg := gamma_branch_neg hz hz40
  have hp : z+1 ≠ 0 := by positivity
  rw [normalized_bar_identity z (branchLog z) hz.ne' hp hg.ne]
  have hz1 : z-1 < 0 := by linarith
  have hP : barPolynomial z (branchLog z) < 0 :=
    (barPolynomial_branch_lt hz hz40).trans (by norm_num)
  apply div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hz1 hP)
  exact mul_neg_of_pos_of_neg (by positivity) hg

/-- The coefficient c̄ from `lem:certcoef`, in original physical scaling. -/
def cbar (z : ℝ) := c1 z+c2 z+c3 z*((branchA z+branchB z)/2)^2/
  balancedTriangle (branchA z) (branchB z)

theorem cbar_scaled {z : ℝ} (hz : 0 < z) :
    cbar z = branchB z^2*(d1 z (branchLog z)+d2 z (branchLog z)+
      (1+z)^2*d3 z (branchLog z)/(z^3+3*z)) := by
  unfold cbar c1 c2 c3
  rw [branch_triangle]
  unfold branchA
  have hb : branchB z ≠ 0 := (branchB_pos z).ne'
  have hd : z^3+3*z ≠ 0 := by positivity
  field_simp
  ring

/-- The remaining sign in `lem:certcoef`, without numerical hypotheses. -/
theorem cbar_neg {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) : cbar z < 0 := by
  rw [cbar_scaled hz]
  exact mul_neg_of_pos_of_neg (pow_pos (branchB_pos z) _) (normalized_bar_neg hz hz40)

/-- Full sign conclusion of `lem:certcoef`. -/
theorem certificate_signs {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    gamma z (branchLog z) < 0 ∧ 0 < c1 z ∧ 0 < c2 z ∧ c3 z < 0 ∧
      0 < c4 z ∧ cbar z < 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := coefficient_signs hz hz40
  exact ⟨gamma_branch_neg hz hz40, h1, h2, h3, h4, cbar_neg hz hz40⟩

/-- Value zero and all three ordinary partial derivatives zero. -/
def IsContact (z x y w : ℝ) : Prop :=
  psi z x y w = 0 ∧ HasDerivAt (fun u => psi z u y w) 0 x ∧
  HasDerivAt (fun u => psi z x u w) 0 y ∧ HasDerivAt (fun u => psi z x y u) 0 w

theorem IsContact.swap_xy {z x y w : ℝ} (h : IsContact z x y w) :
    IsContact z y x w := by
  obtain ⟨hv, hx, hy, hw⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [psi_swap_xy]
    exact hv
  · convert hy using 1
    funext u
    exact psi_swap_xy z u x w
  · convert hx using 1
    funext u
    exact psi_swap_xy z y u w
  · convert hw using 1
    funext u
    exact psi_swap_xy z y x u

theorem IsContact.swap_xw {z x y w : ℝ} (h : IsContact z x y w) :
    IsContact z w y x := by
  obtain ⟨hv, hx, hy, hw⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [psi_swap_xw]
    exact hv
  · convert hw using 1
    funext u
    exact psi_swap_xw z u y x
  · convert hy using 1
    funext u
    exact psi_swap_xw z w u x
  · convert hx using 1
    funext u
    exact psi_swap_xw z w y u

/-- Complete tangency conclusion of `lem:certcoef`, now with no nonvanishing
hypothesis: the denominator sign has been proved on the stated interval. -/
theorem certificate_contacts {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40) :
    IsContact z (branchA z) (branchA z) (branchA z) ∧
    IsContact z (branchA z) (branchB z) (branchB z) ∧
    IsContact z (branchB z) (branchA z) (branchB z) ∧
    IsContact z (branchB z) (branchB z) (branchA z) := by
  have hz1 : z < 1 := by linarith
  have hg := (gamma_branch_neg hz hz40).ne
  have ha : IsContact z (branchA z) (branchA z) (branchA z) :=
    ⟨psi_aaa hz hz1 hg, psi_aaa_partial_tangencies hz hz1 hg⟩
  have hb : IsContact z (branchA z) (branchB z) (branchB z) :=
    ⟨psi_abb hz hz1 hg, psi_abb_partial_tangencies hz hz1 hg⟩
  exact ⟨ha, hb, hb.swap_xy, hb.swap_xw⟩

end SparseLowerTail.Certificate

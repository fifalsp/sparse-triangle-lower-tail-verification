import SparseLowerTail.Section04.BipodalDefinitions
import SparseLowerTail.Section04.BipodalAlgebra
import SparseLowerTail.Section04.BipodalKernel
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Integral representation and integration positivity bridge for `lem:J`. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section04

/-- The integrable vector density in the moment representation. -/
def bipodalWeightedPhi (x y s : ℝ) : Fin 4 → ℝ := fun i => bipodalPhi x y s i / s^2

theorem bipodalPhi_continuous (x y : ℝ) : Continuous (bipodalPhi x y) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun s : ℝ => s-x); fun_prop
  · change Continuous (fun s : ℝ => max (s-y) 0); fun_prop
  · change Continuous (fun s : ℝ => (s^2-x^2)/2); fun_prop
  · change Continuous (fun s : ℝ => max (s^2-y^2) 0/2); fun_prop

theorem bipodalWeightedPhi_continuousOn {x y : ℝ} (hx : 0 < x) :
    ContinuousOn (bipodalWeightedPhi x y) (Icc x 1) := by
  apply continuousOn_pi.mpr
  intro i
  exact ((continuous_apply i).comp (bipodalPhi_continuous x y)).continuousOn.div
    (continuous_id.pow 2).continuousOn (fun s hs => pow_ne_zero 2 (hx.trans_le hs.1).ne')

theorem bipodalWeightedPhi_integrable {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    IntervalIntegrable (bipodalWeightedPhi x y) volume x 1 :=
  (bipodalWeightedPhi_continuousOn hx).intervalIntegrable_of_Icc hx1

private theorem linear_moment {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ s in a..1, (s-a)/s^2) = -Real.log a-(1-a) := by
  have hint : IntervalIntegrable (fun s : ℝ => (s-a)/s^2) volume a 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc ha1
    exact (continuous_id.sub continuous_const).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun s hs => pow_ne_zero 2 (ha.trans_le hs.1).ne')
  have hd (s : ℝ) (hs : s ∈ uIcc a 1) :
      HasDerivAt (fun s : ℝ => Real.log s+a*s⁻¹) ((s-a)/s^2) s := by
    rw [uIcc_of_le ha1] at hs
    have hs0 : s ≠ 0 := (ha.trans_le hs.1).ne'
    convert (Real.hasDerivAt_log hs0).add (((hasDerivAt_id s).inv hs0).const_mul a) using 1
    dsimp
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [Real.log_one, inv_one, mul_one, zero_add]
  field_simp
  ring

private theorem quadratic_moment {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ s in a..1, (s^2-a^2)/2/s^2) = (1-a)-(1-a^2)/2 := by
  have hint : IntervalIntegrable (fun s : ℝ => (s^2-a^2)/2/s^2) volume a 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc ha1
    exact (((continuous_id.pow 2).sub continuous_const).div_const 2).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun s hs => pow_ne_zero 2 (ha.trans_le hs.1).ne')
  have hd (s : ℝ) (hs : s ∈ uIcc a 1) :
      HasDerivAt (fun s : ℝ => (s+a^2*s⁻¹)/2) ((s^2-a^2)/2/s^2) s := by
    rw [uIcc_of_le ha1] at hs
    have hs0 : s ≠ 0 := (ha.trans_le hs.1).ne'
    convert ((hasDerivAt_id s).add (((hasDerivAt_id s).inv hs0).const_mul (a^2))).div_const 2 using 1
    dsimp
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [inv_one, mul_one]
  field_simp
  ring

private theorem clipped_linear_moment {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    (∫ s in x..1, max (s-y) 0/s^2) = -Real.log y-(1-y) := by
  have hy : 0 < y := hx.trans_le hxy
  have hf : ContinuousOn (fun s : ℝ => max (s-y) 0/s^2) (Icc x 1) :=
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun s hs => pow_ne_zero 2 (hx.trans_le hs.1).ne')
  have ha := (hf.mono (Icc_subset_Icc le_rfl hy1)).intervalIntegrable_of_Icc (μ := volume) hxy
  have hb := (hf.mono (Icc_subset_Icc hxy le_rfl)).intervalIntegrable_of_Icc (μ := volume) hy1
  have hzero : (∫ s in x..y, max (s-y) 0/s^2) = 0 := by
    calc
      _ = ∫ s in x..y, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hxy] at hs
        dsimp only
        rw [max_eq_right (sub_nonpos.mpr hs.2), zero_div]
      _ = 0 := by simp
  have heq : (∫ s in y..1, max (s-y) 0/s^2) = ∫ s in y..1, (s-y)/s^2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hy1] at hs
    dsimp only
    rw [max_eq_left (sub_nonneg.mpr hs.1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals ha hb, hzero, zero_add, heq]
  exact linear_moment hy hy1

private theorem clipped_quadratic_moment {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    (∫ s in x..1, max (s^2-y^2) 0/2/s^2) = (1-y)-(1-y^2)/2 := by
  have hy : 0 < y := hx.trans_le hxy
  have hf : ContinuousOn (fun s : ℝ => max (s^2-y^2) 0/2/s^2) (Icc x 1) :=
    ((((continuous_id.pow 2).sub continuous_const).max continuous_const).div_const 2).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun s hs => pow_ne_zero 2 (hx.trans_le hs.1).ne')
  have ha := (hf.mono (Icc_subset_Icc le_rfl hy1)).intervalIntegrable_of_Icc (μ := volume) hxy
  have hb := (hf.mono (Icc_subset_Icc hxy le_rfl)).intervalIntegrable_of_Icc (μ := volume) hy1
  have hzero : (∫ s in x..y, max (s^2-y^2) 0/2/s^2) = 0 := by
    calc
      _ = ∫ s in x..y, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hxy] at hs
        have hs0 : 0 ≤ s := hx.le.trans hs.1
        have hs2 : s^2-y^2 ≤ 0 := by nlinarith [hs.2]
        dsimp only
        rw [max_eq_right hs2, zero_div, zero_div]
      _ = 0 := by simp
  have heq : (∫ s in y..1, max (s^2-y^2) 0/2/s^2) = ∫ s in y..1, (s^2-y^2)/2/s^2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hy1] at hs
    have hs2 : 0 ≤ s^2-y^2 := by nlinarith [hs.1]
    dsimp only
    rw [max_eq_left hs2]
  rw [← intervalIntegral.integral_add_adjacent_intervals ha hb, hzero, zero_add, heq]
  exact quadratic_moment hy hy1

/-- The four logarithmic moments, proved by elementary antiderivatives. -/
theorem bipodalPhiHat_moment {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    bipodalPhiHat x y = bipodalPhi x y 1 + ∫ s in x..1, bipodalWeightedPhi x y s := by
  have hx1 := hxy.trans hy1
  have hy : 0 < y := hx.trans_le hxy
  have hInt := bipodalWeightedPhi_integrable (y := y) hx hx1
  have hcoord (i : Fin 4) : (∫ s in x..1, bipodalWeightedPhi x y s) i =
      ∫ s in x..1, bipodalPhi x y s i/s^2 :=
    ((ContinuousLinearMap.proj i : (Fin 4 → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hInt).symm
  ext i
  rw [Pi.add_apply, hcoord]
  fin_cases i
  · change -Real.log x = 1-x + ∫ s in x..1, (s-x)/s^2
    rw [linear_moment hx hx1]
    ring
  · change -Real.log y = max (1-y) 0 + ∫ s in x..1, max (s-y) 0/s^2
    rw [clipped_linear_moment hx hxy hy1, max_eq_left (sub_nonneg.mpr hy1)]
    ring
  · change 1-x = (1^2-x^2)/2 + ∫ s in x..1, (s^2-x^2)/2/s^2
    rw [quadratic_moment hx hx1]
    ring
  · change 1-y = max (1^2-y^2) 0/2 + ∫ s in x..1, max (s^2-y^2) 0/2/s^2
    rw [clipped_quadratic_moment hx hxy hy1]
    have hy2 : 0 ≤ 1^2-y^2 := by nlinarith
    rw [max_eq_left hy2]
    ring

private def bilinearLeft (x y : ℝ) (w : Fin 4 → ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := bipodalBilinear x y v w
  map_add' v u := by simp only [bipodalBilinear, Pi.add_apply]; ring
  map_smul' c v := by simp only [bipodalBilinear, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def bilinearRight (x y : ℝ) (v : Fin 4 → ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun w := bipodalBilinear x y v w
  map_add' v u := by simp only [bipodalBilinear, Pi.add_apply]; ring
  map_smul' c v := by simp only [bipodalBilinear, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem bilinear_integral_left {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (w : Fin 4 → ℝ) :
    bipodalBilinear x y (∫ s in x..1, bipodalWeightedPhi x y s) w =
      ∫ s in x..1, bipodalBilinear x y (bipodalWeightedPhi x y s) w := by
  exact ((bilinearLeft x y w).toContinuousLinearMap.intervalIntegral_comp_comm
    (bipodalWeightedPhi_integrable hx hx1)).symm

private theorem bilinear_integral_right {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (v : Fin 4 → ℝ) :
    bipodalBilinear x y v (∫ s in x..1, bipodalWeightedPhi x y s) =
      ∫ s in x..1, bipodalBilinear x y v (bipodalWeightedPhi x y s) := by
  exact ((bilinearRight x y v).toContinuousLinearMap.intervalIntegral_comp_comm
    (bipodalWeightedPhi_integrable hx hx1)).symm

theorem bipodalBilinear_hat_eq_J (x y : ℝ) :
    bipodalBilinear x y (bipodalPhiHat x y) (bipodalPhiHat x y) = bipodalJ x y := by
  simp [bipodalBilinear, bipodalPhiHat, bipodalJ]
  ring

/-- `s4:eq:Jrep`, with every moment and exchange with integration proved. -/
theorem bipodalJ_integral_representation {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    bipodalJ x y = bipodalOmega x y 1 1 +
      2*(∫ s in x..1, bipodalOmega x y s 1/s^2) +
      ∫ s in x..1, ∫ t in x..1, bipodalOmega x y s t/s^2/t^2 := by
  have hx1 := hxy.trans hy1
  let M := ∫ s in x..1, bipodalWeightedPhi x y s
  let v := bipodalPhi x y 1
  have hcross : bipodalBilinear x y M v = ∫ s in x..1, bipodalOmega x y s 1/s^2 := by
    rw [bilinear_integral_left hx hx1]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    unfold bipodalBilinear bipodalWeightedPhi bipodalOmega
    dsimp [v]
    unfold bipodalBilinear
    ring
  have hdouble : bipodalBilinear x y M M =
      ∫ s in x..1, ∫ t in x..1, bipodalOmega x y s t/s^2/t^2 := by
    rw [bilinear_integral_left hx hx1]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [bilinear_integral_right hx hx1]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    unfold bipodalOmega bipodalBilinear bipodalWeightedPhi
    ring
  have hexpand : bipodalBilinear x y (v+M) (v+M) =
      bipodalBilinear x y v v+2*bipodalBilinear x y M v+bipodalBilinear x y M M := by
    simp only [bipodalBilinear, Pi.add_apply]
    ring
  rw [← bipodalBilinear_hat_eq_J, bipodalPhiHat_moment hx hxy hy1]
  change bipodalBilinear x y (v+M) (v+M) = _
  rw [hexpand, hcross, hdouble]
  rfl

/-- The one-variable weighted kernel is continuous on the integration interval. -/
theorem bipodalOmega_single_continuousOn {x y : ℝ} (hx : 0 < x) :
    ContinuousOn (fun s => bipodalOmega x y s 1/s^2) (Icc x 1) := by
  have hf : Continuous (fun s => bipodalOmega x y s 1) :=
    (bilinearLeft x y (bipodalPhi x y 1)).toContinuousLinearMap.continuous.comp
      (bipodalPhi_continuous x y)
  exact hf.continuousOn.div (continuous_id.pow 2).continuousOn
    (fun s hs => pow_ne_zero 2 (hx.trans_le hs.1).ne')

/-- A strictly positive contribution already comes from the single integral.
This slightly strengthens/simplifies the final integration step in the paper. -/
theorem bipodalOmega_single_integral_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    0 < ∫ s in x..1, bipodalOmega x y s 1/s^2 := by
  have hx1 := hxy.trans hy
  apply intervalIntegral.integral_pos hx1 (bipodalOmega_single_continuousOn hx)
  · intro s hs
    exact div_nonneg (bipodalOmega_nonneg hx hxy hy ⟨hs.1.le,hs.2⟩ ⟨hx1.le,le_rfl⟩)
      (sq_nonneg s)
  · have hm : (x+1)/2 ∈ Ioo x 1 := by constructor <;> linarith
    refine ⟨(x+1)/2, ⟨hm.1.le,hm.2.le⟩, ?_⟩
    exact div_pos (bipodalOmega_single_pos hx hxy hy hm)
      (sq_pos_of_pos (hx.trans hm.1))

/-- Nonnegativity of the double integral follows directly from the actual
pointwise kernel inequality; no integrability or positivity assumption is added. -/
theorem bipodalOmega_double_integral_nonneg {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    0 ≤ ∫ s in x..1, ∫ t in x..1, bipodalOmega x y s t/s^2/t^2 := by
  have hx1 := (hxy.trans hy).le
  apply intervalIntegral.integral_nonneg hx1
  intro s hs
  apply intervalIntegral.integral_nonneg hx1
  intro t ht
  exact div_nonneg (div_nonneg (bipodalOmega_nonneg hx hxy hy hs ht) (sq_nonneg s)) (sq_nonneg t)

/-- `lem:J`: the explicit logarithmic function is strictly positive throughout
0<x<y<1, with its integral representation and pointwise kernel proved in Lean. -/
theorem bipodalJ_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1) : 0 < bipodalJ x y := by
  have hcorner := bipodalOmega_nonneg hx hxy hy ⟨(hxy.trans hy).le,le_rfl⟩
    ⟨(hxy.trans hy).le,le_rfl⟩
  have hsingle := bipodalOmega_single_integral_pos hx hxy hy
  have hdouble := bipodalOmega_double_integral_nonneg hx hxy hy
  rw [bipodalJ_integral_representation hx hxy.le hy.le]
  linarith

/-- `prop:bipodal`: the complete stationary-system rigidity result. The former
internal J-positivity obligation is discharged by `bipodalJ_pos`. -/
theorem bipodal_rigidity {c μ a d b : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hμ : 0 < μ)
    (ha : 0 < a) (hd : 0 < d) (hb : 0 < b)
    (hne : ¬(a = b ∧ d = b)) (h : BipodalStationary c μ a d b) :
    a = d ∧ a < b ∧ c = 1/2 :=
  bipodal_rigidity_of_J (fun _ _ hx hxy hy => bipodalJ_pos hx hxy hy)
    hc hμ ha hd hb hne h

end SparseLowerTail.Section04

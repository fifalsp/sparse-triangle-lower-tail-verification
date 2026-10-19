import SparseLowerTail.Section04.EntropyGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The sharp quadratic entropy bound from manuscript lem:bregman.
The proof follows the integral-remainder argument in the paper. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SparseLowerTail.Section02

def beta (s : ℝ) : ℝ := (s-1-Real.log s)/(1-s)^2
def bregmanRatio (s u : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..1, (1-θ)/(s+θ*(u-s))

private theorem affine_pos {s u θ : ℝ} (hs : 0 < s) (hu : 0 < u)
    (hθ : θ ∈ Icc (0:ℝ) 1) : 0 < s+θ*(u-s) := by
  rcases lt_or_eq_of_le hθ.2 with ht | rfl
  · have h1 : 0 < (1-θ)*s := mul_pos (sub_pos.mpr ht) hs
    have h2 : 0 ≤ θ*u := mul_nonneg hθ.1 hu.le
    nlinarith
  · simpa using hu

private theorem ratio_continuous {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    ContinuousOn (fun θ : ℝ => (1-θ)/(s+θ*(u-s))) (Icc 0 1) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro θ hθ
    exact ne_of_gt (affine_pos hs hu hθ)

private theorem ratio_integrable {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    IntervalIntegrable (fun θ : ℝ => (1-θ)/(s+θ*(u-s))) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa using ratio_continuous hs hu

/-- Taylor's integral remainder, proved through its elementary primitive. -/
theorem bregman_remainder {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    entropy u - entropy s - (u-s)*Real.log s = (u-s)^2*bregmanRatio s u := by
  let f := fun θ : ℝ => (1-θ)*(u-s)*Real.log (s+θ*(u-s)) + entropy (s+θ*(u-s))
  have hd : ∀ θ ∈ uIcc (0:ℝ) 1, HasDerivAt f
      ((u-s)^2*((1-θ)/(s+θ*(u-s)))) θ := by
    intro θ hθ
    have ht : θ ∈ Icc (0:ℝ) 1 := by simpa using hθ
    have hv := ne_of_gt (affine_pos hs hu ht)
    have ha := ((hasDerivAt_id θ).mul_const (u-s)).const_add s
    have hf := (((((hasDerivAt_id θ).const_sub 1).mul_const (u-s)).mul (ha.log hv)).add
      ((Section04.hasDerivAt_entropy hv).comp θ ha))
    convert hf using 1
    simp only [id_eq]
    field_simp
    ring
  have hi := (ratio_integrable hs hu).const_mul ((u-s)^2)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at he
  dsimp [f] at he
  simp only [sub_self, zero_mul, zero_add, add_zero, sub_zero, one_mul] at he
  simp only [show s+(u-s)=u by ring] at he
  unfold bregmanRatio
  linarith

/-- The ratio at the right endpoint is exactly the paper's beta(s). -/
theorem ratio_one_eq_beta {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    bregmanRatio s 1 = beta s := by
  have h := bregman_remainder hs.1 (by norm_num : (0:ℝ)<1)
  have hn : (1-s)^2 ≠ 0 := pow_ne_zero _ (ne_of_gt (sub_pos.mpr hs.2))
  apply (eq_div_iff hn).mpr
  unfold entropy at h
  norm_num at h
  nlinarith [h]

/-- The remainder ratio decreases with its endpoint. -/
theorem ratio_antitone {s u v : ℝ} (hs : 0 < s) (hu : 0 < u) (hv : 0 < v)
    (huv : u ≤ v) : bregmanRatio s v ≤ bregmanRatio s u := by
  apply intervalIntegral.integral_mono_on (by norm_num) (ratio_integrable hs hv) (ratio_integrable hs hu)
  intro θ hθ
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr hθ.2) (affine_pos hs hu hθ)
  nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr huv)]

/-- The universal coefficient lower bound in lem:bregman. -/
theorem beta_ge_half {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) : (1/2:ℝ) ≤ beta s := by
  rw [← ratio_one_eq_beta hs]
  have hi : IntervalIntegrable (fun θ : ℝ => 1-θ) volume 0 1 :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (a:=0) (b:=1) (by norm_num) hi
    (ratio_integrable hs.1 (by norm_num : (0:ℝ)<1)) (fun θ hθ => by
      have hp := affine_pos hs.1 (by norm_num : (0:ℝ)<1) hθ
      apply (le_div_iff₀ hp).mpr
      have hv : s+θ*(1-s) ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hs.2.le)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hv)])
  have he : (∫ θ in (0:ℝ)..1, (1-θ)) = (1/2:ℝ) := by
    rw [intervalIntegral.integral_sub (show IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 from intervalIntegrable_const)
      (show IntervalIntegrable (fun θ : ℝ => θ) volume 0 1 from continuous_id.intervalIntegrable _ _)]
    norm_num
  simpa only [he] using h

/-- The endpoint u=0 needs no improper integral: the log inequality gives its bound. -/
theorem beta_mul_sq_le_self {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) : beta s * s^2 ≤ s := by
  have hl := Real.one_sub_inv_le_log_of_pos hs.1
  have hmul := mul_le_mul_of_nonneg_left hl hs.1.le
  have hc : s*s⁻¹ = 1 := mul_inv_cancel₀ hs.1.ne'
  have hden : 0 < (1-s)^2 := sq_pos_of_pos (sub_pos.mpr hs.2)
  unfold beta
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hmul)]

/-- Full sharp Bregman inequality from lem:bregman, including u=0. -/
theorem entropy_bregman {s u : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    beta s*(u-s)^2 ≤ entropy u-entropy s-(u-s)*Real.log s := by
  rcases eq_or_lt_of_le hu.1 with he | hp
  · subst u
    have h := beta_mul_sq_le_self hs
    simpa [entropy] using h
  · rw [bregman_remainder hs.1 hp]
    have h := ratio_antitone hs.1 hp (by norm_num : (0:ℝ)<1) hu.2
    rw [ratio_one_eq_beta hs] at h
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg (u-s))]

end SparseLowerTail.Section02

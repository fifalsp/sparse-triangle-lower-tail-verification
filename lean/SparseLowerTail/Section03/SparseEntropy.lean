import SparseLowerTail.Section02.Bregman

/-! Uniform comparison of Bernoulli relative entropy with sparse entropy (`lem:fp`). -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SparseLowerTail.Section03
open Section02

/-- Bernoulli relative entropy, with the usual continuous zero convention. -/
def bernoulliEntropy (p q : ℝ) : ℝ :=
  q * Real.log (q/p) + (1-q) * Real.log ((1-q)/(1-p))

theorem bregmanRatio_self {s : ℝ} (hs : 0 < s) : bregmanRatio s s = 1/(2*s) := by
  unfold bregmanRatio
  simp only [sub_self, mul_zero, add_zero]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  have hi : (∫ θ in (0:ℝ)..1, (1-θ)) = (1/2:ℝ) := by
    rw [intervalIntegral.integral_sub
      (show IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 from intervalIntegrable_const)
      (show IntervalIntegrable (fun θ : ℝ => θ) volume 0 1 from continuous_id.intervalIntegrable _ _)]
    norm_num
  rw [hi]
  field_simp [hs.ne']

/-- The entropy difference is the complementary Bernoulli Bregman remainder. -/
theorem sparse_entropy_remainder {p w : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) :
    bernoulliEntropy p (p*w)/p - entropy w =
      (entropy (1-p*w)-entropy (1-p)-((1-p*w)-(1-p))*Real.log (1-p))/p := by
  have hp0 := hp.1
  have hp1 := hp.2
  have hw0 := hw.1
  have hw1 := hw.2
  have hpw : 0 < 1-p*w := by nlinarith [mul_le_mul_of_nonneg_left hw.2 hp.1.le]
  have hquot : p*w/p=w := by field_simp [hp.1.ne']
  unfold bernoulliEntropy entropy
  rw [hquot, Real.log_div hpw.ne' (sub_pos.mpr hp.2).ne']
  field_simp [hp.1.ne']
  ring

/-- Full uniform entropy comparison, including w=0 and w=1. -/
theorem sparse_entropy_bounds {p w : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) :
    0 ≤ bernoulliEntropy p (p*w)/p - entropy w ∧
    bernoulliEntropy p (p*w)/p - entropy w ≤ p*(1-w)^2/(2*(1-p)) ∧
    p*(1-w)^2/(2*(1-p)) ≤ p/(2*(1-p)) := by
  have hp0 := hp.1
  have hp1 := hp.2
  have hw0 := hw.1
  have hw1 := hw.2
  have hs : 1-p ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hu : 1-p*w ∈ Icc (0:ℝ) 1 := by
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hw.2 hp.1.le,
      mul_nonneg hp.1.le hw.1]
  have hsu : 1-p ≤ 1-p*w := by nlinarith [mul_le_mul_of_nonneg_left hw.2 hp.1.le]
  have hup : 0 < 1-p*w := hs.1.trans_le hsu
  rw [sparse_entropy_remainder hp hw]
  have hb := entropy_bregman hs hu
  have hβ : 0 ≤ beta (1-p) := (by norm_num : (0:ℝ) ≤ 1/2).trans (beta_ge_half hs)
  have hn := mul_nonneg hβ (sq_nonneg ((1-p*w)-(1-p)))
  have hr := bregman_remainder hs.1 hup
  have hratio := ratio_antitone hs.1 hs.1 hup hsu
  rw [bregmanRatio_self hs.1] at hratio
  refine ⟨div_nonneg (by linarith) hp.1.le, ?_, ?_⟩
  · rw [hr]
    have hm := mul_le_mul_of_nonneg_left hratio (sq_nonneg ((1-p*w)-(1-p)))
    have hd := div_le_div_of_nonneg_right hm hp.1.le
    convert hd using 1
    field_simp [hp.1.ne', hs.1.ne']
    ring
  · apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) hs.1.le)
    have hh : (1-w)^2 ≤ 1 := by nlinarith [sq_nonneg w]
    nlinarith [mul_nonneg hp.1.le (sub_nonneg.mpr hh)]

end SparseLowerTail.Section03

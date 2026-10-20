import SparseLowerTail.Section03.SparseEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Finite relative entropy and event-probability transfer (`lem:entropy`(b)). -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section04

private theorem denominator_mul_entropy {q p : ℝ} (hs : p = 0 → q = 0) :
    p * entropy (q/p) = q*Real.log (q/p)-q+p := by
  by_cases hp : p=0
  · simp [hp, hs hp]
  · unfold entropy
    field_simp

/-- Log-sum inequality, allowing zero masses under absolute continuity. -/
theorem finite_log_sum {α : Type*} (s : Finset α) (q p : α → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hs : ∀ i ∈ s, p i=0 → q i=0) (hP : 0 < ∑ i ∈ s, p i) :
    (∑ i ∈ s, q i)*Real.log ((∑ i ∈ s, q i)/(∑ i ∈ s, p i)) ≤
      ∑ i ∈ s, q i*Real.log (q i/p i) := by
  let P := ∑ i ∈ s, p i
  have hP' : P ≠ 0 := hP.ne'
  have hj := strictConvexOn_entropy.convexOn.map_sum_le
    (t:=s) (w:=fun i => p i/P) (p:=fun i => q i/p i)
    (fun i hi => div_nonneg (hp i hi) hP.le)
    (by rw [← Finset.sum_div]; exact div_self hP')
    (fun i hi => div_nonneg (hq i hi) (hp i hi))
  simp only [smul_eq_mul] at hj
  have hmean : (∑ i ∈ s, (p i/P)*(q i/p i)) = (∑ i ∈ s, q i)/P := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hpi : p i=0
    · simp [hpi, hs i hi hpi]
    · field_simp
  rw [hmean] at hj
  have hterms : (∑ i ∈ s, (p i/P)*entropy (q i/p i)) =
      ((∑ i ∈ s, q i*Real.log (q i/p i))-(∑ i ∈ s, q i)+P)/P := by
    calc
      (∑ i ∈ s, (p i/P)*entropy (q i/p i)) =
          ∑ i ∈ s, (q i*Real.log (q i/p i)-q i+p i)/P := by
        apply Finset.sum_congr rfl
        intro i hi
        have hh := denominator_mul_entropy (hs i hi)
        calc
          (p i/P)*entropy (q i/p i) = (p i*entropy (q i/p i))/P := by ring
          _ = (q i*Real.log (q i/p i)-q i+p i)/P := by rw [hh]
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hterms] at hj
  have hm := mul_le_mul_of_nonneg_left hj hP.le
  have he : P*entropy ((∑ i ∈ s, q i)/P) =
      (∑ i ∈ s, q i)*Real.log ((∑ i ∈ s, q i)/P)-(∑ i ∈ s, q i)+P :=
    denominator_mul_entropy (fun h => (hP' h).elim)
  rw [he] at hm
  have heq : P * (((∑ i ∈ s, q i*Real.log (q i/p i))-(∑ i ∈ s, q i)+P)/P) =
      (∑ i ∈ s, q i*Real.log (q i/p i))-(∑ i ∈ s, q i)+P := by field_simp
  rw [heq] at hm
  exact (by dsimp [P] at hm; linarith)

private theorem mul_log_div (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    a*Real.log (a/b) = a*Real.log a-a*Real.log b := by
  by_cases ha : a=0
  · simp [ha]
  · rw [Real.log_div ha hb]; ring

/-- Binary entropy gives the constant log 2 in event-probability transfer. -/
theorem bernoulli_entropy_event_lower {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hx : x ∈ Icc (0:ℝ) 1) :
    x*Real.log (1/u)-Real.log 2 ≤ bernoulliEntropy u x := by
  have hh := Real.binEntropy_le_log_two (p:=x)
  have hn := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.2)
    (Real.log_nonpos (sub_pos.mpr hu.2).le (by linarith [hu.1]))
  unfold bernoulliEntropy
  rw [mul_log_div x hu.1.ne', mul_log_div (1-x) (sub_pos.mpr hu.2).ne']
  rw [one_div, Real.log_inv]
  unfold Real.binEntropy at hh
  simp only [Real.log_inv] at hh
  linarith

/-- Finite relative entropy in the zero-mass convention, under absolute continuity. -/
def finiteRelativeEntropy {α : Type*} [Fintype α] (q p : α → ℝ) : ℝ :=
  ∑ i, q i*Real.log (q i/p i)

/-- Grouping a finite law into an event and its complement decreases relative entropy. -/
theorem bernoulli_entropy_le_finiteRelativeEntropy {α : Type*} [Fintype α]
    (q p : α → ℝ) (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (hqsum : ∑ i, q i=1) (hpsum : ∑ i, p i=1)
    (hs : ∀ i, p i=0 → q i=0) (E : Finset α)
    (hu : (∑ i ∈ E, p i) ∈ Ioo (0:ℝ) 1) :
    bernoulliEntropy (∑ i ∈ E, p i) (∑ i ∈ E, q i) ≤ finiteRelativeEntropy q p := by
  classical
  have hpc : ∑ i ∈ Eᶜ, p i = 1-∑ i ∈ E, p i := by
    have h := Finset.sum_add_sum_compl E p
    rw [hpsum] at h
    linarith
  have hqc : ∑ i ∈ Eᶜ, q i = 1-∑ i ∈ E, q i := by
    have h := Finset.sum_add_sum_compl E q
    rw [hqsum] at h
    linarith
  have h1 := finite_log_sum E q p (fun i _ => hq i) (fun i _ => hp i)
    (fun i _ => hs i) hu.1
  have h2 := finite_log_sum Eᶜ q p (fun i _ => hq i) (fun i _ => hp i)
    (fun i _ => hs i) (by rw [hpc]; linarith [hu.2])
  rw [hpc, hqc] at h2
  have hsplit := Finset.sum_add_sum_compl E (fun i => q i*Real.log (q i/p i))
  unfold bernoulliEntropy finiteRelativeEntropy
  linarith

/-- The probability-transfer bound for every pair of finite laws with absolute continuity. -/
theorem finite_event_probability_le {α : Type*} [Fintype α]
    (q p : α → ℝ) (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (hqsum : ∑ i, q i=1) (hpsum : ∑ i, p i=1)
    (hs : ∀ i, p i=0 → q i=0) (E : Finset α)
    (hu : (∑ i ∈ E, p i) ∈ Ioo (0:ℝ) 1) :
    (∑ i ∈ E, q i) ≤ (finiteRelativeEntropy q p+Real.log 2)/Real.log (1/(∑ i ∈ E, p i)) := by
  classical
  have hx : (∑ i ∈ E, q i) ∈ Icc (0:ℝ) 1 := by
    refine ⟨Finset.sum_nonneg (fun i _ => hq i), ?_⟩
    rw [← hqsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun i _ _ => hq i)
  have hlo := bernoulli_entropy_event_lower hu hx
  have hhi := bernoulli_entropy_le_finiteRelativeEntropy q p hq hp hqsum hpsum hs E hu
  have hlog : 0 < Real.log (1/(∑ i ∈ E, p i)) :=
    Real.log_pos ((one_lt_div hu.1).mpr hu.2)
  apply (le_div_iff₀ hlog).mpr
  linarith

/-- Absolute continuity also transfers zero-probability events. -/
theorem finite_event_probability_zero {α : Type*} (q p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∀ i, p i=0 → q i=0) (E : Finset α)
    (hu : ∑ i ∈ E, p i=0) : ∑ i ∈ E, q i=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply hs i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp j)).mp hu i hi

end SparseLowerTail.Section03

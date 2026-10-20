import SparseLowerTail.Section03.ConditionedProductEntropy
import SparseLowerTail.Section03.HarrisConditioning

/-! Finite-law estimates for the good-event argument in thm:reduction(b). -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- Markov's bound for any finite event on which the nonnegative observable exceeds t. -/
theorem finite_event_markov (μ X : α → ℝ) (hμ : ∀ a, 0≤μ a) (hX : ∀ a, 0≤X a)
    (E : Finset α) {t : ℝ} (ht : 0<t) (hE : ∀ a∈E, t≤X a) :
    finiteEventMass μ E≤(∑ a, μ a*X a)/t := by
  apply (le_div_iff₀ ht).mpr
  rw [finiteEventMass,Finset.sum_mul]
  calc
    ∑ a∈E, μ a*t≤∑ a∈E, μ a*X a :=
      Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hE a ha) (hμ a))
    _≤∑ a, μ a*X a := Finset.sum_le_univ_sum_of_nonneg (fun a => mul_nonneg (hμ a) (hX a))

/-- A nonnegative observable bounded below by v on G has mean at least v minus the bad mass. -/
theorem finite_mean_lower_of_good (μ X : α → ℝ) (hμ : ∀ a, 0≤μ a)
    (hμsum : ∑ a, μ a=1) (hX : ∀ a, 0≤X a) (G : Finset α)
    {v : ℝ} (hv : v≤1) (hG : ∀ a∈G, v≤X a) :
    v-finiteEventMass μ Gᶜ≤∑ a, μ a*X a := by
  have hpoint : ∀ a, v-(if a∈Gᶜ then (1:ℝ) else 0)≤X a := by
    intro a
    by_cases ha : a∈G
    · simpa [ha] using hG a ha
    · simp only [Finset.mem_compl,ha,not_false_eq_true,ite_true]
      linarith [hX a]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (hμ a))
  simpa only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hμsum,one_mul,mul_ite,mul_one,
    mul_zero,Finset.sum_ite_mem,Finset.univ_inter,finiteEventMass] using hh

/-- The excess positive part is controlled by the mean and the mass outside the good event. -/
theorem finite_excess_mean_le (μ X : α → ℝ) (hμ : ∀ a, 0≤μ a)
    (hμsum : ∑ a, μ a=1) (hX : ∀ a, 0≤X a) (G : Finset α)
    {v : ℝ} (hv : v≤1) (hG : ∀ a∈G, v≤X a) :
    (∑ a, μ a*max (X a-v) 0)≤(∑ a, μ a*X a)-v+finiteEventMass μ Gᶜ := by
  have hpoint : ∀ a, max (X a-v) 0≤X a-v+(if a∈Gᶜ then (1:ℝ) else 0) := by
    intro a
    by_cases ha : a∈G
    · simp only [Finset.mem_compl,ha,not_true_eq_false,ite_false,add_zero]
      exact max_eq_left (sub_nonneg.mpr (hG a ha)) |>.le
    · simp only [Finset.mem_compl,ha,not_false_eq_true,ite_true]
      apply max_le
      · linarith
      · linarith [hX a]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (hμ a))
  simpa only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,
    hμsum,one_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_mem,Finset.univ_inter,finiteEventMass] using hh

/-- The joint entropy budget bounds the remaining dependence once the cost has a good-event lower bound. -/
theorem finite_dependence_mean_le (μ X D : α → ℝ) (hμ : ∀ a, 0≤μ a)
    (hμsum : ∑ a, μ a=1) (hX : ∀ a, 0≤X a) (G : Finset α)
    {v R : ℝ} (hv : v≤1) (hG : ∀ a∈G, v≤X a)
    (hbudget : (∑ a, μ a*D a)+(∑ a, μ a*X a)≤R) :
    (∑ a, μ a*D a)≤R-v+finiteEventMass μ Gᶜ := by
  have hh := finite_mean_lower_of_good μ X hμ hμsum hX G hv hG
  linarith

/-- The four simultaneous good events used in the conditioned-structure argument. -/
theorem finite_four_bad_events_le (μ : α → ℝ) (hμ : ∀ a, 0≤μ a)
    (E₁ E₂ E₃ E₄ : Finset α) :
    finiteEventMass μ (E₁∪E₂∪E₃∪E₄)≤
      finiteEventMass μ E₁+finiteEventMass μ E₂+finiteEventMass μ E₃+finiteEventMass μ E₄ := by
  have htwo : ∀ E F : Finset α, finiteEventMass μ (E∪F)≤finiteEventMass μ E+finiteEventMass μ F := by
    intro E F
    calc
      finiteEventMass μ (E∪F) = ∑ a, if a∈E∪F then μ a else 0 := by simp only [Finset.sum_ite_mem,Finset.univ_inter,finiteEventMass]
      _ ≤ ∑ a, ((if a∈E then μ a else 0)+(if a∈F then μ a else 0)) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a∈E <;> by_cases hb : a∈F <;> simp [ha,hb,hμ a]
      _ = finiteEventMass μ E+finiteEventMass μ F := by simp [Finset.sum_add_distrib,finiteEventMass]
  exact (htwo (E₁∪E₂∪E₃) E₄).trans
    (add_le_add_right ((htwo (E₁∪E₂) E₃).trans (add_le_add_right (htwo E₁ E₂) _)) _)

end SparseLowerTail.Section03

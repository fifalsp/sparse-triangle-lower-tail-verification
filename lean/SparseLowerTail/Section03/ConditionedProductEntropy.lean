import SparseLowerTail.Section03.ProductMarginalEntropy

/-! Entropy bounds for a finite law conditioned on an event, with Bernoulli coordinates. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

def bernoulliMass (p : ℝ) : Bool → ℝ
  | false => 1-p
  | true => p

theorem bernoulliMass_sum (p : ℝ) : ∑ b, bernoulliMass p b=1 := by
  simp [bernoulliMass]

theorem bernoulliMass_pos {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (b : Bool) :
    0 < bernoulliMass p b := by
  cases b
  · exact sub_pos.mpr hp.2
  · exact hp.1

/-- The coordinate cost is exactly the scalar Bernoulli relative entropy in the manuscript. -/
theorem bernoulli_marginal_entropy {α : Type*} [Fintype α] (q : α → ℝ)
    (hqsum : ∑ z, q z=1) (f : α → Bool) (p : ℝ) :
    finiteRelativeEntropy (finiteMarginal q f) (bernoulliMass p) =
      bernoulliEntropy p (finiteMarginal q f true) := by
  have hm := finiteMarginal_sum q f
  rw [hqsum] at hm
  have hf : finiteMarginal q f false = 1-finiteMarginal q f true := by
    simp only [Fintype.sum_bool] at hm
    linarith
  simp only [finiteRelativeEntropy, Fintype.sum_bool, bernoulliMass, hf, bernoulliEntropy]

/-- The two expected conditional costs are bounded by the original joint entropy. -/
theorem expected_dependence_add_marginal_entropy_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (q : α → (ι → Bool) → ℝ) (hq : ∀ y z, 0 ≤ q y z)
    (hqsum : ∑ y, ∑ z, q y z=1) (py : α → ℝ)
    (hpy : ∀ y, 0 < py y) (hpysum : ∑ y, py y=1)
    {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    (∑ y, finiteRowMass q y*finiteRelativeEntropy (finiteConditional q y)
      (productMarginals (finiteConditional q y))) +
    (∑ y, finiteRowMass q y*∑ i, bernoulliEntropy p
      (finiteMarginal (finiteConditional q y) (fun z => z i) true)) ≤
    finiteRelativeEntropy (fun yz : α×(ι → Bool) => q yz.1 yz.2)
      (fun yz => py yz.1*finiteProductMass (fun _i : ι => bernoulliMass p) yz.2) := by
  have he : ∀ y,
      finiteRowMass q y*finiteRelativeEntropy (finiteConditional q y)
        (finiteProductMass (fun _i : ι => bernoulliMass p)) =
      finiteRowMass q y*finiteRelativeEntropy (finiteConditional q y)
        (productMarginals (finiteConditional q y)) +
      finiteRowMass q y*∑ i, bernoulliEntropy p
        (finiteMarginal (finiteConditional q y) (fun z => z i) true) := by
    intro y
    by_cases hy : finiteRowMass q y=0
    · simp [hy]
    · rw [product_marginal_entropy_decomposition (finiteConditional q y)
        (finiteConditional_nonneg q hq y) (fun _i : ι => bernoulliMass p)
        (fun _i b => bernoulliMass_pos hp b)]
      simp_rw [bernoulli_marginal_entropy _ (finiteConditional_sum q y hy)]
      ring
  rw [← Finset.sum_add_distrib]
  simp_rw [← he]
  exact expected_conditional_entropy_le q hq hqsum py
    (finiteProductMass (fun _i : ι => bernoulliMass p)) hpy
    (finiteProductMass_pos _ (fun _i b => bernoulliMass_pos hp b)) hpysum

/-- Conditioning on a finite event of positive probability. -/
def finiteConditionedMass {α : Type*} [Fintype α] (p : α → ℝ) (E : Finset α) (a : α) : ℝ := by
  classical
  exact if a ∈ E then p a/(∑ a ∈ E, p a) else 0

theorem finiteConditionedMass_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (E : Finset α) (a : α) : 0 ≤ finiteConditionedMass p E a := by
  classical
  unfold finiteConditionedMass
  split_ifs
  · exact div_nonneg (hp a) (Finset.sum_nonneg (fun b _ => hp b))
  · exact le_rfl

theorem finiteConditionedMass_sum {α : Type*} [Fintype α] (p : α → ℝ)
    (E : Finset α) (hE : 0 < ∑ a ∈ E, p a) : ∑ a, finiteConditionedMass p E a=1 := by
  classical
  simp only [finiteConditionedMass, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.sum_div]
  exact div_self hE.ne'

/-- Relative entropy of conditioning is minus the logarithm of the event probability. -/
theorem finiteConditionedMass_entropy {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 < p a) (E : Finset α) (hE : 0 < ∑ a ∈ E, p a) :
    finiteRelativeEntropy (finiteConditionedMass p E) p = -Real.log (∑ a ∈ E, p a) := by
  classical
  have he : ∀ a, finiteConditionedMass p E a*Real.log (finiteConditionedMass p E a/p a) =
      finiteConditionedMass p E a*Real.log (1/(∑ a ∈ E, p a)) := by
    intro a
    by_cases ha : a ∈ E
    · have hh : (p a/(∑ a ∈ E, p a))/p a=1/(∑ a ∈ E, p a) := by
        field_simp [(hp a).ne', hE.ne']
      simp only [finiteConditionedMass, if_pos ha, hh]
    · simp [finiteConditionedMass, ha]
  unfold finiteRelativeEntropy
  simp_rw [he]
  rw [← Finset.sum_mul, finiteConditionedMass_sum p E hE, one_mul, one_div, Real.log_inv]

/-- A joint law obtained by conditioning a product reference with unrevealed Bernoulli coordinates. -/
def conditionedBernoulliJoint {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (py : α → ℝ) (p : ℝ) (L : Finset (α×(ι → Bool))) (y : α) (z : ι → Bool) : ℝ :=
  finiteConditionedMass (fun yz : α×(ι → Bool) =>
    py yz.1*finiteProductMass (fun _i : ι => bernoulliMass p) yz.2) L (y,z)

/-- Full finite-law entropy budget of `lem:entropy`(a), with the conditional laws constructed. -/
theorem conditioned_bernoulli_entropy_bound {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (py : α → ℝ) (hpy : ∀ y, 0 < py y) (hpysum : ∑ y, py y=1)
    {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (L : Finset (α×(ι → Bool)))
    (hL : 0 < ∑ yz ∈ L, py yz.1*finiteProductMass (fun _i : ι => bernoulliMass p) yz.2) :
    let q := conditionedBernoulliJoint py p L
    (∑ y, finiteRowMass q y*finiteRelativeEntropy (finiteConditional q y)
      (productMarginals (finiteConditional q y))) +
    (∑ y, finiteRowMass q y*∑ i, bernoulliEntropy p
      (finiteMarginal (finiteConditional q y) (fun z => z i) true)) ≤
      -Real.log (∑ yz ∈ L, py yz.1*finiteProductMass (fun _i : ι => bernoulliMass p) yz.2) := by
  let q := conditionedBernoulliJoint py p L
  have href : ∀ yz : α×(ι → Bool),
      0 < py yz.1*finiteProductMass (fun _i : ι => bernoulliMass p) yz.2 :=
    fun yz => mul_pos (hpy yz.1) (finiteProductMass_pos _ (fun _i b => bernoulliMass_pos hp b) yz.2)
  have hq : ∀ y z, 0 ≤ q y z := fun y z =>
    finiteConditionedMass_nonneg _ (fun yz => (href yz).le) L (y,z)
  have hsum : ∑ y, ∑ z, q y z=1 := by
    have hh := finiteConditionedMass_sum _ L hL
    rw [Fintype.sum_prod_type] at hh
    exact hh
  have hh := expected_dependence_add_marginal_entropy_le q hq hsum py hpy hpysum hp
  have he := finiteConditionedMass_entropy _ href L hL
  exact hh.trans_eq he

/-- Actual conditional laws satisfy the event-probability bound against their own product marginals. -/
theorem conditional_product_event_probability_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (q : α → (ι → Bool) → ℝ) (hq : ∀ y z, 0 ≤ q y z) (y : α)
    (hy : 0 < finiteRowMass q y) (E : Finset (ι → Bool))
    (hu : (∑ z ∈ E, productMarginals (finiteConditional q y) z) ∈ Ioo (0:ℝ) 1) :
    (∑ z ∈ E, finiteConditional q y z) ≤
      (finiteRelativeEntropy (finiteConditional q y) (productMarginals (finiteConditional q y))+
        Real.log 2)/Real.log (1/(∑ z ∈ E, productMarginals (finiteConditional q y) z)) := by
  exact finite_event_probability_le (finiteConditional q y) (productMarginals (finiteConditional q y))
    (finiteConditional_nonneg q hq y)
    (productMarginals_nonneg _ (finiteConditional_nonneg q hq y))
    (finiteConditional_sum q y hy.ne') (productMarginals_sum _ (finiteConditional_sum q y hy.ne'))
    (productMarginals_support _ (finiteConditional_nonneg q hq y)) E hu

theorem conditional_product_event_probability_zero {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (q : α → (ι → Bool) → ℝ) (hq : ∀ y z, 0 ≤ q y z) (y : α)
    (E : Finset (ι → Bool)) (hu : ∑ z ∈ E, productMarginals (finiteConditional q y) z=0) :
    ∑ z ∈ E, finiteConditional q y z=0 :=
  finite_event_probability_zero _ _ (productMarginals_nonneg _ (finiteConditional_nonneg q hq y))
    (productMarginals_support _ (finiteConditional_nonneg q hq y)) E hu

end SparseLowerTail.Section03

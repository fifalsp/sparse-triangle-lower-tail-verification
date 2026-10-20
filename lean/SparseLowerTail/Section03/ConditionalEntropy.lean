import SparseLowerTail.Section03.EntropyTransfer

/-! The conditional relative-entropy chain rule used in `lem:entropy`(a). -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- Marginal probability of the first coordinate of a finite joint law. -/
def finiteRowMass {α β : Type*} [Fintype β] (q : α → β → ℝ) (y : α) : ℝ :=
  ∑ z, q y z

/-- Conditional law at y; the zero-mass row has value zero. -/
def finiteConditional {α β : Type*} [Fintype β] (q : α → β → ℝ) (y : α) (z : β) : ℝ :=
  q y z / finiteRowMass q y

theorem finiteRowMass_nonneg {α β : Type*} [Fintype β] (q : α → β → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (y : α) : 0 ≤ finiteRowMass q y :=
  Finset.sum_nonneg (fun z _ => hq y z)

theorem finiteRowMass_zero {α β : Type*} [Fintype β] (q : α → β → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (y : α) (hy : finiteRowMass q y=0) (z : β) : q y z=0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hq y z)).mp hy z (Finset.mem_univ z)

theorem finiteConditional_nonneg {α β : Type*} [Fintype β] (q : α → β → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (y : α) (z : β) : 0 ≤ finiteConditional q y z :=
  div_nonneg (hq y z) (finiteRowMass_nonneg q hq y)

theorem finiteConditional_sum {α β : Type*} [Fintype β] (q : α → β → ℝ)
    (y : α) (hy : finiteRowMass q y ≠ 0) : ∑ z, finiteConditional q y z=1 := by
  simp only [finiteConditional, ← Finset.sum_div]
  exact div_self hy

theorem finiteConditional_factor {α β : Type*} [Fintype β] (q : α → β → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (y : α) (z : β) :
    finiteRowMass q y * finiteConditional q y z=q y z := by
  by_cases hy : finiteRowMass q y=0
  · rw [hy, zero_mul, finiteRowMass_zero q hq y hy z]
  · unfold finiteConditional
    field_simp

private theorem joint_log_ratio_split {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    a*Real.log (a/(c*d)) = a*Real.log (b/c)+b*((a/b)*Real.log ((a/b)/d)) := by
  rw [Real.log_div ha (mul_ne_zero hc hd), Real.log_mul hc hd,
    Real.log_div hb hc, Real.log_div (div_ne_zero ha hb) hd, Real.log_div ha hb]
  field_simp
  ring

private theorem row_entropy_chain {α β : Type*} [Fintype β] (q : α → β → ℝ)
    (hq : ∀ y z, 0 ≤ q y z) (py : α → ℝ) (pz : β → ℝ)
    (hpy : ∀ y, 0 < py y) (hpz : ∀ z, 0 < pz z) (y : α) :
    (∑ z, q y z*Real.log (q y z/(py y*pz z))) =
      finiteRowMass q y*Real.log (finiteRowMass q y/py y) +
        finiteRowMass q y*finiteRelativeEntropy (finiteConditional q y) pz := by
  by_cases hy : finiteRowMass q y=0
  · have hzero := finiteRowMass_zero q hq y hy
    simp [hzero, hy]
  · have he : ∀ z, q y z*Real.log (q y z/(py y*pz z)) =
        q y z*Real.log (finiteRowMass q y/py y) +
          finiteRowMass q y*(finiteConditional q y z*Real.log (finiteConditional q y z/pz z)) := by
      intro z
      by_cases hz : q y z=0
      · simp [hz, finiteConditional]
      · exact joint_log_ratio_split hz hy (hpy y).ne' (hpz z).ne'
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rfl

/-- Relative-entropy chain rule for an actual finite conditional law and a product reference law. -/
theorem finite_conditional_entropy_chain {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β → ℝ) (hq : ∀ y z, 0 ≤ q y z) (py : α → ℝ) (pz : β → ℝ)
    (hpy : ∀ y, 0 < py y) (hpz : ∀ z, 0 < pz z) :
    finiteRelativeEntropy (fun yz : α×β => q yz.1 yz.2) (fun yz => py yz.1*pz yz.2) =
      finiteRelativeEntropy (finiteRowMass q) py +
        ∑ y, finiteRowMass q y*finiteRelativeEntropy (finiteConditional q y) pz := by
  unfold finiteRelativeEntropy
  rw [Fintype.sum_prod_type]
  simp_rw [row_entropy_chain q hq py pz hpy hpz]
  rw [Finset.sum_add_distrib]
  rfl

/-- Gibbs' inequality for normalized finite laws under absolute continuity. -/
theorem finiteRelativeEntropy_nonneg {α : Type*} [Fintype α] (q p : α → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (hqsum : ∑ i, q i=1) (hpsum : ∑ i, p i=1) (hs : ∀ i, p i=0 → q i=0) :
    0 ≤ finiteRelativeEntropy q p := by
  have hh := finite_log_sum Finset.univ q p (fun i _ => hq i) (fun i _ => hp i)
    (fun i _ => hs i) (by rw [hpsum]; norm_num)
  simpa only [hqsum, hpsum, div_self (by norm_num : (1:ℝ) ≠ 0), Real.log_one,
    mul_zero, finiteRelativeEntropy] using hh

/-- Dropping the nonnegative marginal cost bounds expected conditional entropy by total cost. -/
theorem expected_conditional_entropy_le {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β → ℝ) (hq : ∀ y z, 0 ≤ q y z)
    (hqsum : ∑ y, ∑ z, q y z=1) (py : α → ℝ) (pz : β → ℝ)
    (hpy : ∀ y, 0 < py y) (hpz : ∀ z, 0 < pz z) (hpysum : ∑ y, py y=1) :
    (∑ y, finiteRowMass q y*finiteRelativeEntropy (finiteConditional q y) pz) ≤
      finiteRelativeEntropy (fun yz : α×β => q yz.1 yz.2) (fun yz => py yz.1*pz yz.2) := by
  rw [finite_conditional_entropy_chain q hq py pz hpy hpz]
  have hh := finiteRelativeEntropy_nonneg (finiteRowMass q) py
    (finiteRowMass_nonneg q hq) (fun y => (hpy y).le) hqsum hpysum
    (fun y hy => ((hpy y).ne' hy).elim)
  linarith

end SparseLowerTail.Section03

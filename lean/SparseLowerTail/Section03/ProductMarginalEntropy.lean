import SparseLowerTail.Section03.ConditionalEntropy
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Relative entropy against a product law and the product of the actual marginals. -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- Pushforward of a finite mass function along a coordinate map. -/
def finiteMarginal {α β : Type*} [Fintype α] (q : α → ℝ) (f : α → β) (b : β) : ℝ := by
  classical
  exact ∑ z, if f z=b then q z else 0

theorem finiteMarginal_nonneg {α β : Type*} [Fintype α] (q : α → ℝ)
    (hq : ∀ z, 0 ≤ q z) (f : α → β) (b : β) : 0 ≤ finiteMarginal q f b := by
  classical
  unfold finiteMarginal
  exact Finset.sum_nonneg (fun z _ => by split_ifs; exact hq z; exact le_rfl)

/-- Expectations under a marginal agree with expectations of the coordinate. -/
theorem finiteMarginal_expect {α β : Type*} [Fintype α] [Fintype β]
    (q : α → ℝ) (f : α → β) (g : β → ℝ) :
    (∑ b, finiteMarginal q f b*g b) = ∑ z, q z*g (f z) := by
  classical
  simp only [finiteMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [ite_mul, zero_mul]
  simp

theorem finiteMarginal_sum {α β : Type*} [Fintype α] [Fintype β]
    (q : α → ℝ) (f : α → β) : (∑ b, finiteMarginal q f b) = ∑ z, q z := by
  simpa using finiteMarginal_expect q f (fun _ => 1)

theorem mass_le_finiteMarginal {α β : Type*} [Fintype α] (q : α → ℝ)
    (hq : ∀ z, 0 ≤ q z) (f : α → β) (z : α) : q z ≤ finiteMarginal q f (f z) := by
  classical
  unfold finiteMarginal
  have hh := Finset.single_le_sum (s:=Finset.univ) (a:=z)
    (f:=fun a => if f a=f z then q a else 0)
    (fun a _ => by dsimp; split_ifs; exact hq a; exact le_rfl) (Finset.mem_univ z)
  simpa using hh

def finiteProductMass {ι β : Type*} [Fintype ι] [DecidableEq ι] (p : ι → β → ℝ) (z : ι → β) : ℝ :=
  ∏ i, p i (z i)

theorem finiteProductMass_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι] (p : ι → β → ℝ)
    (hp : ∀ i b, 0 ≤ p i b) (z : ι → β) : 0 ≤ finiteProductMass p z :=
  Finset.prod_nonneg (fun i _ => hp i (z i))

theorem finiteProductMass_pos {ι β : Type*} [Fintype ι] [DecidableEq ι] (p : ι → β → ℝ)
    (hp : ∀ i b, 0 < p i b) (z : ι → β) : 0 < finiteProductMass p z :=
  Finset.prod_pos (fun i _ => hp i (z i))

theorem finiteProductMass_sum {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (p : ι → β → ℝ) (hp : ∀ i, ∑ b, p i b=1) : ∑ z, finiteProductMass p z=1 := by
  classical
  unfold finiteProductMass
  rw [← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]

/-- The independent law with the actual one-coordinate marginals. -/
def productMarginals {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] (q : (ι → β) → ℝ) : (ι → β) → ℝ :=
  finiteProductMass (fun i => finiteMarginal q (fun z => z i))

theorem productMarginals_nonneg {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (q : (ι → β) → ℝ) (hq : ∀ z, 0 ≤ q z) (z : ι → β) : 0 ≤ productMarginals q z :=
  finiteProductMass_nonneg _ (fun _i b => finiteMarginal_nonneg q hq _ b) z

theorem productMarginals_sum {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (q : (ι → β) → ℝ) (hqsum : ∑ z, q z=1) : ∑ z, productMarginals q z=1 := by
  apply finiteProductMass_sum
  intro i
  rw [finiteMarginal_sum, hqsum]

/-- Any point with positive joint mass has positive mass under the product of its marginals. -/
theorem productMarginals_support {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (q : (ι → β) → ℝ) (hq : ∀ z, 0 ≤ q z) (z : ι → β) :
    productMarginals q z=0 → q z=0 := by
  contrapose!
  intro hz
  have hqz : 0 < q z := lt_of_le_of_ne (hq z) hz.symm
  apply ne_of_gt
  apply Finset.prod_pos
  intro i _
  exact hqz.trans_le (mass_le_finiteMarginal q hq (fun z => z i) z)

private theorem weighted_log_div {a b : ℝ} (hs : b=0 → a=0) :
    a*Real.log (a/b) = a*Real.log a-a*Real.log b := by
  by_cases ha : a=0
  · simp [ha]
  · have hb : b ≠ 0 := fun hb => ha (hs hb)
    rw [Real.log_div ha hb]
    ring

/-- The cross-entropy of a product reference depends only on the coordinate marginals. -/
theorem finite_product_cross_entropy {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (q : (ι → β) → ℝ) (p : ι → β → ℝ)
    (hs : ∀ z, q z ≠ 0 → ∀ i, p i (z i) ≠ 0) :
    (∑ z, q z*Real.log (finiteProductMass p z)) =
      ∑ i, ∑ b, finiteMarginal q (fun z => z i) b*Real.log (p i b) := by
  classical
  have he : ∀ z, q z*Real.log (finiteProductMass p z) = ∑ i, q z*Real.log (p i (z i)) := by
    intro z
    by_cases hz : q z=0
    · simp [hz]
    · rw [finiteProductMass, Real.log_prod _ _ (fun i _ => hs z hz i), Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (finiteMarginal_expect q (fun z => z i) (fun b => Real.log (p i b))).symm

/-- Decomposition into dependence cost and marginal relative entropies, using the actual marginals. -/
theorem product_marginal_entropy_decomposition {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (q : (ι → β) → ℝ) (hq : ∀ z, 0 ≤ q z) (p : ι → β → ℝ)
    (hp : ∀ i b, 0 < p i b) :
    finiteRelativeEntropy q (finiteProductMass p) =
      finiteRelativeEntropy q (productMarginals q) +
        ∑ i, finiteRelativeEntropy (finiteMarginal q (fun z => z i)) (p i) := by
  classical
  have hcrossp := finite_product_cross_entropy q p (fun z _ i => (hp i (z i)).ne')
  have hcrossq := finite_product_cross_entropy q (fun i => finiteMarginal q (fun z => z i))
    (fun z hz i => (lt_of_le_of_ne (hq z) hz.symm).trans_le
      (mass_le_finiteMarginal q hq (fun z => z i) z) |>.ne')
  have h1 : finiteRelativeEntropy q (finiteProductMass p) =
      (∑ z, q z*Real.log (q z))-(∑ z, q z*Real.log (finiteProductMass p z)) := by
    unfold finiteRelativeEntropy
    simp_rw [weighted_log_div (fun h => ((finiteProductMass_pos p hp _).ne' h).elim)]
    rw [Finset.sum_sub_distrib]
  have h2 : finiteRelativeEntropy q (productMarginals q) =
      (∑ z, q z*Real.log (q z))-(∑ z, q z*Real.log (productMarginals q z)) := by
    unfold finiteRelativeEntropy
    simp_rw [weighted_log_div (productMarginals_support q hq _)]
    rw [Finset.sum_sub_distrib]
  have h3 : (∑ i, finiteRelativeEntropy (finiteMarginal q (fun z => z i)) (p i)) =
      (∑ i, ∑ b, finiteMarginal q (fun z => z i) b*Real.log (finiteMarginal q (fun z => z i) b))-
      (∑ i, ∑ b, finiteMarginal q (fun z => z i) b*Real.log (p i b)) := by
    unfold finiteRelativeEntropy
    simp_rw [weighted_log_div (fun h => ((hp _ _).ne' h).elim), Finset.sum_sub_distrib]
  rw [h1, h2, h3, hcrossp]
  change _ = _-(∑ z, q z*Real.log (finiteProductMass (fun i => finiteMarginal q (fun z => z i)) z))+_
  rw [hcrossq]
  ring

end SparseLowerTail.Section03

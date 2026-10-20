import SparseLowerTail.Section03.RevealedCoordinates
import SparseLowerTail.Section03.KS23RateInputs

/-! The entropy budget for the actual revealed-edge law, transported through an exact equivalence. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual conditional distribution of unrevealed coordinates at a revealed pattern. -/
def unrevealedConditionalLaw (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool) :
    (↑Wᶜ → Bool) → ℝ :=
  finiteConditional (fun y z => q ((splitCoordinates W).symm (y,z))) y

/-- The actual unrevealed conditional law is nonnegative. -/
theorem unrevealedConditionalLaw_nonneg (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z)
    (W : Finset ι) (y : W → Bool) (z : ↑Wᶜ → Bool) :
    0≤unrevealedConditionalLaw q W y z :=
  finiteConditional_nonneg _ (fun _ _ => hq _) y z

/-- Every positive-mass pattern gives a normalized actual unrevealed law. -/
theorem unrevealedConditionalLaw_sum (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool)
    (hy : 0<revealedPatternMass q W y) : ∑ z, unrevealedConditionalLaw q W y z=1 := by
  apply finiteConditional_sum
  rw [splitCoordinates_rowMass]
  exact hy.ne'

/-- A zero-mass revealed pattern gives the zero conditional law. -/
theorem unrevealedConditionalLaw_zero (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool)
    (hy : revealedPatternMass q W y=0) : unrevealedConditionalLaw q W y=(fun _ => 0) := by
  funext z
  unfold unrevealedConditionalLaw finiteConditional
  rw [splitCoordinates_rowMass,hy,div_zero]

/-- Conditional Bernoulli marginals are probabilities, including the zero-row convention. -/
theorem unrevealedConditionalLaw_marginal_mem_unitInterval (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z)
    (W : Finset ι) (y : W → Bool) (i : ↑Wᶜ) :
    finiteMarginal (unrevealedConditionalLaw q W y) (fun z => z i) true∈Icc (0:ℝ) 1 := by
  by_cases hy : revealedPatternMass q W y=0
  · simp [unrevealedConditionalLaw_zero q W y hy,finiteMarginal]
  · have hsum : ∑ z, unrevealedConditionalLaw q W y z=1 := by
      apply finiteConditional_sum
      rw [splitCoordinates_rowMass]
      exact hy
    have hnonneg := unrevealedConditionalLaw_nonneg q hq W y
    have hm := finiteMarginal_sum (unrevealedConditionalLaw q W y) (fun z => z i)
    rw [hsum] at hm
    constructor
    · exact finiteMarginal_nonneg _ hnonneg _ _
    · have hh := Finset.single_le_sum (s:=Finset.univ) (a:=true)
        (f:=finiteMarginal (unrevealedConditionalLaw q W y) (fun z => z i))
        (fun b _ => finiteMarginal_nonneg _ hnonneg _ b) (Finset.mem_univ true)
      rwa [hm] at hh

/-- The dependence entropy of the actual conditional law is nonnegative, also on zero-mass rows. -/
theorem unrevealedConditionalLaw_dependence_nonneg (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z)
    (W : Finset ι) (y : W → Bool) :
    0≤finiteRelativeEntropy (unrevealedConditionalLaw q W y)
      (productMarginals (unrevealedConditionalLaw q W y)) := by
  by_cases hy : revealedPatternMass q W y=0
  · have hz : unrevealedConditionalLaw q W y=(fun _ => 0) := by
      funext z
      unfold unrevealedConditionalLaw finiteConditional
      rw [splitCoordinates_rowMass,hy,div_zero]
    simp [hz,finiteRelativeEntropy]
  · have hsum : ∑ z, unrevealedConditionalLaw q W y z=1 := by
      apply finiteConditional_sum
      rw [splitCoordinates_rowMass]
      exact hy
    have hnonneg := unrevealedConditionalLaw_nonneg q hq W y
    exact finiteRelativeEntropy_nonneg _ _ hnonneg (productMarginals_nonneg _ hnonneg)
      hsum (productMarginals_sum _ hsum) (productMarginals_support _ hnonneg)

/-- Conditional expectations agree in the full edge space and the unrevealed coordinate space. -/
theorem unrevealedConditionalLaw_expect (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool)
    (f : (ι → Bool) → ℝ) :
    (∑ z, finiteConditionedMass q (revealedPatternEvent W y) z*f z) =
      ∑ z : ↑Wᶜ → Bool, unrevealedConditionalLaw q W y z*f ((splitCoordinates W).symm (y,z)) := by
  classical
  have hpoint : ∀ yz : (W → Bool) × (↑Wᶜ → Bool),
      finiteConditionedMass q (revealedPatternEvent W y) ((splitCoordinates W).symm yz)*
        f ((splitCoordinates W).symm yz) =
      if yz.1=y then (q ((splitCoordinates W).symm yz)/revealedPatternMass q W y)*
        f ((splitCoordinates W).symm yz) else 0 := by
    intro yz
    by_cases hy : yz.1=y <;>
      simp [finiteConditionedMass,mem_revealedPatternEvent_symm,hy,revealedPatternMass,finiteEventMass]
  have he := (splitCoordinates W).symm.sum_comp
    (fun z => finiteConditionedMass q (revealedPatternEvent W y) z*f z)
  rw [Fintype.sum_prod_type] at he
  simp_rw [hpoint] at he
  have hinner : ∀ x : W → Bool,
      (∑ z : ↑Wᶜ → Bool, if x=y then (q ((splitCoordinates W).symm (x,z))/revealedPatternMass q W y)*
        f ((splitCoordinates W).symm (x,z)) else 0) =
      if x=y then (∑ z : ↑Wᶜ → Bool, (q ((splitCoordinates W).symm (x,z))/revealedPatternMass q W y)*
        f ((splitCoordinates W).symm (x,z))) else 0 := by
    intro x
    by_cases hx : x=y <;> simp [hx]
  simp_rw [hinner] at he
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
  rw [← he]
  unfold unrevealedConditionalLaw finiteConditional
  rw [splitCoordinates_rowMass]

/-- The entropy budget's unrevealed marginal is the same conditional edge moment used in KS23. -/
theorem unrevealedConditionalLaw_marginal_true (q : (ι → Bool) → ℝ) (W : Finset ι)
    (y : W → Bool) (i : ↑Wᶜ) :
    finiteMarginal (unrevealedConditionalLaw q W y) (fun z => z i) true =
      revealedConditionalMoment q W y {i.val} := by
  classical
  have he := unrevealedConditionalLaw_expect q W y (fun z => ((z i).toNat:ℝ))
  simp_rw [splitCoordinates_symm_snd] at he
  have hleft : (∑ z, finiteConditionedMass q (revealedPatternEvent W y) z*((z i).toNat:ℝ)) =
      revealedConditionalMoment q W y {i.val} := by
    have hbool : ∀ z : ι → Bool, ((z i).toNat:ℝ)=if z∈allTrueEvent {i.val} then 1 else 0 :=
      fun z => by simpa only [Finset.prod_singleton] using booleanProduct_eq_allTrue (A:={i.val}) z
    simp_rw [hbool,mul_ite,mul_one,mul_zero]
    simp only [Finset.sum_ite_mem,Finset.univ_inter,revealedConditionalMoment,finiteEventMass]
  rw [hleft] at he
  rw [he]
  unfold finiteMarginal
  apply Finset.sum_congr rfl
  intro z _
  cases hz : z i <;> simp [hz]

/-- The entropy lemma applied to an arbitrary positive-probability event in the original edge space. -/
theorem revealed_bernoulli_entropy_bound (W : Finset ι) {p : ℝ} (hp : p∈Ioo (0:ℝ) 1)
    (E : Finset (ι → Bool)) (hE : 0<finiteEventMass (productBernoulliMass (fun _ : ι => p)) E) :
    let q := finiteConditionedMass (productBernoulliMass (fun _ : ι => p)) E
    (∑ y : W → Bool, revealedPatternMass q W y*
      finiteRelativeEntropy (unrevealedConditionalLaw q W y)
        (productMarginals (unrevealedConditionalLaw q W y))) +
    (∑ y : W → Bool, revealedPatternMass q W y*∑ i : ↑Wᶜ,
      bernoulliEntropy p (finiteMarginal (unrevealedConditionalLaw q W y) (fun z => z i) true)) ≤
      -Real.log (finiteEventMass (productBernoulliMass (fun _ : ι => p)) E) := by
  let py := productBernoulliMass (fun _ : W => p)
  have hpy : ∀ y, 0<py y := fun y => finiteProductMass_pos _ (fun _ b => bernoulliMass_pos hp b) y
  have hpysum : ∑ y, py y=1 := productBernoulliMass_sum _
  have hEsplit : 0<finiteEventMass (fun yz : (W → Bool) × (↑Wᶜ → Bool) =>
      py yz.1*productBernoulliMass (fun _ : ↑Wᶜ => p) yz.2) (splitCoordinateEvent W E) := by
    change 0<finiteEventMass (fun yz => productBernoulliMass (fun _ : W => p) yz.1*
      productBernoulliMass (fun _ : ↑Wᶜ => p) yz.2) (splitCoordinateEvent W E)
    rw [splitCoordinates_productEventMass W (fun _ => p) E]
    exact hE
  have hh := conditioned_bernoulli_entropy_bound py hpy hpysum hp (splitCoordinateEvent W E) hEsplit
  have he : conditionedBernoulliJoint py p (splitCoordinateEvent W E) =
      (fun y z => finiteConditionedMass (productBernoulliMass (fun _ : ι => p)) E
        ((splitCoordinates W).symm (y,z))) := by
    funext y z
    exact splitCoordinates_conditionedProductJoint W (fun _ => p) E (y,z)
  dsimp only at hh
  rw [he] at hh
  simp_rw [splitCoordinates_rowMass] at hh
  change _≤-Real.log (finiteEventMass (fun yz : (W → Bool) × (↑Wᶜ → Bool) =>
    productBernoulliMass (fun _ : W => p) yz.1*productBernoulliMass (fun _ : ↑Wᶜ => p) yz.2)
      (splitCoordinateEvent W E)) at hh
  rw [splitCoordinates_productEventMass W (fun _ => p) E] at hh
  exact hh

/-- The entropy budget for the genuine hypergraph lower-tail law and every revealed set. -/
theorem hypergraph_revealed_entropy_budget (H : Finset (Finset ι)) (r : ℕ)
    (hr : 1≤r) (hH : ∀ A∈H, A.card=r) {p η : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) (W : Finset ι) :
    let q := hypergraphLowerLaw H r p η
    (∑ y : W → Bool, revealedPatternMass q W y*
      finiteRelativeEntropy (unrevealedConditionalLaw q W y)
        (productMarginals (unrevealedConditionalLaw q W y))) +
    (∑ y : W → Bool, revealedPatternMass q W y*∑ i : ↑Wᶜ,
      bernoulliEntropy p (finiteMarginal (unrevealedConditionalLaw q W y) (fun z => z i) true)) ≤
      hypergraphLowerTailRate H r p η :=
  revealed_bernoulli_entropy_bound W hp (hypergraphLowerEvent H r p η)
    (hypergraphLowerEvent_probability_pos H r hr hH hp hη)

end SparseLowerTail.Section03

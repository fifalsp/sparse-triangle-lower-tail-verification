import SparseLowerTail.Section03.KS23Inputs

/-! Exact splitting of a Bernoulli edge configuration into revealed and unrevealed coordinates. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction to W and its complement, with the genuine inverse configuration map. -/
def splitCoordinates (W : Finset ι) : (ι → Bool) ≃ (W → Bool) × (↑Wᶜ → Bool) where
  toFun z := (fun i => z i,fun i => z i)
  invFun yz i := if hi : i∈W then yz.1 ⟨i,hi⟩ else yz.2 ⟨i,Finset.mem_compl.mpr hi⟩
  left_inv z := by funext i; dsimp; split <;> rfl
  right_inv yz := by
    apply Prod.ext <;> funext i
    · simp [i.property]
    · simp [Finset.mem_compl.mp i.property]

/-- Merging the coordinates recovers every unrevealed value. -/
theorem splitCoordinates_symm_snd (W : Finset ι) (yz : (W → Bool) × (↑Wᶜ → Bool)) (i : ↑Wᶜ) :
    (splitCoordinates W).symm yz i=yz.2 i := by
  simp [splitCoordinates,Finset.mem_compl.mp i.property]

/-- An arbitrary event expressed in split coordinates. -/
def splitCoordinateEvent (W : Finset ι) (E : Finset (ι → Bool)) :
    Finset ((W → Bool) × (↑Wᶜ → Bool)) :=
  Finset.univ.filter (fun yz => (splitCoordinates W).symm yz∈E)

/-- The product reference factors exactly across the revealed set and its complement. -/
theorem splitCoordinates_productMass (W : Finset ι) (p : ι → ℝ) (z : ι → Bool) :
    productBernoulliMass p z =
      productBernoulliMass (fun i : W => p i) ((splitCoordinates W z).1)*
      productBernoulliMass (fun i : ↑Wᶜ => p i) ((splitCoordinates W z).2) := by
  unfold productBernoulliMass finiteProductMass
  change (∏ i, bernoulliMass (p i) (z i))=
    (∏ i : W, bernoulliMass (p i) (z i))*(∏ i : ↑Wᶜ, bernoulliMass (p i) (z i))
  rw [← Finset.prod_subtype W (fun _ => Iff.rfl) (fun i => bernoulliMass (p i) (z i)),
    ← Finset.prod_subtype Wᶜ (fun _ => Iff.rfl) (fun i => bernoulliMass (p i) (z i))]
  exact (Finset.prod_mul_prod_compl W _).symm

/-- Finite event mass is preserved when both event and law are transported by the split equivalence. -/
theorem splitCoordinateEvent_mass (W : Finset ι) (q : (ι → Bool) → ℝ) (E : Finset (ι → Bool)) :
    finiteEventMass (fun yz => q ((splitCoordinates W).symm yz)) (splitCoordinateEvent W E)=
      finiteEventMass q E := by
  unfold finiteEventMass splitCoordinateEvent
  rw [Finset.sum_filter]
  have he := (splitCoordinates W).symm.sum_comp (fun z => if z∈E then q z else 0)
  simpa only [Finset.sum_ite_mem,Finset.univ_inter] using he

/-- The event probability is unchanged under the factored Bernoulli reference. -/
theorem splitCoordinates_productEventMass (W : Finset ι) (p : ι → ℝ) (E : Finset (ι → Bool)) :
    finiteEventMass (fun yz : (W → Bool) × (↑Wᶜ → Bool) =>
      productBernoulliMass (fun i : W => p i) yz.1*
      productBernoulliMass (fun i : ↑Wᶜ => p i) yz.2) (splitCoordinateEvent W E) =
      finiteEventMass (productBernoulliMass p) E := by
  have he : (fun yz : (W → Bool) × (↑Wᶜ → Bool) =>
      productBernoulliMass (fun i : W => p i) yz.1*
      productBernoulliMass (fun i : ↑Wᶜ => p i) yz.2) =
      (fun yz => productBernoulliMass p ((splitCoordinates W).symm yz)) := by
    funext yz
    simpa only [Equiv.apply_symm_apply] using
      (splitCoordinates_productMass W p ((splitCoordinates W).symm yz)).symm
  rw [he]
  exact splitCoordinateEvent_mass W _ E

/-- Conditioning commutes with this actual coordinate change. -/
theorem splitCoordinates_conditionedMass (W : Finset ι) (q : (ι → Bool) → ℝ)
    (E : Finset (ι → Bool)) (yz : (W → Bool) × (↑Wᶜ → Bool)) :
    finiteConditionedMass (fun yz => q ((splitCoordinates W).symm yz))
      (splitCoordinateEvent W E) yz = finiteConditionedMass q E ((splitCoordinates W).symm yz) := by
  unfold finiteConditionedMass
  have hm := splitCoordinateEvent_mass W q E
  unfold finiteEventMass at hm
  rw [hm]
  simp only [splitCoordinateEvent,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hz : (splitCoordinates W).symm yz∈E <;> simp [hz]

/-- The split product law conditioned on E is exactly the original conditioned law. -/
theorem splitCoordinates_conditionedProductJoint (W : Finset ι) (p : ι → ℝ)
    (E : Finset (ι → Bool)) (yz : (W → Bool) × (↑Wᶜ → Bool)) :
    conditionedProductJoint (productBernoulliMass (fun i : W => p i))
      (productBernoulliMass (fun i : ↑Wᶜ => p i)) (splitCoordinateEvent W E) yz.1 yz.2 =
      finiteConditionedMass (productBernoulliMass p) E ((splitCoordinates W).symm yz) := by
  have he : (fun yz : (W → Bool) × (↑Wᶜ → Bool) =>
      productBernoulliMass (fun i : W => p i) yz.1*
      productBernoulliMass (fun i : ↑Wᶜ => p i) yz.2) =
      (fun yz => productBernoulliMass p ((splitCoordinates W).symm yz)) := by
    funext yz
    simpa only [Equiv.apply_symm_apply] using
      (splitCoordinates_productMass W p ((splitCoordinates W).symm yz)).symm
  unfold conditionedProductJoint
  rw [he]
  exact splitCoordinates_conditionedMass W _ E yz

/-- The marginal of the revealed coordinates is exactly the row mass of the split law. -/
theorem splitCoordinates_rowMass (W : Finset ι) (q : (ι → Bool) → ℝ) (y : W → Bool) :
    finiteRowMass (fun y z => q ((splitCoordinates W).symm (y,z))) y =
      revealedPatternMass q W y := by
  classical
  rw [revealedPatternMass_eq_marginal]
  unfold finiteMarginal finiteRowMass
  have he := (splitCoordinates W).sum_comp
    (fun yz => if yz.1=y then q ((splitCoordinates W).symm yz) else 0)
  have hfst : ∀ z : ι → Bool, (splitCoordinates W z).1=(fun i : W => z i) := fun _ => rfl
  simp only [hfst,Equiv.symm_apply_apply] at he
  rw [Fintype.sum_prod_type] at he
  have hinner : ∀ x : W → Bool,
      (∑ z : ↑Wᶜ → Bool, if x=y then q ((splitCoordinates W).symm (x,z)) else 0) =
      if x=y then (∑ z : ↑Wᶜ → Bool, q ((splitCoordinates W).symm (x,z))) else 0 := by
    intro x
    by_cases hx : x=y <;> simp [hx]
  simp_rw [hinner] at he
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
  convert he.symm using 1
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (fun i : W => z i)=y <;> simp [hz]

/-- The concrete split conditional product law has the actual revealed-pattern marginal. -/
theorem splitCoordinates_conditioned_rowMass (W : Finset ι) (p : ι → ℝ)
    (E : Finset (ι → Bool)) (y : W → Bool) :
    finiteRowMass (conditionedProductJoint (productBernoulliMass (fun i : W => p i))
      (productBernoulliMass (fun i : ↑Wᶜ => p i)) (splitCoordinateEvent W E)) y =
      revealedPatternMass (finiteConditionedMass (productBernoulliMass p) E) W y := by
  have he : conditionedProductJoint (productBernoulliMass (fun i : W => p i))
      (productBernoulliMass (fun i : ↑Wᶜ => p i)) (splitCoordinateEvent W E) =
      (fun y z => finiteConditionedMass (productBernoulliMass p) E ((splitCoordinates W).symm (y,z))) := by
    funext y z
    exact splitCoordinates_conditionedProductJoint W p E (y,z)
  rw [he]
  exact splitCoordinates_rowMass W _ y

/-- In split coordinates the revealed-pattern event fixes precisely the first coordinate. -/
theorem mem_revealedPatternEvent_symm (W : Finset ι) (y : W → Bool)
    (yz : (W → Bool) × (↑Wᶜ → Bool)) :
    (splitCoordinates W).symm yz∈revealedPatternEvent W y ↔ yz.1=y := by
  simp only [revealedPatternEvent,Finset.mem_filter,Finset.mem_univ,true_and]
  have hh : (fun i : W => (splitCoordinates W).symm yz i)=yz.1 :=
    congrArg Prod.fst ((splitCoordinates W).apply_symm_apply yz)
  rw [← funext_iff,hh]

/-- Merging a fixed revealed pattern is monotone in the unrevealed coordinates. -/
theorem splitCoordinates_symm_monotone (W : Finset ι) (y : W → Bool) :
    Monotone (fun z : ↑Wᶜ → Bool => (splitCoordinates W).symm (y,z)) := by
  intro z z' hzz i
  by_cases hi : i∈W
  · simp [splitCoordinates,hi]
  · simpa [splitCoordinates,hi] using hzz ⟨i,Finset.mem_compl.mpr hi⟩

/-- A decreasing event remains decreasing in every actual revealed-coordinate section. -/
theorem splitCoordinateEvent_section_isLowerSet (W : Finset ι) (E : Finset (ι → Bool))
    (hE : IsLowerSet (E : Set (ι → Bool))) (y : W → Bool) :
    IsLowerSet (finiteEventSection (splitCoordinateEvent W E) y : Set (↑Wᶜ → Bool)) := by
  intro a b hba ha
  change a∈finiteEventSection (splitCoordinateEvent W E) y at ha
  change b∈finiteEventSection (splitCoordinateEvent W E) y
  simp only [mem_finiteEventSection,splitCoordinateEvent,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  exact hE (splitCoordinates_symm_monotone W y hba) ha

end SparseLowerTail.Section03

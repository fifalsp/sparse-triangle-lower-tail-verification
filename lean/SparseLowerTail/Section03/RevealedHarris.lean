import SparseLowerTail.Section03.RevealedEntropyBudget
import SparseLowerTail.Section03.RevealedTriangleConstraint

/-! Harris domination for the actual unrevealed-coordinate marginals of a lower-tail graph law. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The real-valued count is precisely the natural hyperedge count, embedded in the reals. -/
theorem hypergraphRealCount_eq_natCast (H : Finset (Finset ι)) (z : ι → Bool) :
    hypergraphRealCount H z=(finiteHypergraphCount H z:ℝ) := by
  simp [hypergraphRealCount,finiteHypergraphCount]

omit [Fintype ι] [DecidableEq ι] in
theorem hypergraphRealCount_monotone (H : Finset (Finset ι)) : Monotone (hypergraphRealCount H) := by
  intro x y hxy
  rw [hypergraphRealCount_eq_natCast,hypergraphRealCount_eq_natCast]
  exact_mod_cast finiteHypergraphCount_monotone H hxy

/-- The actual event with a real-valued threshold is decreasing. -/
theorem hypergraphLowerEvent_isLowerSet (H : Finset (Finset ι)) (r : ℕ) (p η : ℝ) :
    IsLowerSet (hypergraphLowerEvent H r p η : Set (ι → Bool)) := by
  intro x y hyx hx
  change x∈hypergraphLowerEvent H r p η at hx
  change y∈hypergraphLowerEvent H r p η
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (hypergraphRealCount_monotone H hyx).trans (Finset.mem_filter.mp hx).2⟩

/-- The actual unrevealed conditional marginal lies in [0,p] at every positive-mass revealed pattern. -/
theorem hypergraph_unrevealed_marginal_bounds (H : Finset (Finset ι)) (r : ℕ)
    (hr : 1≤r) (hH : ∀ A∈H, A.card=r) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η)
    (W : Finset ι) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ)) (y : W → Bool)
    (hy : 0<revealedPatternMass (hypergraphLowerLaw H r p η) W y) (i : ↑Wᶜ) :
    finiteMarginal (unrevealedConditionalLaw (hypergraphLowerLaw H r p η) W y)
      (fun z => z i) true∈Icc (0:ℝ) p := by
  let E := hypergraphLowerEvent H r p η
  let py := productBernoulliMass (fun _ : W => p)
  let J := conditionedProductJoint py (productBernoulliMass (fun _ : ↑Wᶜ => p)) (splitCoordinateEvent W E)
  have hE := hypergraphLowerEvent_probability_pos H r hr hH hp hη
  have hEsplit : 0<finiteEventMass (fun yz : (W → Bool) × (↑Wᶜ → Bool) =>
      py yz.1*productBernoulliMass (fun _ : ↑Wᶜ => p) yz.2) (splitCoordinateEvent W E) := by
    rw [splitCoordinates_productEventMass W (fun _ => p) E]
    exact hE
  have hJ : J=(fun y z => hypergraphLowerLaw H r p η ((splitCoordinates W).symm (y,z))) := by
    funext y z
    exact splitCoordinates_conditionedProductJoint W (fun _ => p) E (y,z)
  have hJrow : 0<finiteRowMass J y := by
    rw [hJ,splitCoordinates_rowMass]
    exact hy
  have hupper := harris_revealed_allTrue_le_pow hHarris ⟨hp.1.le,hp.2.le⟩ py
    (splitCoordinateEvent W E) y {i}
    (finiteProductMass_pos _ (fun _ b => bernoulliMass_pos hp b) y)
    (splitCoordinateEvent_section_isLowerSet W E (hypergraphLowerEvent_isLowerSet H r p η) y)
    hEsplit hJrow
  change finiteEventMass (finiteConditional J y) (allTrueEvent {i})≤p^({i}:Finset ↑Wᶜ).card at hupper
  rw [hJ] at hupper
  have hsingle : ∀ z : ↑Wᶜ → Bool, z∈allTrueEvent {i} ↔ z i=true := by
    intro z
    have hh := booleanProduct_eq_allTrue (A:={i}) z
    simp only [Finset.prod_singleton] at hh
    cases hz : z i <;> by_cases hm : z∈allTrueEvent {i} <;> simp_all
  have hm : finiteEventMass (unrevealedConditionalLaw (hypergraphLowerLaw H r p η) W y) (allTrueEvent {i}) =
      finiteMarginal (unrevealedConditionalLaw (hypergraphLowerLaw H r p η) W y) (fun z => z i) true := by
    classical
    unfold finiteEventMass finiteMarginal
    calc
      _ = ∑ z, if z∈allTrueEvent {i} then unrevealedConditionalLaw (hypergraphLowerLaw H r p η) W y z else 0 := by
        simp only [Finset.sum_ite_mem,Finset.univ_inter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z i=true <;> simp [hz,hsingle z]
  change finiteEventMass (unrevealedConditionalLaw (hypergraphLowerLaw H r p η) W y) (allTrueEvent {i})≤_ at hupper
  rw [hm] at hupper
  constructor
  · exact finiteMarginal_nonneg _
      (finiteConditional_nonneg _ (fun y z => hypergraphLowerLaw_nonneg H r ⟨hp.1.le,hp.2.le⟩ η _) y) _ _
  · simpa only [Finset.card_singleton,pow_one] using hupper

/-- Erasing revealed edges gives genuine probabilities in [0,p] on the entire original edge set. -/
theorem erasedConditionalMeans_bounds (H : Finset (Finset ι)) (r : ℕ)
    (hr : 1≤r) (hH : ∀ A∈H, A.card=r) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η)
    (W : Finset ι) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ)) (y : W → Bool)
    (hy : 0<revealedPatternMass (hypergraphLowerLaw H r p η) W y) (i : ι) :
    erasedConditionalMeans (hypergraphLowerLaw H r p η) W y i∈Icc (0:ℝ) p := by
  classical
  by_cases hi : i∈W
  · simp [erasedConditionalMeans,hi,hp.1.le]
  · rw [erasedConditionalMeans,if_neg hi]
    have hb := hypergraph_unrevealed_marginal_bounds H r hr hH hp hη W hHarris y hy ⟨i,Finset.mem_compl.mpr hi⟩
    rw [unrevealedConditionalLaw_marginal_true] at hb
    exact hb

/-- Harris domination with the zero-row convention included, hence valid for every pattern. -/
theorem hypergraph_unrevealed_marginal_bounds_all (H : Finset (Finset ι)) (r : ℕ)
    (hr : 1≤r) (hH : ∀ A∈H, A.card=r) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η)
    (W : Finset ι) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ)) (y : W → Bool) (i : ↑Wᶜ) :
    finiteMarginal (unrevealedConditionalLaw (hypergraphLowerLaw H r p η) W y)
      (fun z => z i) true∈Icc (0:ℝ) p := by
  by_cases hy : revealedPatternMass (hypergraphLowerLaw H r p η) W y=0
  · simp [unrevealedConditionalLaw_zero _ W y hy,finiteMarginal,hp.1.le]
  · have hypos : 0<revealedPatternMass (hypergraphLowerLaw H r p η) W y :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun z _ => hypergraphLowerLaw_nonneg H r ⟨hp.1.le,hp.2.le⟩ η z)) (Ne.symm hy)
    exact hypergraph_unrevealed_marginal_bounds H r hr hH hp hη W hHarris y hypos i

/-- Every erased conditional mean belongs to [0,p], without exceptional zero-mass patterns. -/
theorem erasedConditionalMeans_bounds_all (H : Finset (Finset ι)) (r : ℕ)
    (hr : 1≤r) (hH : ∀ A∈H, A.card=r) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η)
    (W : Finset ι) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ)) (y : W → Bool) (i : ι) :
    erasedConditionalMeans (hypergraphLowerLaw H r p η) W y i∈Icc (0:ℝ) p := by
  classical
  by_cases hi : i∈W
  · simp [erasedConditionalMeans,hi,hp.1.le]
  · rw [erasedConditionalMeans,if_neg hi]
    have hb := hypergraph_unrevealed_marginal_bounds_all H r hr hH hp hη W hHarris y ⟨i,Finset.mem_compl.mpr hi⟩
    rw [unrevealedConditionalLaw_marginal_true] at hb
    exact hb

end SparseLowerTail.Section03

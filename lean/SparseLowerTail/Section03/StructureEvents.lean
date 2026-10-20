import SparseLowerTail.Section03.StructureMatrices

/-! Actual conditioned event probabilities for the finite matrix conclusions. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02

def constantStructureEvent (n : ℕ) (p r ε : ℝ) : Finset (GraphEdgeCoordinate n → Bool) := by
  classical
  exact Finset.univ.filter (ConstantMatrixClose n p r ε)

def bipodStructureEvent (n : ℕ) (p a b ε : ℝ) : Finset (GraphEdgeCoordinate n → Bool) := by
  classical
  exact Finset.univ.filter (BipodMatrixClose n p a b ε)

def phaseStructureEvent (n : ℕ) (p r a b ε : ℝ) : Finset (GraphEdgeCoordinate n → Bool) :=
  constantStructureEvent n p r ε∪bipodStructureEvent n p a b ε

def triangleConditionalEventMass (n : ℕ) (p r : ℝ) (E : Finset (GraphEdgeCoordinate n → Bool)) : ℝ :=
  finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p (r^3)) E

/-- Any actual event containing a fixed minimizer-neighborhood has conditional probability tending to one. -/
theorem triangle_conditional_event_tendsto
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    (hHarris : ∀ (ν : Type) [Fintype ν] [DecidableEq ν], ClassicalHarrisPositiveAssociation ν)
    {η δ : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hδ : 0<δ)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop)
    (E : (j : ℕ) → Finset (GraphEdgeCoordinate (n j) → Bool))
    (hE : ∀ j (hnj : 0<n j) z, TriangleClose (n j) hnj (p j) (η^(1/3:ℝ)) δ z → z∈E j) :
    Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ)) (E j)) atTop (𝓝 1) := by
  classical
  let r := η^(1/3:ℝ)
  have hr : 0≤r^3 := pow_nonneg (Real.rpow_pos_of_pos hη.1 _).le 3
  have hclose := triangle_conditioned_structure_success_tendsto hdyadic hcompact hpull hcount hlower hupper
    hSelection hCS hHarris hη hδ n p hn hp hpzero hsparse
  have huppermass : ∀ j, triangleConditionalEventMass (n j) (p j) r (E j)≤1 := by
    intro j
    have hh := Finset.sum_le_univ_sum_of_nonneg (s:=E j)
      (fun z => hypergraphLowerLaw_nonneg (coordinateTriangleHypergraph (n j)) 3 ⟨(hp j).1.le,(hp j).2.le⟩ (r^3) z)
    exact hh.trans_eq (hypergraphLowerLaw_sum _ 3 (by norm_num)
      (fun _ hA => coordinateTriangleHypergraph_uniform hA) (hp j) hr)
  have hlower : ∀ᶠ j in atTop, triangleConditionalCloseMass (n j) (p j) r δ≤
      triangleConditionalEventMass (n j) (p j) r (E j) := by
    filter_upwards [hn.eventually_ge_atTop 1] with j hj
    have hjpos : 0<n j := by omega
    rw [triangleConditionalCloseMass,dif_pos hjpos]
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (fun z hz => hE j hjpos z (by simpa only [triangleCloseEvent,Finset.mem_filter,Finset.mem_univ,true_and] using hz))
      (fun z _ _ => hypergraphLowerLaw_nonneg _ 3 ⟨(hp j).1.le,(hp j).2.le⟩ (r^3) z)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hclose tendsto_const_nhds hlower (Eventually.of_forall huppermass)

/-- The two scalar tolerances required by rounding can always be met simultaneously. -/
theorem exists_structure_tolerance {a b ε : ℝ} (hab : a<b) (hε : 0<ε) :
    ∃ δ>0, δ≤ε ∧ 33*δ≤ε ∧ 16*δ/(b-a)≤ε := by
  let δ := min (ε/66) (ε*(b-a)/32)
  have hgap := sub_pos.mpr hab
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,hδ,?_,?_,?_⟩
  · linarith [min_le_left (ε/66) (ε*(b-a)/32)]
  · linarith [min_le_left (ε/66) (ε*(b-a)/32)]
  · apply (div_le_iff₀ hgap).mpr
    linarith [min_le_right (ε/66) (ε*(b-a)/32)]

end SparseLowerTail.Section03

import SparseLowerTail.Section03.DiscreteComparison

/-! Exact identification of the finite triangle variational problem with generic hypergraph coordinates. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hypergraphWeightedCount (H : Finset (Finset ι)) (q : ι → ℝ) : ℝ :=
  ∑ A∈H, ∏ i∈A, q i

def HypergraphFeasible (H : Finset (Finset ι)) (r : ℕ) (p η : ℝ) (q : ι → ℝ) : Prop :=
  (∀ i, q i∈Icc (0:ℝ) 1) ∧ hypergraphWeightedCount H q≤η*p^r*H.card

def hypergraphPhi (H : Finset (Finset ι)) (r : ℕ) (p η : ℝ) : ℝ :=
  sInf {v | ∃ q : ι → ℝ, HypergraphFeasible H r p η q ∧ (∑ i, bernoulliEntropy p (q i))=v}

def extendGraphEdges {n : ℕ} (q : GraphEdgeCoordinate n → ℝ) (e : Finset (Fin n)) : ℝ :=
  if he : e∈completeGraphEdges n then q ⟨e,he⟩ else 0

theorem extendGraphEdges_coe {n : ℕ} (q : GraphEdgeCoordinate n → ℝ) (e : GraphEdgeCoordinate n) :
    extendGraphEdges q e.val=q e := by simp [extendGraphEdges,e.property]

theorem finiteEdgeEntropy_eq_coordinate_sum (n : ℕ) (p : ℝ) (q : Finset (Fin n) → ℝ) :
    finiteEdgeEntropy n p q=∑ e : GraphEdgeCoordinate n, bernoulliEntropy p (q e.val) :=
  Finset.sum_subtype (completeGraphEdges n) (fun _ => Iff.rfl) _

theorem coordinateTriangleEdges_injective_on_triangles (n : ℕ) :
    Set.InjOn (@coordinateTriangleEdges n) (↑(completeGraphTriangles n)) := by
  intro A hA B hB h
  apply triangleEdgeSet_injective_on_triangles n hA hB
  have hh := congrArg projectGraphEdgeSet h
  simpa only [project_coordinateTriangleEdges] using hh

theorem coordinateTriangleEdges_product {n : ℕ} (q : GraphEdgeCoordinate n → ℝ)
    (T : Finset (Fin n)) :
    (∏ e∈coordinateTriangleEdges T, q e)=∏ e∈triangleEdgeSet T, extendGraphEdges q e := by
  rw [← project_coordinateTriangleEdges T]
  unfold projectGraphEdgeSet
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e _
  exact (extendGraphEdges_coe q e).symm

/-- Both counts refer to the actual unordered graph edges and triangles. -/
theorem coordinateTriangle_weightedCount (n : ℕ) (q : GraphEdgeCoordinate n → ℝ) :
    hypergraphWeightedCount (coordinateTriangleHypergraph n) q=weightedTriangleCount (extendGraphEdges q) := by
  unfold hypergraphWeightedCount coordinateTriangleHypergraph weightedTriangleCount
  rw [Finset.sum_image (fun A hA B hB h => coordinateTriangleEdges_injective_on_triangles n hA hB h)]
  apply Finset.sum_congr rfl
  intro T _
  exact coordinateTriangleEdges_product q T

theorem weightedTriangleCount_congr {n : ℕ} (q q' : Finset (Fin n) → ℝ)
    (he : ∀ e∈completeGraphEdges n, q e=q' e) :
    weightedTriangleCount q=weightedTriangleCount q' := by
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.prod_congr rfl
  intro e he'
  exact he e (triangleEdgeSet_edge he')

theorem coordinateTriangle_weightedCount_restrict (n : ℕ) (q : Finset (Fin n) → ℝ) :
    hypergraphWeightedCount (coordinateTriangleHypergraph n) (fun e => q e.val)=weightedTriangleCount q := by
  rw [coordinateTriangle_weightedCount]
  apply weightedTriangleCount_congr
  intro e he
  exact extendGraphEdges_coe _ ⟨e,he⟩

/-- The generic hypergraph entropy minimum is exactly the manuscript's finite triangle minimum. -/
theorem coordinateTrianglePhi_eq (n : ℕ) (p η : ℝ) :
    hypergraphPhi (coordinateTriangleHypergraph n) 3 p η=finiteTrianglePhi n p η := by
  classical
  unfold hypergraphPhi finiteTrianglePhi
  congr 1
  ext v
  constructor
  · rintro ⟨q,hq,hcost⟩
    refine ⟨extendGraphEdges q,⟨?_,?_⟩,?_⟩
    · intro e he
      simpa only [extendGraphEdges_coe q ⟨e,he⟩] using hq.1 ⟨e,he⟩
    · have hh := hq.2
      rw [coordinateTriangle_weightedCount,coordinateTriangleHypergraph_card] at hh
      nlinarith
    · rw [finiteEdgeEntropy_eq_coordinate_sum]
      simpa only [extendGraphEdges_coe] using hcost
  · rintro ⟨q,hq,hcost⟩
    refine ⟨(fun e => q e.val),⟨?_,?_⟩,?_⟩
    · intro e
      exact hq.1 e.val e.property
    · change hypergraphWeightedCount (coordinateTriangleHypergraph n) (fun e => q e.val)≤_
      rw [coordinateTriangle_weightedCount_restrict,coordinateTriangleHypergraph_card]
      have hh := hq.2
      nlinarith
    · rw [← finiteEdgeEntropy_eq_coordinate_sum]
      exact hcost

end SparseLowerTail.Section03

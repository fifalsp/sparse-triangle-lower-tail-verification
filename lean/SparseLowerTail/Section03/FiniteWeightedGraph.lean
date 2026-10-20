import SparseLowerTail.Section03.FiniteCliqueSums

/-! Weighted simple graphs, their actual step graphons, and the exact formulas in s3:step. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

/-- The zero-diagonal adjacency matrix of unordered edge weights. -/
def graphEdgeMatrix {n : ℕ} (q : Finset (Fin n) → ℝ) (i j : Fin n) : ℝ :=
  if i=j then 0 else q {i,j}

/-- The expected triangle count of the independent graph with edge means q. -/
def weightedTriangleCount {n : ℕ} (q : Finset (Fin n) → ℝ) : ℝ :=
  ∑ T∈completeGraphTriangles n, ∏ e∈triangleEdgeSet T, q e

theorem graphEdgeMatrix_symm {n : ℕ} (q : Finset (Fin n) → ℝ) (i j : Fin n) :
    graphEdgeMatrix q i j=graphEdgeMatrix q j i := by
  classical
  by_cases hij : i=j <;> simp [graphEdgeMatrix,hij,Ne.symm,Finset.pair_comm]

theorem graphEdgeMatrix_bounds {n : ℕ} (q : Finset (Fin n) → ℝ)
    (hq : ∀ e∈completeGraphEdges n, q e∈Icc (0:ℝ) 1) (i j : Fin n) :
    graphEdgeMatrix q i j∈Icc (0:ℝ) 1 := by
  classical
  by_cases hij : i=j
  · simp [graphEdgeMatrix,hij]
  · simpa [graphEdgeMatrix,hij] using hq {i,j}
      (Finset.mem_powersetCard_univ.mpr (by simp [hij]))

theorem triangleEdgeSet_three {α : Type*} [DecidableEq α] (i j k : α)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ({i,j,k}:Finset α).powersetCard 2={{i,j},{i,k},{j,k}} := by
  rw [Finset.powersetCard_succ_insert (by simp [hij,hik])]
  have hc : ({j,k}:Finset α).card=2 := by simp [hjk]
  have hs : ({j,k}:Finset α).powersetCard 2={{j,k}} := hc ▸ Finset.powersetCard_self _
  rw [hs,Finset.powersetCard_one]
  ext a
  simp

/-- The ordered matrix triangle sum is exactly six times the unordered triangle count. -/
theorem graphEdgeMatrix_triangle_sum {n : ℕ} (q : Finset (Fin n) → ℝ) :
    (∑ i, ∑ j, ∑ k, graphEdgeMatrix q i j*graphEdgeMatrix q j k*graphEdgeMatrix q i k)=
      6*weightedTriangleCount q := by
  classical
  unfold weightedTriangleCount completeGraphTriangles
  rw [← sum_ordered_triples (fun T : Finset (Fin n) => ∏ e∈triangleEdgeSet T, q e)]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  by_cases hij : i=j
  · subst j; simp [graphEdgeMatrix]
  by_cases hik : i=k
  · subst k; simp [graphEdgeMatrix]
  by_cases hjk : j=k
  · subst k; simp [graphEdgeMatrix]
  have hpijik : ({i,j}:Finset (Fin n))≠{i,k} := by
    intro h
    have hm : j∈({i,k}:Finset (Fin n)) := h ▸ (by simp)
    have : j=i ∨ j=k := by simpa using hm
    exact this.elim (Ne.symm hij) hjk
  have hpijjk : ({i,j}:Finset (Fin n))≠{j,k} := by
    intro h
    have hm : i∈({j,k}:Finset (Fin n)) := h ▸ (by simp)
    have : i=j ∨ i=k := by simpa using hm
    exact this.elim hij hik
  have hpikjk : ({i,k}:Finset (Fin n))≠{j,k} := by
    intro h
    have hm : i∈({j,k}:Finset (Fin n)) := h ▸ (by simp)
    have : i=j ∨ i=k := by simpa using hm
    exact this.elim hij hik
  simp [graphEdgeMatrix,hij,hik,hjk,triangleEdgeSet,triangleEdgeSet_three i j k hij hik hjk,
    hpijik,hpijjk,hpikjk]
  ring

/-- Scale all edge means by p; every triangle product has exactly three factors. -/
theorem weightedTriangleCount_div {n : ℕ} (q : Finset (Fin n) → ℝ) (p : ℝ) :
    weightedTriangleCount (fun e => q e/p)=weightedTriangleCount q/p^3 := by
  unfold weightedTriangleCount
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.prod_div_distrib]
  have hc : (triangleEdgeSet T).card=3 := by
    simp [triangleEdgeSet,Finset.card_powersetCard,Finset.mem_powersetCard_univ.mp hT]
  simp [hc]

/-- The graphon's edge-weight representation used in the finite variational problem. -/
def edgeStepGraphon (n : ℕ) (hn : 0<n) (q : Finset (Fin n) → ℝ)
    (hq : ∀ e∈completeGraphEdges n, q e∈Icc (0:ℝ) 1) : Graphon :=
  matrixStepGraphon (uniformVertexPartition n hn) (graphEdgeMatrix q)
    (graphEdgeMatrix_symm q) (graphEdgeMatrix_bounds q hq)

theorem edgeStepGraphon_cost (n : ℕ) (hn : 0<n) (q : Finset (Fin n) → ℝ)
    (hq : ∀ e∈completeGraphEdges n, q e∈Icc (0:ℝ) 1) :
    cost (edgeStepGraphon n hn q hq)=
      2/(n:ℝ)^2*(∑ e∈completeGraphEdges n, entropy (q e))+1/(n:ℝ) := by
  classical
  rw [edgeStepGraphon,uniformStepGraphon_cost_zero_diagonal n hn _ _ _ (by intro i; simp [graphEdgeMatrix])]
  have he : (∑ i, ∑ j, if i=j then 0 else entropy (graphEdgeMatrix q i j))=
      ∑ i, ∑ j, if i=j then 0 else entropy (q {i,j}) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases hij : i=j <;> simp [graphEdgeMatrix,hij]
  rw [he,sum_ordered_pairs (fun e : Finset (Fin n) => entropy (q e))]
  unfold completeGraphEdges
  ring

theorem edgeStepGraphon_triangle (n : ℕ) (hn : 0<n) (q : Finset (Fin n) → ℝ)
    (hq : ∀ e∈completeGraphEdges n, q e∈Icc (0:ℝ) 1) :
    triangle (edgeStepGraphon n hn q hq)=6*weightedTriangleCount q/(n:ℝ)^3 := by
  rw [edgeStepGraphon,uniformStepGraphon_triangle,graphEdgeMatrix_triangle_sum]

end SparseLowerTail.Section03

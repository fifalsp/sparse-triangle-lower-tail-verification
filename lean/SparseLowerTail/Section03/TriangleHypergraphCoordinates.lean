import SparseLowerTail.Section03.TriangleHypergraph

/-! Reindex the triangle hypergraph by its genuine finite type of graph-edge coordinates. -/
noncomputable section
namespace SparseLowerTail.Section03

abbrev GraphEdgeCoordinate (n : ℕ) := {e : Finset (Fin n) // e∈completeGraphEdges n}

def projectGraphEdgeSet {n : ℕ} (S : Finset (GraphEdgeCoordinate n)) : Finset (Finset (Fin n)) :=
  S.map (Function.Embedding.subtype _)

def coordinateTriangleEdges {n : ℕ} (T : Finset (Fin n)) : Finset (GraphEdgeCoordinate n) :=
  (triangleEdgeSet T).subtype (fun e => e∈completeGraphEdges n)

def coordinateTriangleHypergraph (n : ℕ) : Finset (Finset (GraphEdgeCoordinate n)) :=
  (completeGraphTriangles n).image coordinateTriangleEdges

theorem graphEdgeCoordinate_card (n : ℕ) : Fintype.card (GraphEdgeCoordinate n)=n.choose 2 := by
  rw [Fintype.card_coe,completeGraphEdges_card]

theorem projectGraphEdgeSet_injective (n : ℕ) : Function.Injective (@projectGraphEdgeSet n) :=
  Finset.map_injective _

theorem projectGraphEdgeSet_card {n : ℕ} (S : Finset (GraphEdgeCoordinate n)) :
    (projectGraphEdgeSet S).card=S.card := Finset.card_map _

theorem projectGraphEdgeSet_subset {n : ℕ} (S : Finset (GraphEdgeCoordinate n)) :
    projectGraphEdgeSet S⊆completeGraphEdges n := by
  intro e he
  obtain ⟨e',_he',rfl⟩ := Finset.mem_map.mp he
  exact e'.property

theorem projectGraphEdgeSet_subset_iff {n : ℕ} (S T : Finset (GraphEdgeCoordinate n)) :
    projectGraphEdgeSet S⊆projectGraphEdgeSet T ↔ S⊆T := by
  exact Finset.map_subset_map

theorem project_coordinateTriangleEdges {n : ℕ} (T : Finset (Fin n)) :
    projectGraphEdgeSet (coordinateTriangleEdges T)=triangleEdgeSet T := by
  apply Finset.subtype_map_of_mem
  intro e he
  exact Finset.mem_powersetCard_univ.mpr (Finset.mem_powersetCard.mp he).2

theorem project_coordinateTriangleHypergraph (n : ℕ) :
    (coordinateTriangleHypergraph n).image projectGraphEdgeSet=triangleHyperedges n := by
  simp only [coordinateTriangleHypergraph,Finset.image_image,Function.comp_def,
    project_coordinateTriangleEdges,triangleHyperedges]

theorem coordinateTriangleHypergraph_card (n : ℕ) :
    (coordinateTriangleHypergraph n).card=n.choose 3 := by
  have hh := congrArg Finset.card (project_coordinateTriangleHypergraph n)
  rw [Finset.card_image_iff.mpr (projectGraphEdgeSet_injective n).injOn,triangleHyperedges_card] at hh
  exact hh

theorem coordinateTriangleHypergraph_uniform {n : ℕ} {A : Finset (GraphEdgeCoordinate n)}
    (hA : A∈coordinateTriangleHypergraph n) : A.card=3 := by
  have hh : projectGraphEdgeSet A∈triangleHyperedges n := by
    rw [← project_coordinateTriangleHypergraph]
    exact Finset.mem_image.mpr ⟨A,hA,rfl⟩
  simpa only [projectGraphEdgeSet_card] using triangleHyperedge_uniform hh

theorem coordinateTriangleHypergraph_codegree {n : ℕ} (S : Finset (GraphEdgeCoordinate n)) :
    ((coordinateTriangleHypergraph n).filter (fun A => S⊆A)).card=
      triangleCodegree n (projectGraphEdgeSet S) := by
  classical
  have heq : ((coordinateTriangleHypergraph n).filter (fun A => S⊆A)).image projectGraphEdgeSet=
      (triangleHyperedges n).filter (fun A => projectGraphEdgeSet S⊆A) := by
    rw [← project_coordinateTriangleHypergraph,Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro A _
    exact (projectGraphEdgeSet_subset_iff S A).symm
  have hh := congrArg Finset.card heq
  rw [Finset.card_image_iff.mpr (projectGraphEdgeSet_injective n).injOn] at hh
  exact hh

theorem coordinateTriangleHypergraph_codegree_condition (n : ℕ) (hn : 4≤n) {ell p : ℝ}
    (hell : 0<ell) (hp : (2/ell)/Real.sqrt n≤p) (S : Finset (GraphEdgeCoordinate n))
    (hScard : 1≤S.card ∧ S.card≤3) :
    (((coordinateTriangleHypergraph n).filter (fun A => S⊆A)).card:ℝ) ≤
      3*(ell*p)^(S.card-1)*(coordinateTriangleHypergraph n).card/Fintype.card (GraphEdgeCoordinate n) := by
  rw [coordinateTriangleHypergraph_codegree,coordinateTriangleHypergraph_card,graphEdgeCoordinate_card]
  have hh := triangle_hypergraph_codegree_condition n hn hell hp (projectGraphEdgeSet S)
    (projectGraphEdgeSet_subset S) (by simpa only [projectGraphEdgeSet_card] using hScard)
  simpa only [projectGraphEdgeSet_card,triangleHyperedges_card,completeGraphEdges_card] using hh

end SparseLowerTail.Section03

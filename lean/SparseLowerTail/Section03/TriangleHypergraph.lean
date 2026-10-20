import SparseLowerTail.Section03.DecorrelationBounds
import Mathlib.Data.Fintype.Powerset

/-! The actual hypergraph of triangles of the complete graph, with graph edges as vertices. -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- Unordered edges of the complete n-vertex graph. -/
def completeGraphEdges (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard 2

def completeGraphTriangles (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard 3

/-- A triangle's three unordered graph edges. -/
def triangleEdgeSet {n : ℕ} (T : Finset (Fin n)) : Finset (Finset (Fin n)) := T.powersetCard 2

def triangleHyperedges (n : ℕ) : Finset (Finset (Finset (Fin n))) :=
  (completeGraphTriangles n).image triangleEdgeSet

/-- Codegree counts hyperedges containing every edge in S. -/
def triangleCodegree (n : ℕ) (S : Finset (Finset (Fin n))) : ℕ :=
  ((triangleHyperedges n).filter (fun H => S⊆H)).card

theorem completeGraphEdges_card (n : ℕ) : (completeGraphEdges n).card=n.choose 2 := by
  simp [completeGraphEdges,Finset.card_powersetCard]

theorem completeGraphTriangles_card (n : ℕ) : (completeGraphTriangles n).card=n.choose 3 := by
  simp [completeGraphTriangles,Finset.card_powersetCard]

/-- A set of at least two vertices is recovered from all its pairs. -/
theorem biUnion_triangleEdgeSet {n : ℕ} (T : Finset (Fin n)) (hT : 2≤T.card) :
    (triangleEdgeSet T).biUnion id=T := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨e,he,hxe⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_powersetCard.mp he).1 hxe
  · intro hx
    obtain ⟨y,hy,hyx⟩ := T.exists_mem_ne (by omega) x
    apply Finset.mem_biUnion.mpr
    refine ⟨{x,y},Finset.mem_powersetCard.mpr ⟨?_,?_⟩,by simp⟩
    · intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> assumption
    · simp [Ne.symm hyx]

theorem triangleEdgeSet_injective_on_triangles (n : ℕ) :
    Set.InjOn (@triangleEdgeSet n) (↑(completeGraphTriangles n)) := by
  intro A hA B hB h
  have hAc : A.card=3 := Finset.mem_powersetCard_univ.mp hA
  have hBc : B.card=3 := Finset.mem_powersetCard_univ.mp hB
  have hh := congrArg (fun H : Finset (Finset (Fin n)) => H.biUnion id) h
  simpa only [biUnion_triangleEdgeSet A (by omega),biUnion_triangleEdgeSet B (by omega)] using hh

theorem triangleHyperedges_card (n : ℕ) : (triangleHyperedges n).card=n.choose 3 := by
  rw [triangleHyperedges,Finset.card_image_iff.mpr (triangleEdgeSet_injective_on_triangles n)]
  exact completeGraphTriangles_card n

theorem triangleHyperedge_uniform {n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : H∈triangleHyperedges n) : H.card=3 := by
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hH
  have hc : T.card=3 := Finset.mem_powersetCard_univ.mp hT
  simp [triangleEdgeSet,Finset.card_powersetCard,hc]

theorem triangleHyperedge_vertices {n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : H∈triangleHyperedges n) : H⊆completeGraphEdges n := by
  obtain ⟨T,_hT,rfl⟩ := Finset.mem_image.mp hH
  intro e he
  exact Finset.mem_powersetCard_univ.mpr (Finset.mem_powersetCard.mp he).2

/-- Triangles through a fixed graph edge are obtained by adjoining one outside vertex. -/
theorem triangles_containing_edge {n : ℕ} (e : Finset (Fin n)) (he : e.card=2) :
    (completeGraphTriangles n).filter (fun T => e⊆T)=
      (Finset.univ\e).image (fun v => insert v e) := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨hTc,heT⟩ := Finset.mem_filter.mp hT
    have hc : T.card=3 := Finset.mem_powersetCard_univ.mp hTc
    obtain ⟨v,hv,hvT⟩ := Finset.exists_eq_insert_iff.mpr ⟨heT,by omega⟩
    exact Finset.mem_image.mpr ⟨v,by simp [hv],hvT⟩
  · intro hT
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hT
    have hv' : v∉e := (Finset.mem_sdiff.mp hv).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powersetCard_univ.mpr (by simp [hv',he]),Finset.subset_insert v e⟩

theorem triangles_containing_edge_card {n : ℕ} (e : Finset (Fin n)) (he : e.card=2) :
    ((completeGraphTriangles n).filter (fun T => e⊆T)).card=n-2 := by
  classical
  rw [triangles_containing_edge e he]
  have hinj : Set.InjOn (fun v => insert v e) (↑(Finset.univ\e : Finset (Fin n))) := by
    intro v hv w _hw h
    have hv' : v∉e := (Finset.mem_sdiff.mp hv).2
    change insert v e=insert w e at h
    have hvw : v∈insert w e := by rw [← h]; exact Finset.mem_insert_self _ _
    simpa [hv'] using hvw
  rw [Finset.card_image_iff.mpr hinj,Finset.card_sdiff]
  simp [he]

/-- The degree of every graph edge in the triangle hypergraph is exactly n-2. -/
theorem triangleCodegree_singleton {n : ℕ} (e : Finset (Fin n)) (he : e∈completeGraphEdges n) :
    triangleCodegree n {e}=n-2 := by
  classical
  have hc : e.card=2 := Finset.mem_powersetCard_univ.mp he
  have heq : (triangleHyperedges n).filter (fun H => ({e}:Finset _)⊆H) =
      ((completeGraphTriangles n).filter (fun T => e⊆T)).image triangleEdgeSet := by
    ext H
    simp only [triangleHyperedges,Finset.mem_filter,Finset.mem_image,Finset.singleton_subset_iff]
    constructor
    · rintro ⟨⟨T,hT,rfl⟩,heT⟩
      exact ⟨T,⟨hT,(Finset.mem_powersetCard.mp heT).1⟩,rfl⟩
    · rintro ⟨T,⟨hT,heT⟩,rfl⟩
      exact ⟨⟨T,hT,rfl⟩,Finset.mem_powersetCard.mpr ⟨heT,hc⟩⟩
  unfold triangleCodegree
  rw [heq,Finset.card_image_iff.mpr ((triangleEdgeSet_injective_on_triangles n).mono
    (fun _ h => (Finset.mem_filter.mp h).1))]
  exact triangles_containing_edge_card e hc

/-- Two distinct pairs use at least three vertices. -/
theorem three_le_card_union_pairs {n : ℕ} (e f : Finset (Fin n))
    (he : e.card=2) (hf : f.card=2) (hne : e≠f) : 3≤(e∪f).card := by
  by_contra hh
  have hle : (e∪f).card≤e.card := by omega
  have heq := Finset.eq_of_subset_of_card_le (Finset.subset_union_left : e⊆e∪f) hle
  have hfe : f⊆e := heq ▸ Finset.subset_union_right
  have hfeq : f=e := Finset.eq_of_subset_of_card_le hfe (by omega)
  exact hne hfeq.symm

/-- A triangle containing two distinct graph edges is unique. -/
theorem triangle_unique_of_two_edges {n : ℕ} (e f T U : Finset (Fin n))
    (he : e.card=2) (hf : f.card=2) (hne : e≠f) (hT : T.card=3) (hU : U.card=3)
    (heT : e⊆T) (hfT : f⊆T) (heU : e⊆U) (hfU : f⊆U) : T=U := by
  have hu := three_le_card_union_pairs e f he hf hne
  have ht := Finset.eq_of_subset_of_card_le (Finset.union_subset heT hfT) (by omega)
  have hu' := Finset.eq_of_subset_of_card_le (Finset.union_subset heU hfU) (by omega)
  exact ht.symm.trans hu'

/-- Every codegree involving at least two distinct graph edges is at most one. -/
theorem triangleCodegree_le_one {n : ℕ} (S : Finset (Finset (Fin n))) (hS : 2≤S.card) :
    triangleCodegree n S≤1 := by
  classical
  obtain ⟨e,heS,f,hfS,hne⟩ := Finset.one_lt_card.mp (by omega : 1<S.card)
  unfold triangleCodegree
  apply Finset.card_le_one.mpr
  intro H hH J hJ
  obtain ⟨hHH,hSH⟩ := Finset.mem_filter.mp hH
  obtain ⟨hJJ,hSJ⟩ := Finset.mem_filter.mp hJ
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hHH
  obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hJJ
  have heT := Finset.mem_powersetCard.mp (hSH heS)
  have hfT := Finset.mem_powersetCard.mp (hSH hfS)
  have heU := Finset.mem_powersetCard.mp (hSJ heS)
  have hfU := Finset.mem_powersetCard.mp (hSJ hfS)
  have hTU := triangle_unique_of_two_edges e f T U heT.2 hfT.2 hne
    (Finset.mem_powersetCard_univ.mp hT) (Finset.mem_powersetCard_univ.mp hU)
    heT.1 hfT.1 heU.1 hfU.1
  rw [hTU]

/-- The complete triangle hypergraph satisfies all three actual codegree inequalities. -/
theorem triangle_hypergraph_codegree_condition (n : ℕ) (hn : 4≤n) {ell p : ℝ}
    (hell : 0<ell) (hp : (2/ell)/Real.sqrt n≤p)
    (S : Finset (Finset (Fin n))) (hSV : S⊆completeGraphEdges n)
    (hScard : 1≤S.card ∧ S.card≤3) :
    (triangleCodegree n S:ℝ) ≤
      3*(ell*p)^(S.card-1)*(triangleHyperedges n).card/(completeGraphEdges n).card := by
  have hreq := sparse_threshold_requirements n hn hell hp
  have hnum := triangle_numeric_codegree_bounds n hn hreq.1 hreq.2.1 hreq.2.2
  rw [triangleHyperedges_card,completeGraphEdges_card]
  change (triangleCodegree n S:ℝ)≤3*(ell*p)^(S.card-1)*triangleEdgeCount n/triangleVertexCount n
  by_cases hs : S.card=1
  · obtain ⟨e,rfl⟩ := Finset.card_eq_one.mp hs
    have he : e∈completeGraphEdges n := hSV (Finset.mem_singleton_self e)
    rw [triangleCodegree_singleton e he]
    simp only [Finset.card_singleton,Nat.sub_self,pow_zero,mul_one]
    rw [Nat.cast_sub (by omega : 2≤n)]
    norm_num only [Nat.cast_ofNat]
    exact hnum.1
  · have hdeg : (triangleCodegree n S:ℝ)≤1 := by exact_mod_cast triangleCodegree_le_one S (by omega)
    have hs' : S.card=2 ∨ S.card=3 := by omega
    rcases hs' with hs'|hs'
    · rw [hs']; norm_num only [Nat.reduceSub,pow_one]
      exact hdeg.trans hnum.2.1
    · rw [hs']; norm_num only [Nat.reduceSub]
      exact hdeg.trans hnum.2.2

end SparseLowerTail.Section03

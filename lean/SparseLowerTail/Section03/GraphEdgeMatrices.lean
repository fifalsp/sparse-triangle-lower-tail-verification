import SparseLowerTail.Section03.GraphEdgeEndpoints

/-! Identify endpoint-sum matrices with the manuscript's unordered-edge adjacency matrices. -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- An increasing presentation of an edge agrees with its selected endpoint enumeration. -/
theorem graphEdgeEndpoints_eq_of_ordered_pair {n : ℕ} (e : GraphEdgeCoordinate n) {u v : Fin n}
    (huv : u<v) (he : e.val={u,v}) : graphEdgeEndpoints e=(u,v) := by
  have ha : (graphEdgeEndpoints e).1=u ∨ (graphEdgeEndpoints e).1=v := by
    have hh : (graphEdgeEndpoints e).1∈e.val := by rw [graphEdgeEndpoints_pair]; simp
    simpa only [he,Finset.mem_insert,Finset.mem_singleton] using hh
  have hb : (graphEdgeEndpoints e).2=u ∨ (graphEdgeEndpoints e).2=v := by
    have hh : (graphEdgeEndpoints e).2∈e.val := by rw [graphEdgeEndpoints_pair]; simp
    simpa only [he,Finset.mem_insert,Finset.mem_singleton] using hh
  have ho := graphEdgeEndpoints_ordered e
  rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals first | exact Prod.ext ha hb | exfalso; rw [ha,hb] at ho; omega

/-- At an increasing vertex pair, the endpoint sum contains exactly its one edge weight. -/
theorem symmetricEdgeMatrix_graphEdgeEndpoints_ordered {n : ℕ} (q : GraphEdgeCoordinate n → ℝ)
    {u v : Fin n} (huv : u<v) :
    symmetricEdgeMatrix graphEdgeEndpoints q u v =
      q ⟨{u,v},Finset.mem_powersetCard_univ.mpr (by simp [ne_of_lt huv])⟩ := by
  let e : GraphEdgeCoordinate n := ⟨{u,v},Finset.mem_powersetCard_univ.mpr (by simp [ne_of_lt huv])⟩
  have he : graphEdgeEndpoints e=(u,v) := graphEdgeEndpoints_eq_of_ordered_pair e huv rfl
  have hdir : ∀ f : GraphEdgeCoordinate n, (u,v)=graphEdgeEndpoints f ↔ f=e := by
    intro f
    constructor
    · intro hf
      exact graphEdgeEndpoints_injective n (hf.symm.trans he.symm)
    · intro hf
      simpa only [hf] using he.symm
  have hrev : ∀ f : GraphEdgeCoordinate n, (v,u)≠graphEdgeEndpoints f := by
    intro f hf
    have hh := graphEdgeEndpoints_ordered f
    rw [← hf] at hh
    exact (not_lt_of_ge huv.le) hh
  simp [symmetricEdgeMatrix,hdir,hrev,e]

/-- The two actual representations of an arbitrary real weighted adjacency matrix agree. -/
theorem symmetricEdgeMatrix_graphEdgeEndpoints {n : ℕ} (q : GraphEdgeCoordinate n → ℝ) :
    symmetricEdgeMatrix graphEdgeEndpoints q=graphEdgeMatrix (extendGraphEdges q) := by
  funext u v
  rcases lt_trichotomy u v with huv | huv | huv
  · rw [symmetricEdgeMatrix_graphEdgeEndpoints_ordered q huv]
    rw [graphEdgeMatrix,if_neg (ne_of_lt huv)]
    exact (extendGraphEdges_coe q ⟨{u,v},Finset.mem_powersetCard_univ.mpr (by simp [ne_of_lt huv])⟩).symm
  · subst v
    rw [symmetricEdgeMatrix_diagonal graphEdgeEndpoints graphEdgeEndpoints_ordered]
    simp [graphEdgeMatrix]
  · rw [symmetricEdgeMatrix_symm graphEdgeEndpoints q,graphEdgeMatrix_symm]
    rw [symmetricEdgeMatrix_graphEdgeEndpoints_ordered q huv]
    rw [graphEdgeMatrix,if_neg (ne_of_lt huv)]
    exact (extendGraphEdges_coe q ⟨{v,u},Finset.mem_powersetCard_univ.mpr (by simp [ne_of_lt huv])⟩).symm

/-- An endpoint sum can be restricted to any set outside which all weights vanish. -/
theorem symmetricEdgeMatrix_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (ends : ι → Fin n×Fin n) (S : Finset ι) (a : ι → ℝ) (hzero : ∀ i∉S, a i=0) :
    symmetricEdgeMatrix ends a=symmetricEdgeMatrix (fun i : S => ends i) (fun i : S => a i) := by
  funext u v
  unfold symmetricEdgeMatrix
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun i => (if (u,v)=ends i then a i else 0)+(if (v,u)=ends i then a i else 0))]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp [hzero i hi]

/-- Subtracting coordinate vectors subtracts their actual weighted adjacency matrices. -/
theorem graphEdgeMatrix_extend_sub {n : ℕ} (a b : GraphEdgeCoordinate n → ℝ) :
    graphEdgeMatrix (extendGraphEdges (fun i => a i-b i)) =
      (fun u v => graphEdgeMatrix (extendGraphEdges a) u v-graphEdgeMatrix (extendGraphEdges b) u v) := by
  classical
  funext u v
  by_cases huv : u=v
  · simp [graphEdgeMatrix,huv]
  · simp only [graphEdgeMatrix,if_neg huv]
    have he : {u,v}∈completeGraphEdges n := Finset.mem_powersetCard_univ.mpr (by simp [huv])
    simp [extendGraphEdges,he]

/-- Nonnegative edge weights bound every normalized matrix rectangle by twice their total mass. -/
theorem symmetricEdgeMatrix_cutNorm_le {ι : Type*} [Fintype ι] {n : ℕ}
    (ends : ι → Fin n×Fin n) (a : ι → ℝ) (ha : ∀ i, 0≤a i) :
    finiteMatrixCutNorm (symmetricEdgeMatrix ends a)≤2*(∑ i, a i)/(n:ℝ)^2 := by
  unfold finiteMatrixCutNorm
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sup'_le
  intro xy _
  rw [symmetricEdgeMatrix_rectangle]
  calc
    _≤∑ i, |rectangleEdgeCoefficient ends xy i*a i| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ i, 2*a i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (ha i)]
      exact mul_le_mul_of_nonneg_right (rectangleEdgeCoefficient_abs_le ends xy i) (ha i)
    _=2*(∑ i, a i) := by rw [Finset.mul_sum]

/-- Scaling edge weights scales every entry of the genuine adjacency matrix. -/
theorem graphEdgeMatrix_div {n : ℕ} (a : Finset (Fin n) → ℝ) (p : ℝ) :
    graphEdgeMatrix (fun e => a e/p)=(fun u v => graphEdgeMatrix a u v/p) := by
  classical
  funext u v
  by_cases huv : u=v <;> simp [graphEdgeMatrix,huv]

end SparseLowerTail.Section03

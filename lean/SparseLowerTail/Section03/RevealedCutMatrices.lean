import SparseLowerTail.Section03.GraphEdgeMatrices
import SparseLowerTail.Section03.RevealedCutConcentration
import SparseLowerTail.Section03.RevealedEdgeTail
import SparseLowerTail.Section03.MatrixCutBounds

/-! The cut-concentration matrix is exactly the difference of the actual erased adjacency and means. -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Section03

def erasedBooleanCoordinates {ι : Type*} [DecidableEq ι] (W : Finset ι) (z : ι → Bool) (i : ι) : ℝ :=
  if i∈W then 0 else (z i).toNat

/-- The concentration matrix and the original graph's erased-edge matrix difference coincide. -/
theorem unrevealed_cut_matrix_eq {n : ℕ} (q : (GraphEdgeCoordinate n → Bool) → ℝ)
    (W : Finset (GraphEdgeCoordinate n)) (y : W → Bool) (z : ↑Wᶜ → Bool) :
    symmetricEdgeMatrix (unrevealedEdgeEndpoints W)
      (fun i => (z i).toNat-unrevealedConditionalMeans q W y i) =
    (fun u v => graphEdgeMatrix (extendGraphEdges (erasedBooleanCoordinates W ((splitCoordinates W).symm (y,z)))) u v-
      graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans q W y)) u v) := by
  let a := fun i => erasedBooleanCoordinates W ((splitCoordinates W).symm (y,z)) i-erasedConditionalMeans q W y i
  have hzero : ∀ i∉Wᶜ, a i=0 := by
    intro i hi
    have hiW : i∈W := by simpa only [Finset.mem_compl,not_not] using hi
    simp [a,erasedBooleanCoordinates,erasedConditionalMeans,hiW]
  have hrest : (fun i : ↑Wᶜ => a i)=(fun i : ↑Wᶜ => (z i).toNat-unrevealedConditionalMeans q W y i) := by
    funext i
    have hi : i.val∉W := Finset.mem_compl.mp i.property
    simp only [a,erasedBooleanCoordinates,erasedConditionalMeans,if_neg hi,splitCoordinates_symm_snd,
      unrevealedConditionalMeans,unrevealedConditionalLaw_marginal_true]
  have hh := symmetricEdgeMatrix_restrict graphEdgeEndpoints Wᶜ a hzero
  rw [hrest] at hh
  calc
    _ = symmetricEdgeMatrix graphEdgeEndpoints a := hh.symm
    _ = graphEdgeMatrix (extendGraphEdges a) := symmetricEdgeMatrix_graphEdgeEndpoints a
    _ = _ := graphEdgeMatrix_extend_sub _ _

/-- The concentration event, written directly in the original graph-edge space. -/
theorem revealedFamilyEvent_cut_eq {n : ℕ} (q : (GraphEdgeCoordinate n → Bool) → ℝ)
    (W : Finset (GraphEdgeCoordinate n)) (ε p : ℝ) :
    revealedFamilyEvent W (fun y => unrevealedCutEvent q W y ε p)=
      Finset.univ.filter (fun z => (ε/4)*p<finiteMatrixCutNorm (fun u v =>
        graphEdgeMatrix (extendGraphEdges (erasedBooleanCoordinates W z)) u v-
        graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans q W (splitCoordinates W z).1)) u v)) := by
  classical
  ext z
  simp only [revealedFamilyEvent,unrevealedCutEvent,Finset.mem_filter,Finset.mem_univ,true_and]
  have hh := unrevealed_cut_matrix_eq q W (splitCoordinates W z).1 (splitCoordinates W z).2
  rw [Prod.mk.eta,Equiv.symm_apply_apply] at hh
  rw [hh]

/-- Removing the present revealed edges changes the matrix cut norm by at most 2N_W/n². -/
theorem erasedBooleanCoordinates_cut_difference {n : ℕ} (W : Finset (GraphEdgeCoordinate n))
    (z : GraphEdgeCoordinate n → Bool) :
    finiteMatrixCutNorm (fun u v => graphEdgeMatrix (extendGraphEdges (fun i => ((z i).toNat:ℝ))) u v-
      graphEdgeMatrix (extendGraphEdges (erasedBooleanCoordinates W z)) u v)≤2*revealedEdgeCount W z/(n:ℝ)^2 := by
  let a := fun i : GraphEdgeCoordinate n => ((z i).toNat:ℝ)-erasedBooleanCoordinates W z i
  have ha : ∀ i, 0≤a i := by
    intro i
    by_cases hi : i∈W <;> simp [a,erasedBooleanCoordinates,hi]
  have hsum : ∑ i, a i=revealedEdgeCount W z := by
    have he : ∀ i, a i=if i∈W then ((z i).toNat:ℝ) else 0 := by
      intro i
      by_cases hi : i∈W <;> simp [a,erasedBooleanCoordinates,hi]
    simp_rw [he]
    simp only [Finset.sum_ite_mem,Finset.univ_inter,revealedEdgeCount]
  have hh := symmetricEdgeMatrix_cutNorm_le graphEdgeEndpoints a ha
  rw [symmetricEdgeMatrix_graphEdgeEndpoints,graphEdgeMatrix_extend_sub,hsum] at hh
  exact hh

/-- Few revealed edges and a small unrevealed cut error imply the required normalized matrix proximity. -/
theorem normalized_graph_matrix_close (n : ℕ) (hn : 0<n)
    (q : (GraphEdgeCoordinate n → Bool) → ℝ) (W : Finset (GraphEdgeCoordinate n))
    (y : W → Bool) (z : GraphEdgeCoordinate n → Bool) {p α ε : ℝ} (hp : 0<p) (hα : α≤ε/16)
    (hcount : revealedEdgeCount W z≤2*α*p*(n:ℝ)^2)
    (hcut : finiteMatrixCutNorm (fun u v => graphEdgeMatrix (extendGraphEdges (erasedBooleanCoordinates W z)) u v-
      graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans q W y)) u v)≤(ε/4)*p) :
    finiteMatrixCutNorm (fun u v => (graphEdgeMatrix (extendGraphEdges (fun i => ((z i).toNat:ℝ))) u v-
      graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans q W y)) u v)/p)≤ε/2 := by
  let A := graphEdgeMatrix (extendGraphEdges (fun i => ((z i).toNat:ℝ)))
  let B := graphEdgeMatrix (extendGraphEdges (erasedBooleanCoordinates W z))
  let C := graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans q W y))
  have hn2 : 0<(n:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hn)
  have hdelete : finiteMatrixCutNorm (fun u v => A u v-B u v)≤4*α*p := by
    have hh := erasedBooleanCoordinates_cut_difference W z
    apply hh.trans
    apply (div_le_iff₀ hn2).mpr
    nlinarith
  have hsum : finiteMatrixCutNorm (fun u v => A u v-C u v)≤4*α*p+(ε/4)*p := by
    have he : (fun u v => A u v-C u v)=(fun u v => (A u v-B u v)+(B u v-C u v)) := by funext u v; ring
    rw [he]
    exact (finiteMatrixCutNorm_add_le _ _).trans (add_le_add hdelete hcut)
  have hdiv := (finiteMatrixCutNorm_div_le (fun u v => A u v-C u v) hp).trans
    (div_le_div_of_nonneg_right hsum hp.le)
  apply hdiv.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_le_mul_of_nonneg_right hα hp.le]

end SparseLowerTail.Section03

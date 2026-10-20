import SparseLowerTail.Section03.HypergraphVariational
import SparseLowerTail.Section03.BernoulliConcentration

/-! Ordered endpoint enumeration of the actual graph-edge coordinate type. -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- Every genuine graph-edge coordinate has a unique increasing pair of endpoints. -/
theorem graphEdgeCoordinate_exists_ordered_pair {n : ℕ} (e : GraphEdgeCoordinate n) :
    ∃ a b : Fin n, a<b ∧ e.val={a,b} := by
  have hc : e.val.card=2 := Finset.mem_powersetCard_univ.mp e.property
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp hc
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact ⟨a,b,hlt,he⟩
  · exact ⟨b,a,hgt,he.trans (Finset.pair_comm _ _)⟩

def graphEdgeEndpoints {n : ℕ} (e : GraphEdgeCoordinate n) : Fin n×Fin n :=
  ⟨(graphEdgeCoordinate_exists_ordered_pair e).choose,
    (graphEdgeCoordinate_exists_ordered_pair e).choose_spec.choose⟩

theorem graphEdgeEndpoints_ordered {n : ℕ} (e : GraphEdgeCoordinate n) :
    (graphEdgeEndpoints e).1<(graphEdgeEndpoints e).2 :=
  (graphEdgeCoordinate_exists_ordered_pair e).choose_spec.choose_spec.1

theorem graphEdgeEndpoints_pair {n : ℕ} (e : GraphEdgeCoordinate n) :
    e.val={(graphEdgeEndpoints e).1,(graphEdgeEndpoints e).2} :=
  (graphEdgeCoordinate_exists_ordered_pair e).choose_spec.choose_spec.2

theorem graphEdgeEndpoints_injective (n : ℕ) : Function.Injective (@graphEdgeEndpoints n) := by
  intro e f hef
  apply Subtype.ext
  rw [graphEdgeEndpoints_pair e,graphEdgeEndpoints_pair f,hef]

def unrevealedEdgeEndpoints {n : ℕ} (W : Finset (GraphEdgeCoordinate n))
    (i : ↑Wᶜ) : Fin n×Fin n := graphEdgeEndpoints i.val

theorem unrevealedEdgeEndpoints_injective {n : ℕ} (W : Finset (GraphEdgeCoordinate n)) :
    Function.Injective (unrevealedEdgeEndpoints W) := by
  intro e f hef
  apply Subtype.ext
  exact graphEdgeEndpoints_injective n hef

theorem unrevealedEdgeEndpoints_ordered {n : ℕ} (W : Finset (GraphEdgeCoordinate n)) (i : ↑Wᶜ) :
    (unrevealedEdgeEndpoints W i).1<(unrevealedEdgeEndpoints W i).2 := graphEdgeEndpoints_ordered i.val

end SparseLowerTail.Section03

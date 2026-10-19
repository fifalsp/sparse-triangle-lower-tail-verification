import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# The continuation step in Theorem 1.3

This is the order-theoretic argument in Section 8, Steps 1--4. The assumptions
are explicit: this lemma does not establish the graphon-specific inputs.
-/
namespace SparseLowerTail

/-- A classification propagates through an interval if it holds near both ends,
is open to the left, and cannot fail at a boundary above the lower known range.
`boundary` is where the paper's boundary and tie-exclusion lemmas enter. -/
theorem classification_on_interval
    (good : ℝ → Prop) (lower upper : ℝ)
    (hlower : 0 < lower)
    (small : ∀ r, 0 < r → r ≤ lower → good r)
    (open_left : ∀ r, 0 < r → r < upper → good r →
      ∃ ε > 0, ∀ s, r - ε < s → s ≤ r → 0 < s → good s)
    (seed : ∃ s, 0 < s ∧ s < upper ∧ ∀ r, s < r → r < upper → good r)
    (boundary : ∀ r, lower ≤ r → r < upper →
      (∀ s, r < s → s < upper → good s) → good r) :
    ∀ r, 0 < r → r < upper → good r := by
  let S : Set ℝ := {s | 0 < s ∧ s < upper ∧
    ∀ r, s < r → r < upper → good r}
  have hne : S.Nonempty := seed
  have hbdd : BddBelow S := ⟨0, fun s hs => le_of_lt hs.1⟩
  let r₀ := sInf S
  have hzero : 0 ≤ r₀ := le_csInf hne (fun s hs => le_of_lt hs.1)
  obtain ⟨s, hs⟩ := hne
  have htop : r₀ < upper := lt_of_le_of_lt (csInf_le hbdd hs) hs.2.1
  have habove : ∀ r, r₀ < r → r < upper → good r := by
    intro r hr hru
    obtain ⟨s, hsS, hsr⟩ := exists_lt_of_csInf_lt ⟨s, hs⟩ hr
    exact hsS.2.2 r hsr hru
  have hbelow : r₀ < lower := by
    by_contra hn
    have hlr : lower ≤ r₀ := le_of_not_gt hn
    have hrpos : 0 < r₀ := lt_of_lt_of_le hlower hlr
    have hg : good r₀ := boundary r₀ hlr htop habove
    obtain ⟨ε, hε, hopen⟩ := open_left r₀ hrpos htop hg
    let δ := min (ε / 2) (r₀ / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by linarith)
    have hδε : δ ≤ ε / 2 := min_le_left _ _
    have hδr : δ ≤ r₀ / 2 := min_le_right _ _
    have hnew : r₀ - δ ∈ S := by
      refine ⟨by linarith, by linarith, ?_⟩
      intro t ht htu
      by_cases htr : r₀ < t
      · exact habove t htr htu
      · exact hopen t (by linarith) (le_of_not_gt htr) (by linarith)
    have := csInf_le hbdd hnew
    change r₀ ≤ r₀ - δ at this
    linarith
  intro r hr hru
  by_cases hrl : r ≤ lower
  · exact small r hr hrl
  · exact habove r (lt_trans hbelow (lt_of_not_ge hrl)) hru

end SparseLowerTail

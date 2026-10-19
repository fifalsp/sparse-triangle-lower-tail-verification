import SparseLowerTail.Section05.SortedLogBoxes

/-! Exact rectangular subdivision for kernel-checked cover replay.
A tree carries actual leaf proofs; the coverage theorem follows recursively
from a rational cut of one coordinate and does not assume a cover relation. -/
noncomputable section
namespace SparseLowerTail.Section05

def edgeCoordinate (q : EdgeTriple) : Fin 3 → ℝ := ![q.1.1,q.1.2,q.2]

/-- Rational endpoints, as used by a dyadic interval certificate. -/
structure LogBox where
  lower : Fin 3 → ℚ
  upper : Fin 3 → ℚ

@[ext] theorem LogBox.ext {B C : LogBox}
    (hl : ∀ i, B.lower i=C.lower i) (hu : ∀ i, B.upper i=C.upper i) : B=C := by
  cases B
  cases C
  simp only [LogBox.mk.injEq]
  exact ⟨funext hl,funext hu⟩

def LogBox.region (B : LogBox) : Set EdgeTriple :=
  {q | ∀ i, (B.lower i : ℝ) ≤ edgeCoordinate q i ∧ edgeCoordinate q i ≤ (B.upper i : ℝ)}

def LogBox.left (B : LogBox) (i : Fin 3) (c : ℚ) : LogBox :=
  ⟨B.lower,Function.update B.upper i c⟩

def LogBox.right (B : LogBox) (i : Fin 3) (c : ℚ) : LogBox :=
  ⟨Function.update B.lower i c,B.upper⟩

def LogBox.CutInside (B : LogBox) (i : Fin 3) (c : ℚ) : Prop :=
  B.lower i ≤ c ∧ c ≤ B.upper i

/-- A split has no omitted middle interval, including at the cut itself. -/
theorem LogBox.mem_left_or_right {B : LogBox} {q : EdgeTriple} (hq : q ∈ B.region)
    (i : Fin 3) (c : ℚ) : q ∈ (B.left i c).region ∨ q ∈ (B.right i c).region := by
  rcases le_total (edgeCoordinate q i) (c : ℝ) with h | h
  · left
    intro j
    by_cases hj : j=i
    · subst j
      exact ⟨(hq i).1,by simpa [LogBox.left] using h⟩
    · simpa [LogBox.left,Function.update_of_ne hj] using hq j
  · right
    intro j
    by_cases hj : j=i
    · subst j
      exact ⟨by simpa [LogBox.right] using h,(hq i).2⟩
    · simpa [LogBox.right,Function.update_of_ne hj] using hq j

theorem LogBox.left_subset {B : LogBox} {i : Fin 3} {c : ℚ} (hc : B.CutInside i c) :
    (B.left i c).region ⊆ B.region := by
  intro q hq j
  by_cases hj : j=i
  · subst j
    have h := hq i
    simp [LogBox.left] at h
    exact ⟨h.1,h.2.trans (by exact_mod_cast hc.2)⟩
  · simpa [LogBox.left,Function.update_of_ne hj] using hq j

theorem LogBox.right_subset {B : LogBox} {i : Fin 3} {c : ℚ} (hc : B.CutInside i c) :
    (B.right i c).region ⊆ B.region := by
  intro q hq j
  by_cases hj : j=i
  · subst j
    have h := hq i
    simp [LogBox.right] at h
    have hcl : (B.lower i : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc.1
    exact ⟨hcl.trans h.1,h.2⟩
  · simpa [LogBox.right,Function.update_of_ne hj] using hq j

/-- Exact set equality, not merely a volume comparison or sampled cover. -/
theorem LogBox.split_region {B : LogBox} {i : Fin 3} {c : ℚ} (hc : B.CutInside i c) :
    B.region=(B.left i c).region ∪ (B.right i c).region := by
  ext q
  constructor
  · intro hq
    exact B.mem_left_or_right hq i c
  · rintro (hq | hq)
    · exact B.left_subset hc hq
    · exact B.right_subset hc hq

/-- A finite, proof-producing subdivision tree. There is no unchecked leaf status:
every leaf supplies a proof on its whole box (or on its specified domain). -/
inductive CheckedLogBoxTree (D : Set EdgeTriple) (P : EdgeTriple → Prop) : LogBox → Type
  | leaf (B : LogBox) (proof : ∀ q ∈ B.region, q ∈ D → P q) : CheckedLogBoxTree D P B
  | split (B : LogBox) (i : Fin 3) (c : ℚ) (inside : B.CutInside i c)
      (left : CheckedLogBoxTree D P (B.left i c))
      (right : CheckedLogBoxTree D P (B.right i c)) : CheckedLogBoxTree D P B

/-- The tree's leaf proofs imply its conclusion everywhere in the root box. -/
theorem CheckedLogBoxTree.sound {D : Set EdgeTriple} {P : EdgeTriple → Prop} {B : LogBox}
    (T : CheckedLogBoxTree D P B) : ∀ q ∈ B.region, q ∈ D → P q := by
  induction T with
  | leaf B h => exact h
  | split B i c hi l r hl hr =>
    intro q hq hD
    rcases B.mem_left_or_right hq i c with hq | hq
    · exact hl q hq hD
    · exact hr q hq hD

/-- Empty ordered intersections can be discarded with a proved contradiction. -/
def CheckedLogBoxTree.empty {D : Set EdgeTriple} {P : EdgeTriple → Prop} (B : LogBox)
    (h : Disjoint B.region D) : CheckedLogBoxTree D P B :=
  .leaf B (fun _ hB hD => False.elim (Set.disjoint_left.mp h hB hD))

/-- Number of leaves actually present in the proof tree. -/
def CheckedLogBoxTree.leafCount {D : Set EdgeTriple} {P : EdgeTriple → Prop} {B : LogBox} :
    CheckedLogBoxTree D P B → ℕ
  | .leaf _ _ => 1
  | .split _ _ _ _ l r => l.leafCount+r.leafCount

end SparseLowerTail.Section05

import SparseLowerTail.Section03.ConditionedProductEntropy
import Mathlib.Data.Bool.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Harris positive association as an explicit classical input; the paper's conditioning deductions. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

def finiteEventMass {α : Type*} (p : α → ℝ) (E : Finset α) : ℝ := ∑ z ∈ E, p z

def productBernoulliMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) : (ι → Bool) → ℝ := finiteProductMass (fun i => bernoulliMass (p i))

/-- The usual Harris theorem for two increasing events under an independent Bernoulli law.
This input contains no conditional probability or decreasing-event conclusion. -/
def ClassicalHarrisPositiveAssociation (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ p : ι → ℝ, (∀ i, p i ∈ Icc (0:ℝ) 1) →
    ∀ A B : Finset (ι → Bool), IsUpperSet (A : Set (ι → Bool)) →
      IsUpperSet (B : Set (ι → Bool)) →
      finiteEventMass (productBernoulliMass p) A * finiteEventMass (productBernoulliMass p) B ≤
        finiteEventMass (productBernoulliMass p) (A ∩ B)

theorem productBernoulliMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    ∑ z, productBernoulliMass p z=1 := finiteProductMass_sum _ (fun i => bernoulliMass_sum (p i))

theorem finiteEventMass_split {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (A L : Finset α) :
    finiteEventMass p (A∩L)+finiteEventMass p (A∩Lᶜ)=finiteEventMass p A := by
  simpa only [finiteEventMass, Finset.sdiff_eq_inter_compl] using A.sum_inter_add_sum_diff L p

theorem finiteConditionedMass_event {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (L A : Finset α) :
    finiteEventMass (finiteConditionedMass p L) A = finiteEventMass p (A∩L)/finiteEventMass p L := by
  simp only [finiteEventMass, finiteConditionedMass, Finset.sum_ite_mem]
  rw [← Finset.sum_div]
  apply congrArg (fun z : ℝ => z/(∑ a ∈ L, p a))
  apply Finset.sum_congr
  · ext z; simp
  · intro z _; rfl

/-- Harris for an increasing event and a decreasing event, derived by complementation. -/
theorem harris_increasing_decreasing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hHarris : ClassicalHarrisPositiveAssociation ι) (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Icc (0:ℝ) 1) (A L : Finset (ι → Bool))
    (hA : IsUpperSet (A : Set (ι → Bool))) (hL : IsLowerSet (L : Set (ι → Bool))) :
    finiteEventMass (productBernoulliMass p) (A∩L) ≤
      finiteEventMass (productBernoulliMass p) A * finiteEventMass (productBernoulliMass p) L := by
  classical
  have hLc : IsUpperSet ((Lᶜ : Finset (ι → Bool)) : Set (ι → Bool)) := by
    simpa only [Finset.coe_compl] using hL.compl
  have hh := hHarris p hp A Lᶜ hA hLc
  have hsplit := finiteEventMass_split (productBernoulliMass p) A L
  have hnorm := Finset.sum_add_sum_compl L (productBernoulliMass p)
  rw [productBernoulliMass_sum p] at hnorm
  change finiteEventMass (productBernoulliMass p) L+
    finiteEventMass (productBernoulliMass p) Lᶜ=1 at hnorm
  have hm := congrArg (fun z : ℝ => finiteEventMass (productBernoulliMass p) A*z) hnorm
  nlinarith

/-- Manuscript `lem:harris`(a): conditioning on a decreasing event suppresses every increasing event. -/
theorem harris_conditioned_event_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hHarris : ClassicalHarrisPositiveAssociation ι) (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Icc (0:ℝ) 1) (A L : Finset (ι → Bool))
    (hA : IsUpperSet (A : Set (ι → Bool))) (hL : IsLowerSet (L : Set (ι → Bool)))
    (hpos : 0 < finiteEventMass (productBernoulliMass p) L) :
    finiteEventMass (finiteConditionedMass (productBernoulliMass p) L) A ≤
      finiteEventMass (productBernoulliMass p) A := by
  classical
  rw [finiteConditionedMass_event]
  apply (div_le_iff₀ hpos).mpr
  exact harris_increasing_decreasing hHarris p hp A L hA hL

/-- The event that every coordinate in a specified finite set is present. -/
def allTrueEvent {ι : Type*} [Fintype ι] [DecidableEq ι] (κ : Finset ι) : Finset (ι → Bool) :=
  Fintype.piFinset (fun i => if i ∈ κ then {true} else Finset.univ)

theorem allTrueEvent_isUpperSet {ι : Type*} [Fintype ι] [DecidableEq ι] (κ : Finset ι) :
    IsUpperSet (allTrueEvent κ : Set (ι → Bool)) := by
  intro x y hxy hx
  change y ∈ allTrueEvent κ
  rw [allTrueEvent, Fintype.mem_piFinset]
  have hx' := Fintype.mem_piFinset.mp hx
  intro i
  by_cases hi : i ∈ κ
  · have hxi : x i=true := by simpa [hi] using hx' i
    have hle := hxy i
    rw [hxi] at hle
    have hyi : y i=true := by
      cases he : y i
      · rw [he] at hle
        exact False.elim ((by decide : ¬((true:Bool) ≤ false)) hle)
      · rfl
    simp [hi, hyi]
  · simp [hi]

theorem productBernoulliMass_allTrueEvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (κ : Finset ι) :
    finiteEventMass (productBernoulliMass p) (allTrueEvent κ) = ∏ i ∈ κ, p i := by
  classical
  unfold finiteEventMass productBernoulliMass finiteProductMass allTrueEvent
  rw [← Finset.prod_univ_sum]
  have he : ∀ i, (∑ b ∈ (if i ∈ κ then ({true} : Finset Bool) else Finset.univ),
      bernoulliMass (p i) b) = if i ∈ κ then p i else 1 := by
    intro i
    by_cases hi : i ∈ κ <;> simp [hi, bernoulliMass]
  simp_rw [he]
  simp

/-- The conditional pinned-coordinate bound in a decreasing section of a product space. -/
theorem harris_conditioned_allTrue_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hHarris : ClassicalHarrisPositiveAssociation ι) (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Icc (0:ℝ) 1) (κ : Finset ι) (L : Finset (ι → Bool))
    (hL : IsLowerSet (L : Set (ι → Bool)))
    (hpos : 0 < finiteEventMass (productBernoulliMass p) L) :
    finiteEventMass (finiteConditionedMass (productBernoulliMass p) L) (allTrueEvent κ) ≤
      ∏ i ∈ κ, p i := by
  simpa only [productBernoulliMass_allTrueEvent] using
    harris_conditioned_event_le hHarris p hp (allTrueEvent κ) L (allTrueEvent_isUpperSet κ) hL hpos

theorem harris_conditioned_allTrue_le_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hHarris : ClassicalHarrisPositiveAssociation ι) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1)
    (κ : Finset ι) (L : Finset (ι → Bool)) (hL : IsLowerSet (L : Set (ι → Bool)))
    (hpos : 0 < finiteEventMass (productBernoulliMass (fun _i : ι => p)) L) :
    finiteEventMass (finiteConditionedMass (productBernoulliMass (fun _i : ι => p)) L)
      (allTrueEvent κ) ≤ p^κ.card := by
  simpa using harris_conditioned_allTrue_le hHarris (fun _i : ι => p) (fun _i => hp) κ L hL hpos

/-- Section of an event after revealing its first coordinate. -/
def finiteEventSection {α β : Type*} [Fintype β] (L : Finset (α×β)) (y : α) : Finset β := by
  classical
  exact Finset.univ.filter (fun z => (y,z) ∈ L)

@[simp] theorem mem_finiteEventSection {α β : Type*} [Fintype β]
    (L : Finset (α×β)) (y : α) (z : β) : z ∈ finiteEventSection L y ↔ (y,z) ∈ L := by
  classical
  simp [finiteEventSection]

theorem finiteEventSection_isLowerSet {α β : Type*} [Preorder α] [Preorder β] [Fintype β]
    (L : Finset (α×β)) (hL : IsLowerSet (L : Set (α×β))) (y : α) :
    IsLowerSet (finiteEventSection L y : Set β) := by
  intro a b hab hb
  change b ∈ finiteEventSection L y
  apply (mem_finiteEventSection L y b).mpr
  exact hL (show (y,b) ≤ (y,a) from ⟨le_rfl,hab⟩) ((mem_finiteEventSection L y a).mp hb)

/-- Joint mass obtained by conditioning a product reference, with a revealed first coordinate. -/
def conditionedProductJoint {α β : Type*} [Fintype α] [Fintype β]
    (py : α → ℝ) (pz : β → ℝ) (L : Finset (α×β)) (y : α) (z : β) : ℝ :=
  finiteConditionedMass (fun yz : α×β => py yz.1*pz yz.2) L (y,z)

theorem conditionedProductJoint_row {α β : Type*} [Fintype α] [Fintype β]
    (py : α → ℝ) (pz : β → ℝ) (L : Finset (α×β)) (y : α) :
    finiteRowMass (conditionedProductJoint py pz L) y =
      (py y/finiteEventMass (fun yz : α×β => py yz.1*pz yz.2) L)*
        finiteEventMass pz (finiteEventSection L y) := by
  classical
  have he : ∀ z, conditionedProductJoint py pz L y z =
      (py y/finiteEventMass (fun yz : α×β => py yz.1*pz yz.2) L)*
        (if z ∈ finiteEventSection L y then pz z else 0) := by
    intro z
    by_cases hz : (y,z) ∈ L
    · simp only [conditionedProductJoint, finiteConditionedMass, if_pos hz,
        mem_finiteEventSection, finiteEventMass]
      ring
    · simp [conditionedProductJoint, finiteConditionedMass, hz]
  unfold finiteRowMass
  simp_rw [he]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, finiteEventMass]

theorem conditionedProductJoint_section_pos {α β : Type*} [Fintype α] [Fintype β]
    (py : α → ℝ) (pz : β → ℝ) (L : Finset (α×β)) (y : α) (hpy : 0 < py y)
    (hL : 0 < finiteEventMass (fun yz : α×β => py yz.1*pz yz.2) L)
    (hy : 0 < finiteRowMass (conditionedProductJoint py pz L) y) :
    0 < finiteEventMass pz (finiteEventSection L y) := by
  rw [conditionedProductJoint_row] at hy
  exact (mul_pos_iff_of_pos_left (div_pos hpy hL)).mp hy

/-- The unrevealed coordinates are the original product law conditioned on the revealed section. -/
theorem finiteConditional_conditionedProductJoint {α β : Type*} [Fintype α] [Fintype β]
    (py : α → ℝ) (pz : β → ℝ) (L : Finset (α×β)) (y : α) (hpy : 0 < py y)
    (hL : 0 < finiteEventMass (fun yz : α×β => py yz.1*pz yz.2) L)
    (hy : 0 < finiteRowMass (conditionedProductJoint py pz L) y) :
    finiteConditional (conditionedProductJoint py pz L) y =
      finiteConditionedMass pz (finiteEventSection L y) := by
  classical
  have hs := conditionedProductJoint_section_pos py pz L y hpy hL hy
  funext z
  unfold finiteConditional
  rw [conditionedProductJoint_row]
  by_cases hz : (y,z) ∈ L
  · simp only [conditionedProductJoint, finiteConditionedMass, if_pos hz, mem_finiteEventSection]
    change (py y*pz z/finiteEventMass (fun yz : α×β => py yz.1*pz yz.2) L)/
        ((py y/finiteEventMass (fun yz : α×β => py yz.1*pz yz.2) L)*
          finiteEventMass pz (finiteEventSection L y)) = pz z/finiteEventMass pz (finiteEventSection L y)
    field_simp [hpy.ne', hL.ne', hs.ne']
  · simp [conditionedProductJoint, finiteConditionedMass, hz]

/-- Manuscript `lem:harris`(b): revealing coordinates preserves the bound on a pinned-edge event. -/
theorem harris_revealed_allTrue_le_pow {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (hHarris : ClassicalHarrisPositiveAssociation ι) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1)
    (py : α → ℝ) (L : Finset (α×(ι → Bool))) (y : α) (κ : Finset ι) (hpy : 0 < py y)
    (hL : IsLowerSet (finiteEventSection L y : Set (ι → Bool)))
    (hpos : 0 < finiteEventMass (fun yz : α×(ι → Bool) =>
      py yz.1*productBernoulliMass (fun _i : ι => p) yz.2) L)
    (hy : 0 < finiteRowMass (conditionedProductJoint py
      (productBernoulliMass (fun _i : ι => p)) L) y) :
    finiteEventMass (finiteConditional (conditionedProductJoint py
      (productBernoulliMass (fun _i : ι => p)) L) y) (allTrueEvent κ) ≤ p^κ.card := by
  rw [finiteConditional_conditionedProductJoint py _ L y hpy hpos hy]
  exact harris_conditioned_allTrue_le_pow hHarris hp κ (finiteEventSection L y) hL
    (conditionedProductJoint_section_pos py _ L y hpy hpos hy)

/-- Number of hyperedges present in a finite Boolean configuration; triangles are a special case. -/
def finiteHypergraphCount {ι : Type*} (H : Finset (Finset ι)) (z : ι → Bool) : ℕ :=
  ∑ κ ∈ H, ∏ i ∈ κ, (z i).toNat

theorem finiteHypergraphCount_monotone {ι : Type*} (H : Finset (Finset ι)) :
    Monotone (finiteHypergraphCount H) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro κ _
  exact Finset.prod_le_prod' (fun i _ => Bool.toNat_le_toNat (hxy i))

def finiteHypergraphLowerEvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Finset (Finset ι)) (t : ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter (fun z => finiteHypergraphCount H z ≤ t)

theorem finiteHypergraphLowerEvent_isLowerSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Finset (Finset ι)) (t : ℕ) :
    IsLowerSet (finiteHypergraphLowerEvent H t : Set (ι → Bool)) := by
  classical
  intro x y hyx hx
  change y ∈ finiteHypergraphLowerEvent H t
  have hx' : finiteHypergraphCount H x ≤ t := by simpa [finiteHypergraphLowerEvent] using hx
  have hy := (finiteHypergraphCount_monotone H hyx).trans hx'
  simpa [finiteHypergraphLowerEvent] using hy

/-- A lower-tail event written in revealed and unrevealed coordinates. -/
def jointHypergraphLowerEvent {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (H : Finset (Finset (α⊕ι))) (t : ℕ) :
    Finset ((α → Bool)×(ι → Bool)) := by
  classical
  exact Finset.univ.filter (fun yz => finiteHypergraphCount H (Sum.elim yz.1 yz.2) ≤ t)

theorem jointHypergraphLowerEvent_isLowerSet {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (H : Finset (Finset (α⊕ι))) (t : ℕ) :
    IsLowerSet (jointHypergraphLowerEvent H t : Set ((α → Bool)×(ι → Bool))) := by
  classical
  intro x y hyx hx
  change y ∈ jointHypergraphLowerEvent H t
  have hx' : finiteHypergraphCount H (Sum.elim x.1 x.2) ≤ t := by
    simpa [jointHypergraphLowerEvent] using hx
  have hmerge : Sum.elim y.1 y.2 ≤ Sum.elim x.1 x.2 := by
    intro i
    cases i with
    | inl i => exact hyx.1 i
    | inr i => exact hyx.2 i
  have hy := (finiteHypergraphCount_monotone H hmerge).trans hx'
  simpa [jointHypergraphLowerEvent] using hy

theorem hypergraph_lower_section_isLowerSet {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (H : Finset (Finset (α⊕ι))) (t : ℕ) (y : α → Bool) :
    IsLowerSet (finiteEventSection (jointHypergraphLowerEvent H t) y : Set (ι → Bool)) :=
  finiteEventSection_isLowerSet _ (jointHypergraphLowerEvent_isLowerSet H t) y

end SparseLowerTail.Section03

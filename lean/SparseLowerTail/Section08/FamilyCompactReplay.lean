import SparseLowerTail.Section08.FamilyCompactAssembly
import SparseLowerTail.Section08.FamilyExteriorLeaf
import SparseLowerTail.Numerics.BoxReplayTable

/-! Formal replay interface for the ordered compact-family subdivision.
Taylor, contact, and ordered-empty leaves share one zero-preserving conclusion.
The complete numerical table and tree remain separate proof obligations. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Numerics Section04 Set

def familyCompactCoordinates (z : ℝ) (q : FamilyVector) : Fin 4 → ℝ :=
  ![branchLog z,q 0,q 1,q 2]

def familyCompactProperty (x : Fin 4 → ℝ) : Prop :=
  ∀z : ℝ,0<z → Bounds (branchLog z) (39/10) (19/2) →
    ∀q : FamilyVector,x=familyCompactCoordinates z q → q 2≤q 1 → q 1≤q 0 →
      FamilyLeafConclusion z q

namespace FamilyExteriorLeaf

def Encloses (C : FamilyExteriorLeaf) (B : ReplayBox 4) : Prop :=
  C.data.whole.logLower.q≤B.lower 0 ∧ B.upper 0≤C.data.whole.logUpper.q ∧
    ∀i,(C.box.qLower i).q≤B.lower i.succ ∧ B.upper i.succ≤(C.box.qUpper i).q

instance (C : FamilyExteriorLeaf) (B : ReplayBox 4) : Decidable (C.Encloses B) :=
  inferInstanceAs (Decidable (C.data.whole.logLower.q≤B.lower 0 ∧
    B.upper 0≤C.data.whole.logUpper.q ∧
      ∀i,(C.box.qLower i).q≤B.lower i.succ ∧ B.upper i.succ≤(C.box.qUpper i).q))

theorem compact_property (C : FamilyExteriorLeaf) (hC : C.Valid)
    {B : ReplayBox 4} (hB : C.Encloses B) : ∀x,B.Contains x → familyCompactProperty x := by
  intro x hx z hz _ q he _ _
  rw [he] at hx
  have hp := C.positive hC (t := branchLog z)
    (show Bounds (branchLog z) (C.data.whole.logLower.q : ℝ) (C.data.whole.logUpper.q : ℝ) from
      ⟨(show (C.data.whole.logLower.q : ℝ)≤(B.lower 0 : ℝ) by exact_mod_cast hB.1).trans (hx 0).1,
       (hx 0).2.trans (by exact_mod_cast hB.2.1)⟩)
    (q := q) (fun i => by
      have hi : Bounds (q i) (B.lower i.succ : ℝ) (B.upper i.succ : ℝ) := by
        have h := hx i.succ
        fin_cases i <;> exact h
      exact ⟨(show ((C.box.qLower i).q : ℝ)≤(B.lower i.succ : ℝ) by exact_mod_cast (hB.2.2 i).1).trans hi.1,
        hi.2.trans (by exact_mod_cast (hB.2.2 i).2)⟩)
  rw [branchLog_eq_neg_log,neg_neg,Real.exp_log hz] at hp
  exact familyLeafConclusion_of_positive hp

end FamilyExteriorLeaf

theorem familyCompactProperty_ordered_empty (B : ReplayBox 4)
    (hempty : B.upper 1<B.lower 2 ∨ B.upper 2<B.lower 3) :
    ∀x,B.Contains x → familyCompactProperty x := by
  intro x hx z _ _ q he hs21 hs10
  rw [he] at hx
  have hu0 : q 0≤(B.upper 1 : ℝ) := (hx 1).2
  have hl1 : (B.lower 2 : ℝ)≤q 1 := (hx 2).1
  have hu1 : q 1≤(B.upper 2 : ℝ) := (hx 2).2
  have hl2 : (B.lower 3 : ℝ)≤q 2 := (hx 3).1
  exfalso
  rcases hempty with h | h
  · have hh : (B.upper 1 : ℝ)<(B.lower 2 : ℝ) := by exact_mod_cast h
    linarith
  · have hh : (B.upper 2 : ℝ)<(B.lower 3 : ℝ) := by exact_mod_cast h
    linarith

namespace FamilyParameterCertificate

def contactLowerValue (C : FamilyParameterCertificate) (mixed : Bool) (i : Fin 3) : ℚ :=
  (if mixed then (if i=0 then C.logLower.q else 0) else C.logLower.q)+C.deltaLower.q
def contactUpperValue (C : FamilyParameterCertificate) (mixed : Bool) (i : Fin 3) : ℚ :=
  (if mixed then (if i=0 then C.logUpper.q else 0) else C.logUpper.q)+C.deltaUpper.q

theorem contact_interval (C : FamilyParameterCertificate) (hC : C.Valid)
    {z : ℝ} (hz : 0<z) (hz1 : z<1)
    (hL : Bounds (branchLog z) (C.logLower.q : ℝ) (C.logUpper.q : ℝ))
    (mixed : Bool) (i : Fin 3) :
    Bounds (familyContact mixed z i) (C.contactLowerValue mixed i : ℝ)
      (C.contactUpperValue mixed i : ℝ) := by
  have hd := C.delta_endpoint_bounds hC hz hL
  have ha := qA_eq_add hz hz1
  rw [show 2*branchLog z*z=2*z*branchLog z by ring] at ha
  have hqa : Bounds (qA z) ((C.logLower.q+C.deltaLower.q : ℚ) : ℝ)
      ((C.logUpper.q+C.deltaUpper.q : ℚ) : ℝ) := by
    push_cast
    rw [ha]
    exact hL.add hd
  have hb : -Real.log (branchB z)=2*z*branchLog z/(1-z)^2 := by
    rw [branchB,Real.log_exp]
    ring
  have hqb : Bounds (-Real.log (branchB z)) (C.deltaLower.q : ℝ) (C.deltaUpper.q : ℝ) := by
    rw [hb]
    exact hd
  cases mixed <;> fin_cases i
  all_goals first
    | simpa [contactLowerValue,contactUpperValue,familyContact,familyContactAAA,familyContactABB] using hqa
    | simpa [contactLowerValue,contactUpperValue,familyContact,familyContactAAA,familyContactABB] using hqb

/-- The q box must lie inside every moving contact cube, so the upper
contact endpoint constrains its lower side, and conversely. -/
def InContact (C : FamilyParameterCertificate) (mixed : Bool) (B : ReplayBox 4) : Prop :=
  C.logLower.q≤B.lower 0 ∧ B.upper 0≤C.logUpper.q ∧
    ∀i,C.contactUpperValue mixed i-1/10≤B.lower i.succ ∧
      B.upper i.succ≤C.contactLowerValue mixed i+1/10

instance (C : FamilyParameterCertificate) (mixed : Bool) (B : ReplayBox 4) :
    Decidable (C.InContact mixed B) := inferInstanceAs (Decidable (
      C.logLower.q≤B.lower 0 ∧ B.upper 0≤C.logUpper.q ∧
      ∀i,C.contactUpperValue mixed i-1/10≤B.lower i.succ ∧
        B.upper i.succ≤C.contactLowerValue mixed i+1/10))

theorem compact_property_of_contact (hABB : FamilyABBLocal)
    (C : FamilyParameterCertificate) (hC : C.Valid) (mixed : Bool)
    {B : ReplayBox 4} (hB : C.InContact mixed B) :
    ∀x,B.Contains x → familyCompactProperty x := by
  intro x hx z hz hL q he _ _
  rw [he] at hx
  have hz1 : z<1 := by linarith [family_parameter_lt_one_fortieth hz hL.1]
  have hcL : Bounds (branchLog z) (C.logLower.q : ℝ) (C.logUpper.q : ℝ) :=
    ⟨(show (C.logLower.q : ℝ)≤(B.lower 0 : ℝ) by exact_mod_cast hB.1).trans (hx 0).1,
      (hx 0).2.trans (by exact_mod_cast hB.2.1)⟩
  apply familyLeafConclusion_of_contact hABB hz hL mixed
  intro i
  have hc := C.contact_interval hC hz hz1 hcL mixed i
  have hi : Bounds (q i) (B.lower i.succ : ℝ) (B.upper i.succ : ℝ) := by
    have hh := hx i.succ
    fin_cases i <;> exact hh
  have hl : (C.contactUpperValue mixed i : ℝ)-1/10≤(B.lower i.succ : ℝ) :=
    by
      have hh : ((C.contactUpperValue mixed i-1/10 : ℚ) : ℝ)≤(B.lower i.succ : ℝ) :=
        Rat.cast_le.mpr (hB.2.2 i).1
      norm_num at hh
      linarith
  have hu : (B.upper i.succ : ℝ)≤(C.contactLowerValue mixed i : ℝ)+1/10 :=
    by
      have hh : (B.upper i.succ : ℝ)≤((C.contactLowerValue mixed i+1/10 : ℚ) : ℝ) :=
        Rat.cast_le.mpr (hB.2.2 i).2
      norm_num at hh
      exact hh
  apply abs_le.mpr
  constructor <;> linarith [hc.1,hc.2,hi.1,hi.2]

end FamilyParameterCertificate

def familyCompactInitialBox : ReplayBox 4 := ⟨![39/10,0,0,0],![19/2,12,12,12]⟩

/-- Exactly the main theorem's remaining compact-family obligation, once
every leaf and every split of the full table has been checked. -/
theorem compactFamilyCertificate_of_table (table : RegisterTree (Option (ReplayBox 4)))
    (tree : BoxReplay 4) (htree : tree.Valid table.get familyCompactInitialBox)
    (hleaf : table.All (ReplayBoxProperty familyCompactProperty)) :
    Section08.CompactFamilyCertificate := by
  apply compactFamilyCertificate_of_ordered
  intro z hz hL q hq hs21 hs10
  have hx : familyCompactInitialBox.Contains (familyCompactCoordinates z q) := by
    intro i
    fin_cases i
    · simpa [familyCompactInitialBox,familyCompactCoordinates] using hL
    · simpa [familyCompactInitialBox,familyCompactCoordinates] using hq 0
    · simpa [familyCompactInitialBox,familyCompactCoordinates] using hq 1
    · simpa [familyCompactInitialBox,familyCompactCoordinates] using hq 2
  exact BoxReplay.sound_table hleaf tree htree _ hx z hz hL q rfl hs21 hs10

end SparseLowerTail.Certificate

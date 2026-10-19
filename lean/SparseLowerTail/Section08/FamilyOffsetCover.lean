import SparseLowerTail.Numerics.BoxReplayTable
import SparseLowerTail.Section08.FamilyScaledIntervals
import SparseLowerTail.Section08.FamilyAAACover

/-! Four-dimensional replay around the moving ABB contact. A table leaf must
prove both its rational enclosure and its Hessian margins. Coverage is a
separate checked subdivision, never inferred from a list of accepted boxes. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Numerics Section04

def familyABBOffsetCoordinates (z : ℝ) (q : FamilyVector) : Fin 4 → ℝ :=
  ![branchLog z,q 0-familyContactABB z 0,q 1-familyContactABB z 1,
    q 2-familyContactABB z 2]

namespace FamilyBoxCertificate

def contactLower (C : FamilyBoxCertificate) (i : Fin 3) : ℚ :=
  (if i=0 then C.parameter.logLower.q else 0)+C.parameter.deltaLower.q
def contactUpper (C : FamilyBoxCertificate) (i : Fin 3) : ℚ :=
  (if i=0 then C.parameter.logUpper.q else 0)+C.parameter.deltaUpper.q

theorem contact_bounds (C : FamilyBoxCertificate) (hC : C.Valid)
    {z : ℝ} (hz : 0<z) (hz1 : z<1)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ)
      (C.parameter.logUpper.q : ℝ)) (i : Fin 3) :
    Bounds (familyContactABB z i) (C.contactLower i : ℝ) (C.contactUpper i : ℝ) := by
  have hd := C.parameter.delta_endpoint_bounds hC.1 hz hL
  have ha := qA_eq_add hz hz1
  rw [show 2*branchLog z*z=2*z*branchLog z by ring] at ha
  have hb : -Real.log (branchB z)=2*z*branchLog z/(1-z)^2 := by
    rw [branchB,Real.log_exp]
    ring
  fin_cases i
  · change Bounds (qA z) ((C.parameter.logLower.q+C.parameter.deltaLower.q : ℚ) : ℝ)
      ((C.parameter.logUpper.q+C.parameter.deltaUpper.q : ℚ) : ℝ)
    push_cast
    constructor <;> linarith [hd.1,hd.2,hL.1,hL.2,ha]
  · change Bounds (-Real.log (branchB z)) ((0+C.parameter.deltaLower.q : ℚ) : ℝ)
      ((0+C.parameter.deltaUpper.q : ℚ) : ℝ)
    simpa only [hb,zero_add] using hd
  · change Bounds (-Real.log (branchB z)) ((0+C.parameter.deltaLower.q : ℚ) : ℝ)
      ((0+C.parameter.deltaUpper.q : ℚ) : ℝ)
    simpa only [hb,zero_add] using hd

def EnclosesABBOffsets (C : FamilyBoxCertificate) (B : ReplayBox 4) : Prop :=
  C.parameter.logLower.q=B.lower 0 ∧ C.parameter.logUpper.q=B.upper 0 ∧
    ∀i,(C.qLower i).q≤C.contactLower i+B.lower i.succ ∧
      C.contactUpper i+B.upper i.succ≤(C.qUpper i).q

instance (C : FamilyBoxCertificate) (B : ReplayBox 4) : Decidable (C.EnclosesABBOffsets B) :=
  inferInstanceAs (Decidable (C.parameter.logLower.q=B.lower 0 ∧
    C.parameter.logUpper.q=B.upper 0 ∧
    ∀i,(C.qLower i).q≤C.contactLower i+B.lower i.succ ∧
      C.contactUpper i+B.upper i.succ≤(C.qUpper i).q))

theorem bounds_of_offsets (C : FamilyBoxCertificate) (hC : C.Valid)
    {B : ReplayBox 4} (hB : C.EnclosesABBOffsets B)
    {z : ℝ} (hz : 0<z) (hz1 : z<1) {q : FamilyVector}
    (hq : B.Contains (familyABBOffsetCoordinates z q)) :
    Bounds (branchLog z) (C.parameter.logLower.q : ℝ) (C.parameter.logUpper.q : ℝ) ∧
    ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ) := by
  have hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ)
      (C.parameter.logUpper.q : ℝ) := by
    simpa only [hB.1,hB.2.1,familyABBOffsetCoordinates,Matrix.cons_val_zero] using hq 0
  refine ⟨hL,?_⟩
  intro i
  have hc := C.contact_bounds hC hz hz1 hL i
  have ho : Bounds (q i-familyContactABB z i) (B.lower i.succ : ℝ) (B.upper i.succ : ℝ) := by
    have hh := hq i.succ
    fin_cases i <;> exact hh
  have hl : ((C.qLower i).q : ℝ)≤(C.contactLower i : ℝ)+(B.lower i.succ : ℝ) :=
    by exact_mod_cast (hB.2.2 i).1
  have hu : (C.contactUpper i : ℝ)+(B.upper i.succ : ℝ)≤((C.qUpper i).q : ℝ) :=
    by exact_mod_cast (hB.2.2 i).2
  constructor <;> linarith [hc.1,hc.2,ho.1,ho.2]

end FamilyBoxCertificate

theorem FamilyScaledBoxCertificate.abb_offset_hessian_positive
    (C : FamilyScaledBoxCertificate) (hC : C.Valid)
    (T : FamilyRationalMatrix)
    (hpos : FamilyIntervalPositive (familyIntervalCongruence C.hessianIntervals T))
    {B : ReplayBox 4} (hB : C.box.EnclosesABBOffsets B)
    {z : ℝ} (hz : 0<z) (hz1 : z<1) {q : FamilyVector}
    (hq : B.Contains (familyABBOffsetCoordinates z q))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  obtain ⟨hL,hbox⟩ := C.box.bounds_of_offsets hC.1 hB hz hz1 hq
  exact C.hessian_positive hC T hpos hz hL hbox hv

def familyABBInitialBox : ReplayBox 4 :=
  ⟨![39/10,-1/10,-1/10,-1/10],![19/2,1/10,1/10,1/10]⟩

theorem familyABBInitialBox_contains {z : ℝ} {q : FamilyVector}
    (hL : Bounds (branchLog z) (39/10) (19/2))
    (hq : q∈familyCube (familyContactABB z) (1/10)) :
    familyABBInitialBox.Contains (familyABBOffsetCoordinates z q) := by
  intro i
  fin_cases i
  · simpa [familyABBInitialBox,familyABBOffsetCoordinates] using hL
  · change Bounds (q 0-familyContactABB z 0) (((-1)/10 : ℚ) : ℝ) ((1/10 : ℚ) : ℝ)
    norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat]
    exact abs_le.mp (hq 0)
  · change Bounds (q 1-familyContactABB z 1) (((-1)/10 : ℚ) : ℝ) ((1/10 : ℚ) : ℝ)
    norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat]
    exact abs_le.mp (hq 1)
  · change Bounds (q 2-familyContactABB z 2) (((-1)/10 : ℚ) : ℝ) ((1/10 : ℚ) : ℝ)
    norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat]
    exact abs_le.mp (hq 2)

/-- This assembly becomes unconditional only after the full leaf table and
its four-dimensional coverage tree have been checked. -/
theorem familyABB_local_of_replay (table : ℕ → Option (ReplayBox 4))
    (tree : BoxReplay 4) (htree : tree.Valid table familyABBInitialBox)
    (hleaf : ∀i B,table i=some B → ∀z : ℝ,0<z → z<1 → ∀q : FamilyVector,
      B.Contains (familyABBOffsetCoordinates z q) → ∀v : FamilyVector,
      v≠0 → 0<familyHessianForm z q v)
    {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z) (1/10)) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) := by
  have hz40 := FamilyAAACover.z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  apply familyContactABB_local hz hz1 (gamma_branch_neg hz hz40).ne (by norm_num) _ hq
  intro q' hq' v hv
  let P : (Fin 4 → ℝ) → Prop := fun x =>
    ∀q' : FamilyVector,x=familyABBOffsetCoordinates z q' → 0<familyHessianForm z q' v
  have ht : ∀x,familyABBInitialBox.Contains x → P x := by
    refine BoxReplay.sound (P := P) ?_ tree htree
    intro i B hi x hx q' he
    exact hleaf i B hi z hz hz1 q' (he ▸ hx) v hv
  exact ht _ (familyABBInitialBox_contains hL hq') q' rfl

/-- Uniform leaf conclusion, expressed as a predicate on the four coordinates
so that checked subtrees can be reused as leaves of the final tree. -/
def familyABBOffsetProperty (x : Fin 4 → ℝ) : Prop :=
  ∀z : ℝ,0<z → z<1 → ∀q : FamilyVector,x=familyABBOffsetCoordinates z q →
    ∀v : FamilyVector,v≠0 → 0<familyHessianForm z q v

theorem FamilyScaledBoxCertificate.abb_offset_property
    (C : FamilyScaledBoxCertificate) (hC : C.Valid) (T : FamilyRationalMatrix)
    (hpos : FamilyIntervalPositive (familyIntervalCongruence C.hessianIntervals T))
    {B : ReplayBox 4} (hB : C.box.EnclosesABBOffsets B) :
    ∀x,B.Contains x → familyABBOffsetProperty x := by
  intro x hx z hz hz1 q he v hv
  exact C.abb_offset_hessian_positive hC T hpos hB hz hz1 (he ▸ hx) hv

theorem familyABB_local_of_table (table : RegisterTree (Option (ReplayBox 4)))
    (tree : BoxReplay 4) (htree : tree.Valid table.get familyABBInitialBox)
    (hleaf : table.All (ReplayBoxProperty familyABBOffsetProperty))
    {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z) (1/10)) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) := by
  apply familyABB_local_of_replay table.get tree htree _ hz hL hq
  intro i B hi z hz hz1 q hq v hv
  have hh := hleaf.get i
  rw [hi] at hh
  exact hh _ hq z hz hz1 q rfl v hv

end SparseLowerTail.Certificate

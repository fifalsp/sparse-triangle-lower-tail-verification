import SparseLowerTail.Section08.FamilyHessianPerturbation
import SparseLowerTail.Section08.ManuscriptFamilyRadius
import SparseLowerTail.Section08.FamilyOffsetCover

/-! A checked radius extension using a retraction to the old cube and a small
outward padding of the existing scaled-Hessian intervals. -/
noncomputable section
namespace SparseLowerTail.Certificate.HessianRadiusTransfer
open Numerics Section04 Set ManuscriptFamilyRadius HessianPerturbation

/-- Shrink the exact binary64 cube to the rational one-tenth cube. -/
def retract (c q : FamilyVector) : FamilyVector :=
  fun i => c i+(q i-c i)*(18014398509481984/18014398509481985)

theorem retract_in_cube {c q : FamilyVector}
    (hq : q∈familyCube c binary64Radius) : retract c q∈familyCube c (1/10) := by
  intro i
  have he : retract c q i-c i=(q i-c i)*(18014398509481984/18014398509481985) := by
    unfold retract
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤18014398509481984/18014398509481985)]
  have h := mul_le_mul_of_nonneg_right (hq i)
    (by norm_num : (0:ℝ)≤18014398509481984/18014398509481985)
  exact h.trans_eq (by norm_num [binary64Radius])

theorem retract_change {c q : FamilyVector}
    (hq : q∈familyCube c binary64Radius) (i : Fin 3) :
    |q i-retract c q i| ≤ 1/180143985094819840 := by
  have he : q i-retract c q i=(q i-c i)*(1/18014398509481985) := by
    unfold retract
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/18014398509481985)]
  have h := mul_le_mul_of_nonneg_right (hq i)
    (by norm_num : (0:ℝ)≤1/18014398509481985)
  exact h.trans_eq (by norm_num [binary64Radius])

theorem cube_in_analytic_box {c q : FamilyVector}
    (hc : ∀i,c i∈Icc (0:ℝ) 10) (hq : q∈familyCube c binary64Radius) :
    ∀i,q i∈Icc (-1:ℝ) 11 := by
  intro i
  have h := abs_le.mp (hq i)
  have hr : binary64Radius≤1 := by norm_num [binary64Radius]
  exact ⟨by linarith [(hc i).1],by linarith [(hc i).2]⟩

theorem retract_in_analytic_box {c q : FamilyVector}
    (hc : ∀i,c i∈Icc (0:ℝ) 10) (hq : q∈familyCube c binary64Radius) :
    ∀i,retract c q i∈Icc (-1:ℝ) 11 := by
  intro i
  have h := abs_le.mp (retract_in_cube hq i)
  exact ⟨by linarith [(hc i).1],by linarith [(hc i).2]⟩

/-- Integer padding of 2^30 dyadic units equals 2^-30 in real units. -/
def padded (I : DyadicInterval) : DyadicInterval :=
  ⟨I.lower-2^30,I.upper+2^30⟩

theorem padded_contains {I : DyadicInterval} {x y : ℝ}
    (hx : I.contains x) (hd : |y-x|≤(2^30:ℝ)/DyadicInterval.scale) :
    (padded I).contains y := by
  have hh := abs_le.mp hd
  change (I.lower:ℝ)/DyadicInterval.scale≤x ∧
    x≤(I.upper:ℝ)/DyadicInterval.scale at hx
  change ((I.lower-2^30:ℤ):ℝ)/DyadicInterval.scale≤y ∧
    y≤((I.upper+2^30:ℤ):ℝ)/DyadicInterval.scale
  push_cast
  rw [sub_div,add_div]
  constructor <;> linarith [hx.1,hx.2,hh.1,hh.2]

def paddedMatrix (H : FamilyIntervalMatrix) : FamilyIntervalMatrix :=
  fun i j => padded (H i j)

/-- Existing interval enclosures can be reused after retraction; the analytic
perturbation fits inside the explicit dyadic padding. -/
theorem padded_hessian_contains {z : ℝ} {c q : FamilyVector}
    (hc : ∀i,c i∈Icc (0:ℝ) 10) (hz : CoefficientBounds z)
    (hq : q∈familyCube c binary64Radius) {H : FamilyIntervalMatrix}
    (hH : ∀i j,(H i j).contains (familyHessianScaled z (retract c q) i j)) :
    ∀i j,(paddedMatrix H i j).contains (familyHessianScaled z q i j) := by
  intro i j
  apply padded_contains (hH i j)
  have h := scaled_hessian_change (by norm_num : (0:ℝ)≤1/180143985094819840)
    hz (cube_in_analytic_box hc hq) (retract_in_analytic_box hc hq)
    (retract_change hq) i j
  exact h.trans (by norm_num [DyadicInterval.scale])

/-- The larger-cube conclusion requires newly checked integer margins of the
padded matrix. It does not reuse positivity of an unpadded enclosure. -/
theorem hessian_positive_of_retracted_enclosure {z : ℝ} {c q : FamilyVector}
    (hc : ∀i,c i∈Icc (0:ℝ) 10) (hz : CoefficientBounds z)
    (hq : q∈familyCube c binary64Radius) (H : FamilyIntervalMatrix)
    (T : FamilyRationalMatrix)
    (hH : ∀i j,(H i j).contains (familyHessianScaled z (retract c q) i j))
    (hm : FamilyIntervalPositive (familyIntervalCongruence (paddedMatrix H) T))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  familyHessian_pos_of_interval_congruence (paddedMatrix H) T
    (padded_hessian_contains hc hz hq hH) hm hv

/-- An integer condition on the stored coefficient endpoints. -/
def SmallCoefficient (I : DyadicInterval) : Prop :=
  -1000*DyadicInterval.scale≤I.lower ∧ I.upper≤1000*DyadicInterval.scale

instance (I : DyadicInterval) : Decidable (SmallCoefficient I) :=
  inferInstanceAs (Decidable (-1000*DyadicInterval.scale≤I.lower ∧
    I.upper≤1000*DyadicInterval.scale))

theorem small_coefficient_sound {I : DyadicInterval} {x : ℝ}
    (hI : SmallCoefficient I) (hx : I.contains x) : |x|≤1000 := by
  have hl : (-1000:ℝ)*DyadicInterval.scale≤I.lower := by exact_mod_cast hI.1
  have hu : (I.upper:ℝ)≤1000*DyadicInterval.scale := by exact_mod_cast hI.2
  have hlo := div_le_div_of_nonneg_right hl DyadicInterval.scale_real_pos.le
  have hup := div_le_div_of_nonneg_right hu DyadicInterval.scale_real_pos.le
  rw [mul_div_cancel_right₀ _ DyadicInterval.scale_real_pos.ne'] at hlo hup
  exact abs_le.mpr ⟨hlo.trans hx.1,hx.2.trans hup⟩

theorem coefficient_bounds_of_certificate (C : FamilyBoxCertificate) (hC : C.Valid)
    (hs : ∀i,SmallCoefficient (C.coefficient i)) {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ)
      (C.parameter.logUpper.q : ℝ)) : CoefficientBounds z := by
  have hc (i : Fin 7) := small_coefficient_sound (hs i)
    (C.parameter.coefficient_contains hC.1 hz hL i (hC.2.1 i))
  exact ⟨hc 1,hc 2,hc 4,hc 5,hc 6⟩

/-- Rational endpoint bounds on the moving contact. -/
def BoundedContact (C : FamilyBoxCertificate) : Prop :=
  ∀i,0≤C.contactLower i ∧ C.contactUpper i≤10

instance (C : FamilyBoxCertificate) : Decidable (BoundedContact C) :=
  inferInstanceAs (Decidable (∀i,0≤C.contactLower i ∧ C.contactUpper i≤10))

theorem bounded_contact_sound (C : FamilyBoxCertificate) (hC : C.Valid)
    (hb : BoundedContact C) {z : ℝ} (hz : 0<z) (hz1 : z<1)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ)
      (C.parameter.logUpper.q : ℝ)) :
    ∀i,familyContactABB z i∈Icc (0:ℝ) 10 := by
  intro i
  have hc := C.contact_bounds hC hz hz1 hL i
  have hl : (0:ℝ)≤C.contactLower i := by exact_mod_cast (hb i).1
  have hu : (C.contactUpper i:ℝ)≤10 := by exact_mod_cast (hb i).2
  exact ⟨hl.trans hc.1,hc.2.trans hu⟩

/-- The predicate propagated through the unchanged rational-radius tree. -/
def RadiusABBOffsetProperty (x : Fin 4→ℝ) : Prop :=
  ∀z : ℝ,0<z → z<1 → ∀q : FamilyVector,
    q∈familyCube (familyContactABB z) binary64Radius →
    x=familyABBOffsetCoordinates z (retract (familyContactABB z) q) →
    ∀v : FamilyVector,v≠0 → 0<familyHessianForm z q v

/-- Leaf adapter: the old enclosure is used at the retracted point. All new
leaf obligations are finite integer or rational arithmetic. -/
theorem abb_radius_offset_property (C : FamilyScaledBoxCertificate) (hC : C.Valid)
    (T : FamilyRationalMatrix)
    (hm : FamilyIntervalPositive (familyIntervalCongruence (paddedMatrix C.hessianIntervals) T))
    {B : ReplayBox 4} (hB : C.box.EnclosesABBOffsets B)
    (hs : ∀i,SmallCoefficient (C.box.coefficient i)) (hb : BoundedContact C.box) :
    ∀x,B.Contains x → RadiusABBOffsetProperty x := by
  intro x hx z hz hz1 q hq he v hv
  obtain ⟨hL,hbox⟩ := C.box.bounds_of_offsets hC.1 hB hz hz1 (he ▸ hx)
  exact hessian_positive_of_retracted_enclosure
    (bounded_contact_sound C.box hC.1 hb hz hz1 hL)
    (coefficient_bounds_of_certificate C.box hC.1 hs hz hL) hq C.hessianIntervals T
    (C.hessianIntervals_contains hC hz hL hbox) hm hv

/-- Full coverage assembly at the literal manuscript radius. The padded leaf
proofs, including their new margins, remain explicit until checked. -/
theorem abb_hessian_of_table (table : RegisterTree (Option (ReplayBox 4)))
    (tree : BoxReplay 4) (htree : tree.Valid table.get familyABBInitialBox)
    (hleaf : table.All (ReplayBoxProperty RadiusABBOffsetProperty))
    {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z) binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  have hz40 := FamilyAAACover.z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hp := tree.sound_table hleaf htree _
    (familyABBInitialBox_contains hL (retract_in_cube hq))
  exact hp z hz hz1 q hq rfl v hv

theorem abb_local_of_table (table : RegisterTree (Option (ReplayBox 4)))
    (tree : BoxReplay 4) (htree : tree.Valid table.get familyABBInitialBox)
    (hleaf : table.All (ReplayBoxProperty RadiusABBOffsetProperty))
    {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z) binary64Radius) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) := by
  have hz40 := FamilyAAACover.z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  apply familyContactABB_local hz hz1 (gamma_branch_neg hz hz40).ne binary64Radius_pos.le _ hq
  intro p hp v hv
  exact abb_hessian_of_table table tree htree hleaf hz hL hp hv

end SparseLowerTail.Certificate.HessianRadiusTransfer

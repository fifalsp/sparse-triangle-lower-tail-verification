import SparseLowerTail.Section08.FamilyTaylorData
import SparseLowerTail.Section08.FamilyExteriorTaylor
import SparseLowerTail.Section08.FamilyLocalFactoredIntervals

/-! A finite exterior Taylor leaf. Validity consists of exact parameter,
exponential, interval, geometry, and scalar margin checks. -/
namespace SparseLowerTail.Certificate
open Numerics Section04

structure FamilyExteriorLeaf where
  data : FamilyTaylorData
  box : FamilyBoxCertificate
  radius : Fin 3 → ℚ
  beta : Fin 3 → ℚ

namespace FamilyExteriorLeaf

def diagonal (C : FamilyExteriorLeaf) (i : Fin 3) : ℚ :=
  (C.box.factoredHessianIntervals i i).toRational.lower
def cross (C : FamilyExteriorLeaf) (i j : Fin 3) : ℚ :=
  (C.box.factoredHessianIntervals i j).toRational.absUpper
def margin (C : FamilyExteriorLeaf) : ℚ :=
  C.data.valueLower+(C.beta 0+C.beta 1+C.beta 2)-
    (C.cross 0 1*C.radius 0*C.radius 1+C.cross 0 2*C.radius 0*C.radius 2+
      C.cross 1 2*C.radius 1*C.radius 2)

structure Valid (C : FamilyExteriorLeaf) : Prop where
  data_valid : C.data.Valid
  box_valid : C.box.Valid
  same_parameter : C.box.parameter=C.data.whole
  center_lower : ∀i,(C.box.qLower i).q≤(C.data.qCenter i).q
  center_upper : ∀i,(C.data.qCenter i).q≤(C.box.qUpper i).q
  radius_left : ∀i,(C.data.qCenter i).q-(C.box.qLower i).q≤C.radius i
  radius_right : ∀i,(C.box.qUpper i).q-(C.data.qCenter i).q≤C.radius i
  choice : ∀i,C.beta i≤-C.data.gradientUpper i*C.radius i+min 0 (C.diagonal i)*(C.radius i)^2/2 ∨
    (0<C.diagonal i ∧ C.beta i≤-(C.data.gradientUpper i)^2/(2*C.diagonal i)) ∨
    (0<C.diagonal i ∧ C.diagonal i*C.radius i≤C.data.gradientLower i ∧
      C.beta i≤-C.data.gradientUpper i*C.radius i+C.diagonal i*(C.radius i)^2/2)
  positive_margin : 0<C.margin

/-- An accepted leaf proves strict positivity for every real point of its
whole four-dimensional box. No numeric success flag is trusted. -/
theorem margin_le (C : FamilyExteriorLeaf) (hC : C.Valid) {t : ℝ}
    (ht : Bounds t (C.data.whole.logLower.q : ℝ) (C.data.whole.logUpper.q : ℝ))
    {q : FamilyVector}
    (hq : ∀i,Bounds (q i) ((C.box.qLower i).q : ℝ) ((C.box.qUpper i).q : ℝ)) :
    (C.margin : ℝ)≤familyPhi (Real.exp (-t)) q := by
  have hcenter (i : Fin 3) :
      Bounds (C.data.q i) ((C.box.qLower i).q : ℝ) ((C.box.qUpper i).q : ℝ) := by
    dsimp [FamilyTaylorData.q,FamilyWeightExpr.center]
    exact ⟨by exact_mod_cast hC.center_lower i,by exact_mod_cast hC.center_upper i⟩
  have hr (i : Fin 3) : |q i-C.data.q i|≤(C.radius i : ℝ) := by
    have hl : C.data.q i-((C.box.qLower i).q : ℝ)≤(C.radius i : ℝ) := by
      dsimp [FamilyTaylorData.q,FamilyWeightExpr.center]
      exact_mod_cast hC.radius_left i
    have hu : ((C.box.qUpper i).q : ℝ)-C.data.q i≤(C.radius i : ℝ) := by
      dsimp [FamilyTaylorData.q,FamilyWeightExpr.center]
      exact_mod_cast hC.radius_right i
    exact abs_le.mpr ⟨by linarith [(hq i).1],by linarith [(hq i).2]⟩
  have hhess (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) (i j : Fin 3) :
      (C.box.factoredHessianIntervals i j).toRational.contains
        (familyHessian (Real.exp (-t)) (familySegment C.data.q (q-C.data.q) s) i j) := by
    apply DyadicInterval.toRational_contains.mpr
    apply C.box.factoredHessianIntervals_contains hC.box_valid (Real.exp_pos _)
    · rw [hC.same_parameter]
      simpa only [branchLog_eq_neg_log,Real.log_exp,neg_neg] using ht
    · intro k
      exact Bounds.segment (hcenter k) (hq k) hs.1 hs.2
  have hlower := familyPhi_exterior_lower
    (p := C.data.q) (q := q) (r := fun i => (C.radius i : ℝ))
    (P := fun i => (C.data.gradientUpper i : ℝ))
    (m := fun i => (C.data.gradientLower i : ℝ))
    (h := fun i => (C.diagonal i : ℝ)) (β := fun i => (C.beta i : ℝ))
    (K := fun i j => (C.cross i j : ℝ))
    (C.data.valueLower_bound hC.data_valid ht) hr
    (fun i => (C.data.gradient_bounds hC.data_valid ht i).2)
    (fun i => (C.data.gradient_bounds hC.data_valid ht i).1)
    (fun i => by
      dsimp only
      rcases hC.choice i with hb | ⟨hh,hb⟩ | ⟨hh,hfar,hb⟩
      · exact Or.inl (by exact_mod_cast hb)
      · exact Or.inr (Or.inl ⟨by exact_mod_cast hh,by exact_mod_cast hb⟩)
      · exact Or.inr (Or.inr ⟨by exact_mod_cast hh,by exact_mod_cast hfar,by exact_mod_cast hb⟩))
    (fun s hs i => (hhess s hs i i).1)
    (fun s hs i j _ => RationalInterval.absUpper_bound (hhess s hs i j))
  simpa only [margin,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,familyCrossError,sumThree] using hlower

theorem positive (C : FamilyExteriorLeaf) (hC : C.Valid) {t : ℝ}
    (ht : Bounds t (C.data.whole.logLower.q : ℝ) (C.data.whole.logUpper.q : ℝ))
    {q : FamilyVector}
    (hq : ∀i,Bounds (q i) ((C.box.qLower i).q : ℝ) ((C.box.qUpper i).q : ℝ)) :
    0<familyPhi (Real.exp (-t)) q :=
  (show (0:ℝ)<(C.margin : ℝ) by exact_mod_cast hC.positive_margin).trans_le
    (C.margin_le hC ht hq)

end FamilyExteriorLeaf
end SparseLowerTail.Certificate

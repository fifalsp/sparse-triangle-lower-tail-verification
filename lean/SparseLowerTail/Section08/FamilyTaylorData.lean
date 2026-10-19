import SparseLowerTail.Section08.FamilyWeightIntervals
import SparseLowerTail.Numerics.IntervalMagnitudes

/-! Finite, checkable parameter data for an exterior Taylor leaf. Every
analytic bound below is derived from rational and dyadic checks. -/
namespace SparseLowerTail.Certificate
open Numerics Section04 FamilyCoeff

structure FamilyTaylorData where
  whole : FamilyParameterCertificate
  midpoint : FamilyParameterCertificate
  qCenter : Fin 3 → ExpEndpointCertificate
  wholeD : Fin 4 → Fin 7 → DyadicInterval
  centerD : Fin 3 → Fin 7 → DyadicInterval
  width : ℚ

namespace FamilyTaylorData

structure Valid (C : FamilyTaylorData) : Prop where
  whole_valid : C.whole.Valid
  midpoint_valid : C.midpoint.Valid
  q_valid : ∀i,(C.qCenter i).Valid
  point : C.midpoint.logLower.q=C.midpoint.logUpper.q
  positive : 0<C.whole.logLower.q
  center_lower : C.whole.logLower.q≤C.midpoint.logLower.q
  center_upper : C.midpoint.logLower.q≤C.whole.logUpper.q
  width_nonneg : 0≤C.width
  width_left : C.midpoint.logLower.q-C.whole.logLower.q≤C.width
  width_right : C.whole.logUpper.q-C.midpoint.logLower.q≤C.width
  whole_checked : ∀n i,(derivativeExpr i n.val).dyadicEval C.whole.parameterBox=some (C.wholeD n i)
  center_checked : ∀n i,(derivativeExpr i n.val).dyadicEval C.midpoint.parameterBox=some (C.centerD n i)

noncomputable def q (C : FamilyTaylorData) : Fin 3 → ℝ := FamilyWeightExpr.center C.qCenter
noncomputable def c (C : FamilyTaylorData) : ℝ := C.midpoint.logLower.q

def phiCenter (C : FamilyTaylorData) (n : Fin 3) : DyadicInterval :=
  (weightedInterval (FamilyWeightExpr.weightIntervals C.qCenter) (C.centerD n)).add
    (if n.val=0 then FamilyWeightExpr.productInterval C.qCenter else DyadicInterval.point 0)
def phiThird (C : FamilyTaylorData) : DyadicInterval :=
  weightedInterval (FamilyWeightExpr.weightIntervals C.qCenter) (C.wholeD 3)
def gradientCenter (C : FamilyTaylorData) (i : Fin 3) (n : Fin 2) : DyadicInterval :=
  (weightedInterval (FamilyWeightExpr.gradientIntervals C.qCenter i) (C.centerD ⟨n.val,by omega⟩)).add
    (if n.val=0 then (FamilyWeightExpr.productInterval C.qCenter).neg else DyadicInterval.point 0)
def gradientSecond (C : FamilyTaylorData) (i : Fin 3) : DyadicInterval :=
  weightedInterval (FamilyWeightExpr.gradientIntervals C.qCenter i) (C.wholeD 2)

def valueLower (C : FamilyTaylorData) : ℚ :=
  (C.phiCenter 0).toRational.lower-(C.phiCenter 1).toRational.absUpper*C.width+
    min 0 (C.phiCenter 2).toRational.lower*C.width^2/2-
    C.phiThird.toRational.absUpper*C.width^3/6

def gradientError (C : FamilyTaylorData) (i : Fin 3) : ℚ :=
  (C.gradientCenter i 1).toRational.absUpper*C.width+
    (C.gradientSecond i).toRational.absUpper*C.width^2/2
def gradientUpper (C : FamilyTaylorData) (i : Fin 3) : ℚ :=
  (C.gradientCenter i 0).toRational.absUpper+C.gradientError i
def gradientLower (C : FamilyTaylorData) (i : Fin 3) : ℚ :=
  (C.gradientCenter i 0).toRational.absLower-C.gradientError i

theorem center_bounds (C : FamilyTaylorData) (hC : C.Valid) :
    Bounds C.c (C.midpoint.logLower.q : ℝ) (C.midpoint.logUpper.q : ℝ) :=
  ⟨le_rfl,by dsimp [c]; exact_mod_cast hC.point.le⟩

theorem segment_bounds (C : FamilyTaylorData) (hC : C.Valid) {t : ℝ}
    (ht : Bounds t (C.whole.logLower.q : ℝ) (C.whole.logUpper.q : ℝ))
    {s : ℝ} (hs : s∈Set.Icc (0:ℝ) 1) :
    Bounds (C.c+s*(t-C.c)) (C.whole.logLower.q : ℝ) (C.whole.logUpper.q : ℝ) := by
  apply Bounds.segment (show Bounds C.c _ _ from
    ⟨by dsimp [c]; exact_mod_cast hC.center_lower,by dsimp [c]; exact_mod_cast hC.center_upper⟩) ht hs.1 hs.2

theorem displacement_bound (C : FamilyTaylorData) (hC : C.Valid) {t : ℝ}
    (ht : Bounds t (C.whole.logLower.q : ℝ) (C.whole.logUpper.q : ℝ)) :
    |t-C.c|≤(C.width : ℝ) := by
  have hl : C.c-(C.whole.logLower.q : ℝ)≤(C.width : ℝ) := by dsimp [c]; exact_mod_cast hC.width_left
  have hu : (C.whole.logUpper.q : ℝ)-C.c≤(C.width : ℝ) := by dsimp [c]; exact_mod_cast hC.width_right
  exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

theorem phiCenter_contains (C : FamilyTaylorData) (hC : C.Valid) (n : Fin 3) :
    (C.phiCenter n).contains (phiParameterDerivative C.q n.val C.c) := by
  have hd := weightedDerivative_interval C.midpoint hC.midpoint_valid (phiWeights C.q) n.val
    (FamilyWeightExpr.weightIntervals C.qCenter) (C.centerD n)
    (FamilyWeightExpr.weightIntervals_contains C.qCenter hC.q_valid) (hC.center_checked n)
    (C.center_bounds hC)
  have hp := FamilyWeightExpr.productInterval_contains C.qCenter hC.q_valid
  by_cases hn : n.val=0
  · simpa only [phiCenter,phiParameterDerivative,hn,↓reduceIte] using DyadicInterval.add_contains hd hp
  · simpa only [phiCenter,phiParameterDerivative,hn,↓reduceIte,Rat.cast_zero] using
      DyadicInterval.add_contains hd (DyadicInterval.point_contains 0)

theorem gradientCenter_contains (C : FamilyTaylorData) (hC : C.Valid) (i : Fin 3) (n : Fin 2) :
    (C.gradientCenter i n).contains (gradientParameterDerivative C.q i n.val C.c) := by
  have hd := weightedDerivative_interval C.midpoint hC.midpoint_valid (FamilyCoeff.gradientWeights C.q i) n.val
    (FamilyWeightExpr.gradientIntervals C.qCenter i) (C.centerD ⟨n.val,by omega⟩)
    (FamilyWeightExpr.gradientIntervals_contains C.qCenter hC.q_valid i)
    (hC.center_checked ⟨n.val,by omega⟩) (C.center_bounds hC)
  have hp := DyadicInterval.neg_contains (FamilyWeightExpr.productInterval_contains C.qCenter hC.q_valid)
  by_cases hn : n.val=0
  · simpa only [gradientCenter,gradientParameterDerivative,hn,↓reduceIte,sub_eq_add_neg] using
      DyadicInterval.add_contains hd hp
  · simpa only [gradientCenter,gradientParameterDerivative,hn,↓reduceIte,sub_zero,add_zero,Rat.cast_zero] using
      DyadicInterval.add_contains hd (DyadicInterval.point_contains 0)

theorem valueLower_bound (C : FamilyTaylorData) (hC : C.Valid) {t : ℝ}
    (ht : Bounds t (C.whole.logLower.q : ℝ) (C.whole.logUpper.q : ℝ)) :
    (C.valueLower : ℝ)≤phi (Real.exp (-t)) (C.q 0) (C.q 1) (C.q 2) := by
  have hh := phi_parameter_taylor_lower C.whole hC.whole_valid C.q
    (FamilyWeightExpr.weightIntervals C.qCenter) C.wholeD
    (FamilyWeightExpr.weightIntervals_contains C.qCenter hC.q_valid) hC.whole_checked
    (fun s hs => C.segment_bounds hC ht hs) (by exact_mod_cast hC.positive)
    (C.displacement_bound hC ht)
  have hb0 := DyadicInterval.toRational_contains.mpr (C.phiCenter_contains hC 0)
  have hb1 := RationalInterval.absUpper_bound (DyadicInterval.toRational_contains.mpr (C.phiCenter_contains hC 1))
  have hb2 := (DyadicInterval.toRational_contains.mpr (C.phiCenter_contains hC 2)).1
  have hw : (0:ℝ)≤C.width := by exact_mod_cast hC.width_nonneg
  have hl := mul_le_mul_of_nonneg_right hb1 hw
  have hq := mul_le_mul_of_nonneg_right (min_le_min_left 0 hb2) (sq_nonneg (C.width : ℝ))
  simp only [Fin.val_zero,phiParameterDerivative_zero] at hb0
  simp only [valueLower,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_min,
    Rat.cast_zero,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  rw [DyadicInterval.toRational_absUpper C.phiThird]
  simp only [add_sub_cancel] at hh
  change _ ≤ phi (Real.exp (-t)) (C.q 0) (C.q 1) (C.q 2)
  dsimp only [phiThird] at *
  norm_num at hl hq
  linarith [hb0.1]

theorem gradient_bounds (C : FamilyTaylorData) (hC : C.Valid) {t : ℝ}
    (ht : Bounds t (C.whole.logLower.q : ℝ) (C.whole.logUpper.q : ℝ)) (i : Fin 3) :
    (C.gradientLower i : ℝ)≤|familyGradient (Real.exp (-t)) C.q i| ∧
    |familyGradient (Real.exp (-t)) C.q i|≤(C.gradientUpper i : ℝ) := by
  have hh := gradient_parameter_variation C.whole hC.whole_valid C.q i
    (FamilyWeightExpr.gradientIntervals C.qCenter i)
    (fun n => C.wholeD ⟨n.val,by omega⟩)
    (FamilyWeightExpr.gradientIntervals_contains C.qCenter hC.q_valid i)
    (fun n j => hC.whole_checked ⟨n.val,by omega⟩ j)
    (fun s hs => C.segment_bounds hC ht hs) (by exact_mod_cast hC.positive)
    (C.displacement_bound hC ht)
  have hb1 := RationalInterval.absUpper_bound
    (DyadicInterval.toRational_contains.mpr (C.gradientCenter_contains hC i 1))
  have hw : (0:ℝ)≤C.width := by exact_mod_cast hC.width_nonneg
  have hl := mul_le_mul_of_nonneg_right hb1 hw
  have herr : |familyGradient (Real.exp (-t)) C.q i-familyGradient (Real.exp (-C.c)) C.q i|≤
      (C.gradientError i : ℝ) := by
    simp only [gradientError,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
    rw [DyadicInterval.toRational_absUpper (C.gradientSecond i)]
    simp only [add_sub_cancel] at hh
    dsimp only [gradientSecond]
    exact hh.trans (add_le_add_right hl _)
  have hc0 := DyadicInterval.toRational_contains.mpr (C.gradientCenter_contains hC i 0)
  simp only [Fin.val_zero,gradientParameterDerivative_zero] at hc0
  simpa only [gradientLower,gradientUpper,Rat.cast_sub,Rat.cast_add] using
    RationalInterval.magnitude_bounds_of_error hc0 herr

end FamilyTaylorData
end SparseLowerTail.Certificate

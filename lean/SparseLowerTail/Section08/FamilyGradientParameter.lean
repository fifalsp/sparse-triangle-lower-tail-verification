import SparseLowerTail.Section08.FamilyParameterTaylor
import SparseLowerTail.Section08.FamilyLocalFormula

/-! Parameter variation of the actual q-gradient. This is the second-order
L estimate used by the exterior family certificate, with coefficient
cancellations retained before taking absolute values. -/
noncomputable section
namespace SparseLowerTail.Certificate.FamilyCoeff
open Numerics Section04 Set

/-- Coordinate derivatives of the seven signed weights in `phiWeights`. -/
def gradientWeights (q : Fin 3 → ℝ) (i : Fin 3) : Fin 7 → ℝ :=
  let x := fun j => Real.exp (-q j)
  let s := q 0+q 1+q 2
  ![0,-x i,-((1-q i)*x i),-1,(2*q i-(q i)^2)*x i,
    -x i*(x 0+x 1+x 2-x i),(s-1)*(x 0*x 1*x 2)]

def gradientParameterDerivative (q : Fin 3 → ℝ) (i : Fin 3) (n : ℕ) (t : ℝ) : ℝ :=
  weightedDerivative (gradientWeights q i) n t-
    if n=0 then Real.exp (-q 0)*Real.exp (-q 1)*Real.exp (-q 2) else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem gradientParameterDerivative_zero (q : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    gradientParameterDerivative q i 0 t=familyGradient (Real.exp (-t)) q i := by
  fin_cases i <;>
    simp [gradientParameterDerivative,weightedDerivative,coefficientDerivative_zero,
      gradientWeights,coefficientValues,Fin.sum_univ_succ,familyGradient,
      familyPhiExpr,familyPartials,familyVariables,PolynomialExpr.along,
      PolynomialExpr.realEval] <;> ring

theorem gradientParameterDerivative_hasDerivAt (q : Fin 3 → ℝ) (i : Fin 3)
    (n : ℕ) {t : ℝ} (ht : 0<t)
    (he : ∀j,(derivativeExpr j n).Domain (parameterCurve t)) :
    HasDerivAt (gradientParameterDerivative q i n)
      (gradientParameterDerivative q i (n+1) t) t := by
  simpa only [gradientParameterDerivative,Nat.add_one_ne_zero,↓reduceIte,sub_zero] using
    (weightedDerivative_hasDerivAt (gradientWeights q i) n ht he).sub_const
      (if n=0 then Real.exp (-q 0)*Real.exp (-q 1)*Real.exp (-q 2) else 0)

/-- The gradient error uses the second derivative over the whole interval,
while the first derivative remains evaluated at the center. -/
theorem gradient_parameter_variation (C : FamilyParameterCertificate) (hC : C.Valid)
    (q : Fin 3 → ℝ) (i : Fin 3) (W : Fin 7 → DyadicInterval)
    (D : Fin 3 → Fin 7 → DyadicInterval)
    (hW : ∀j,(W j).contains (gradientWeights q i j))
    (hD : ∀n j,(derivativeExpr j n.val).dyadicEval C.parameterBox=some (D n j))
    {c d w : ℝ}
    (hpath : ∀s ∈ Icc (0:ℝ) 1,
      Bounds (c+s*d) (C.logLower.q : ℝ) (C.logUpper.q : ℝ))
    (hpos : 0<(C.logLower.q : ℝ)) (hd : |d|≤w) :
    |familyGradient (Real.exp (-(c+d))) q i-familyGradient (Real.exp (-c)) q i| ≤
      |gradientParameterDerivative q i 1 c| * w+
        ((weightedInterval W (D 2)).absBound : ℝ)/DyadicInterval.scale*w^2/2 := by
  have hdv (n : Fin 2) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      HasDerivAt (gradientParameterDerivative q i n.val)
        (gradientParameterDerivative q i (n.val+1) (c+s*d)) (c+s*d) := by
    apply gradientParameterDerivative_hasDerivAt q i n.val (hpos.trans_le (hpath s hs).1)
    intro j
    apply RationalExpr.domain_of_dyadicEval _ _ (hD ⟨n.val,by omega⟩ j)
    rw [parameterCurve_eq]
    apply C.parameterBox_contains hC (Real.exp_pos _)
    simpa only [branchLog_eq_neg_log,Real.log_exp,neg_neg] using hpath s hs
  have hb (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      |gradientParameterDerivative q i 2 (c+s*d)| ≤
        ((weightedInterval W (D 2)).absBound : ℝ)/DyadicInterval.scale := by
    simpa only [gradientParameterDerivative,show (2:ℕ)≠0 by decide,↓reduceIte,sub_zero] using
      DyadicInterval.abs_le_absBound
        (weightedDerivative_interval C hC (gradientWeights q i) 2 W (D 2) hW (hD 2) (hpath s hs))
  simpa [gradientParameterDerivative_zero] using parameter_variation2 (hdv 0) (hdv 1) hb hd

end SparseLowerTail.Certificate.FamilyCoeff

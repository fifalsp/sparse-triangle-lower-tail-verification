import SparseLowerTail.Section05.ApexTangencyDeterminant
import SparseLowerTail.Section05.CoverCoefficientData

/-! Exact coefficients for each of the six published fan cells. The rounded
fixed slots are retained verbatim; only slots 0,2,3,4 are solved. All contact
values and gradients are proved exactly, not checked against a tolerance. -/
noncomputable section
namespace SparseLowerTail.Section05
open Numerics CoverGeometry

theorem apexExactCoefficients_fixed (base : Fin 12 → ℚ) (lam : ℚ) (i : Fin 12)
    (h0 : i≠0) (h2 : i≠2) (h3 : i≠3) (h4 : i≠4) :
    apexExactCoefficients base lam i=(base i : ℝ) := by
  simp [apexExactCoefficients,apexSolvedCoefficients,apexCoefficientBasis,
    apexUnknownIndex,h0,h2,h3,h4]

/-- Uniqueness concerns the four exact corrections, with all other slots fixed. -/
theorem apexTangencySolution_unique (base : Fin 12 → ℚ) (lam : ℚ)
    {x : Fin 4 → ℝ}
    (hx : apexTangencyResidual (apexSolvedCoefficients (fun i => (base i : ℝ)) x)
      (lam : ℝ)=0) :
    x=fun j => (apexSolutionExpr base lam j).realEval apexPrimitiveValues := by
  rw [apexSolvedCoefficients_residual] at hx
  have hs : apexTangencyMatrix.mulVec x= -apexTangencyResidual (fun i => (base i : ℝ)) (lam : ℝ) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hx
  apply RationalExpr.cramer4_unique apexTangencyMatrixExpr (apexTangencyRhsExpr base lam)
    apexPrimitiveValues
  · simpa only [apexTangencyMatrixExpr_eval] using apexTangencyMatrix_det_ne_zero
  · simpa only [apexTangencyMatrixExpr_eval,apexTangencyRhsExpr_eval] using hs

def apexFanTheta (i : Fin 6) : Fin 12 → ℝ :=
  apexExactCoefficients (fixedCellThetaQ (i.castAdd 6)) (cellLambdaQ (i.castAdd 6))

/-- The published null slots are exactly the four solved positions. -/
theorem fixedCellThetaQ_fan_unknown_zero (i : Fin 6) (j : Fin 4) :
    fixedCellThetaQ (i.castAdd 6) (apexUnknownIndex j)=0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem apexSolvedCoefficients_unknown (base : Fin 12 → ℝ) (x : Fin 4 → ℝ) (j : Fin 4) :
    apexSolvedCoefficients base x (apexUnknownIndex j)=base (apexUnknownIndex j)+x j := by
  fin_cases j
  · change base 0+x 0*1+x 1*0+x 2*0+x 3*0=base 0+x 0
    ring
  · change base 2+x 0*0+x 1*1+x 2*0+x 3*0=base 2+x 1
    ring
  · change base 3+x 0*0+x 1*0+x 2*1+x 3*0=base 3+x 2
    ring
  · change base 4+x 0*0+x 1*0+x 2*0+x 3*1=base 4+x 3
    ring

theorem apexFanTheta_unknown (i : Fin 6) (j : Fin 4) :
    apexFanTheta i (apexUnknownIndex j)=
      (apexSolutionExpr (fixedCellThetaQ (i.castAdd 6))
        (cellLambdaQ (i.castAdd 6)) j).realEval apexPrimitiveValues := by
  unfold apexFanTheta apexExactCoefficients
  rw [apexSolvedCoefficients_unknown,fixedCellThetaQ_fan_unknown_zero]
  simp

theorem apexFanTheta_fixed (i : Fin 6) (j : Fin 12)
    (h0 : j≠0) (h2 : j≠2) (h3 : j≠3) (h4 : j≠4) :
    apexFanTheta i j=(fixedCellThetaQ (i.castAdd 6) j : ℝ) :=
  apexExactCoefficients_fixed _ _ j h0 h2 h3 h4

theorem apexFanTheta_tangent (i : Fin 6) :
    apexTangencyResidual (apexFanTheta i) (cellLambda (i.castAdd 6))=0 := by
  rw [←cellLambdaQ_cast]
  exact apexExactCoefficients_tangent_checked _ _

theorem apexFanTheta_contacts (i : Fin 6) :
    (apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) apexContactAAA=0 ∧
      ∀j,apexGradient (apexFanTheta i) (cellLambda (i.castAdd 6)) apexContactAAA j=0) ∧
    (apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) apexContactABB=0 ∧
      ∀j,apexGradient (apexFanTheta i) (cellLambda (i.castAdd 6)) apexContactABB j=0) :=
  apexTangency_contacts (apexFanTheta_tangent i)

end SparseLowerTail.Section05

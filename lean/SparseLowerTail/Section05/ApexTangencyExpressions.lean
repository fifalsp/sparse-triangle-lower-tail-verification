import SparseLowerTail.Section05.ApexContactGradients
import SparseLowerTail.Numerics.RationalSubstitution
import SparseLowerTail.Numerics.RationalMatrix4

/-! Rational reification of the exact four-by-four tangency matrix. Its nine
primitive parameters are qa,qb,a,b,t,omega,mu,m,F. Every matrix/RHS entry is
proved equal to the actual certificate value or derivative before evaluation. -/
noncomputable section
namespace SparseLowerTail.Section05
open Numerics Section04

abbrev ApexParameterExpr := RationalExpr 9

def apexPrimitiveValues : Fin 9 → ℝ :=
  ![-Real.log criticalA,-Real.log criticalB,criticalA,criticalB,criticalTriangle,
    criticalOmega,relaxationMultiplier criticalPoint,criticalMean,criticalCost]

def apexContactForRow (i : Fin 4) : ApexVector :=
  if i.val<2 then apexContactAAA else apexContactABB

def apexEquationExpr (i : Fin 4) : ApexExpr :=
  if i=0 then apexCertificateExpr else
    (apexCertificateExpr.along (apexPartials (if i=3 then 1 else 0))).simplify

theorem apexEquationExpr_eval (θ : Fin 12 → ℝ) (lam : ℝ) (i : Fin 4) :
    (apexEquationExpr i).realEval (apexVariables θ lam (apexContactForRow i))=
      apexTangencyResidual θ lam i := by
  fin_cases i
  · exact apexCertificateExpr_realEval θ lam _
  · change (apexCertificateExpr.along (apexPartials 0)).simplify.realEval
      (apexVariables θ lam apexContactAAA) = _
    exact PolynomialExpr.realEval_simplify _ _
  · change (apexCertificateExpr.along (apexPartials 0)).simplify.realEval
      (apexVariables θ lam apexContactABB) = _
    exact PolynomialExpr.realEval_simplify _ _
  · change (apexCertificateExpr.along (apexPartials 1)).simplify.realEval
      (apexVariables θ lam apexContactABB) = _
    exact PolynomialExpr.realEval_simplify _ _

def apexContactSubstitution (θ : Fin 12 → ℚ) (lam : ℚ) (mixed : Bool) :
    Fin 24 → PolynomialExpr 9 :=
  ![.var 0,if mixed then .var 1 else .var 0,if mixed then .var 1 else .var 0,
    .var 2,if mixed then .var 3 else .var 2,if mixed then .var 3 else .var 2,
    .var 4,.var 5,.var 6,.var 7,.var 8,
    .rational (θ 0),.rational (θ 1),.rational (θ 2),.rational (θ 3),.rational (θ 4),
    .rational (θ 5),.rational (θ 6),.rational (θ 7),.rational (θ 8),.rational (θ 9),
    .rational (θ 10),.rational (θ 11),.rational lam]

theorem apexContactSubstitution_eval (θ : Fin 12 → ℚ) (lam : ℚ) (mixed : Bool) :
    (fun k => (apexContactSubstitution θ lam mixed k).realEval apexPrimitiveValues)=
      apexVariables (fun j => (θ j : ℝ)) (lam : ℝ)
        (if mixed then apexContactABB else apexContactAAA) := by
  have ha : 0<criticalA := branchA_pos transitionParameter_mem_Ioo.1
  have hb : 0<criticalB := branchB_pos transitionParameter
  cases mixed <;> funext k <;> fin_cases k <;>
    norm_num [apexContactSubstitution,apexPrimitiveValues,apexVariables,apexEnvironment,
      apexContactAAA,apexContactABB,PolynomialExpr.realEval,Matrix.cons_val,neg_neg,
      Real.exp_log ha,Real.exp_log hb,Bool.false_eq_true,if_false,if_true]
  all_goals first
    | rfl
    | (change criticalB = Real.exp (-(-Real.log criticalB)); rw [neg_neg, Real.exp_log hb])

def apexResidualExpr (θ : Fin 12 → ℚ) (lam : ℚ) (i : Fin 4) : ApexParameterExpr :=
  ((apexEquationExpr i).subst (apexContactSubstitution θ lam (decide (2 ≤ i.val)))).simplify.toRational

theorem apexResidualExpr_eval (θ : Fin 12 → ℚ) (lam : ℚ) (i : Fin 4) :
    (apexResidualExpr θ lam i).realEval apexPrimitiveValues=
      apexTangencyResidual (fun j => (θ j : ℝ)) (lam : ℝ) i := by
  rw [apexResidualExpr,PolynomialExpr.toRational_realEval,PolynomialExpr.realEval_simplify,
    PolynomialExpr.subst_realEval,apexContactSubstitution_eval]
  have he : (if decide (2 ≤ i.val) then apexContactABB else apexContactAAA)=apexContactForRow i := by
    fin_cases i <;> rfl
  rw [he]
  exact apexEquationExpr_eval _ _ i

def apexCoefficientBasisQ (j : Fin 4) : Fin 12 → ℚ :=
  fun i => if i=apexUnknownIndex j then 1 else 0

theorem apexCoefficientBasisQ_cast (j : Fin 4) :
    (fun i => (apexCoefficientBasisQ j i : ℝ))=apexCoefficientBasis j := by
  funext i
  simp only [apexCoefficientBasisQ,apexCoefficientBasis]
  split_ifs <;> norm_num

def apexTangencyMatrixExpr (i j : Fin 4) : ApexParameterExpr :=
  apexResidualExpr (apexCoefficientBasisQ j) 0 i

theorem apexTangencyMatrixExpr_eval :
    RationalExpr.matrixEval apexTangencyMatrixExpr apexPrimitiveValues=apexTangencyMatrix := by
  funext i j
  simp only [RationalExpr.matrixEval,apexTangencyMatrixExpr,apexResidualExpr_eval,
    apexCoefficientBasisQ_cast,Rat.cast_zero,apexTangencyMatrix]

def apexTangencyRhsExpr (base : Fin 12 → ℚ) (lam : ℚ) (i : Fin 4) : ApexParameterExpr :=
  -(apexResidualExpr base lam i)

theorem apexTangencyRhsExpr_eval (base : Fin 12 → ℚ) (lam : ℚ) :
    (fun i => (apexTangencyRhsExpr base lam i).realEval apexPrimitiveValues)=
      -apexTangencyResidual (fun j => (base j : ℝ)) (lam : ℝ) := by
  funext i
  simp only [apexTangencyRhsExpr,RationalExpr.realEval_neg,apexResidualExpr_eval,Pi.neg_apply]

def apexSolutionExpr (base : Fin 12 → ℚ) (lam : ℚ) (j : Fin 4) : ApexParameterExpr :=
  RationalExpr.cramer4 apexTangencyMatrixExpr (apexTangencyRhsExpr base lam) j

def apexExactCoefficients (base : Fin 12 → ℚ) (lam : ℚ) : Fin 12 → ℝ :=
  apexSolvedCoefficients (fun j => (base j : ℝ))
    (fun j => (apexSolutionExpr base lam j).realEval apexPrimitiveValues)

/-- Invertibility of the one common matrix suffices for every fan cell. -/
theorem apexExactCoefficients_tangent (base : Fin 12 → ℚ) (lam : ℚ)
    (hd : apexTangencyMatrix.det≠0) :
    apexTangencyResidual (apexExactCoefficients base lam) (lam : ℝ)=0 := by
  apply apexSolvedCoefficients_tangent
  have h := RationalExpr.cramer4_solves apexTangencyMatrixExpr (apexTangencyRhsExpr base lam)
    apexPrimitiveValues (by simpa only [apexTangencyMatrixExpr_eval] using hd)
  simpa only [apexTangencyMatrixExpr_eval,apexTangencyRhsExpr_eval,apexSolutionExpr] using h

/-- Exact, fully stationary contacts for the Cramer-defined coefficients. -/
theorem apexExactCoefficients_contacts (base : Fin 12 → ℚ) (lam : ℚ)
    (hd : apexTangencyMatrix.det≠0) :
    (apexPhi (apexExactCoefficients base lam) (lam : ℝ) apexContactAAA=0 ∧
      ∀i,apexGradient (apexExactCoefficients base lam) (lam : ℝ) apexContactAAA i=0) ∧
    (apexPhi (apexExactCoefficients base lam) (lam : ℝ) apexContactABB=0 ∧
      ∀i,apexGradient (apexExactCoefficients base lam) (lam : ℝ) apexContactABB i=0) :=
  apexTangency_contacts (apexExactCoefficients_tangent base lam hd)

end SparseLowerTail.Section05

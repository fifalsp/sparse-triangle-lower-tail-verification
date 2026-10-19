import SparseLowerTail.Section08.FamilyBoxIntervals
import SparseLowerTail.Section08.FamilyLocalIntervalMatrix

/-! Connecting the actual logarithmic Hessian to checked interval boxes. -/
namespace SparseLowerTail.Certificate
open Section04 Numerics
namespace FamilyBoxCertificate

def hessianIntervals (C : FamilyBoxCertificate) : FamilyIntervalMatrix := fun i j =>
  ((familyPhiExpr.along (familyPartials i)).along (familyPartials j)).dyadicEval
    C.variableIntervals

theorem hessianIntervals_contains (C : FamilyBoxCertificate) (hC : C.Valid)
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ) (C.parameter.logUpper.q : ℝ))
    {q : FamilyVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ)) :
    ∀i j,(C.hessianIntervals i j).contains (familyHessian z q i j) := by
  intro i j
  exact PolynomialExpr.dyadicEval_contains _ (C.variableIntervals_contains hC hz hL hq)

theorem hessian_positive (C : FamilyBoxCertificate) (hC : C.Valid)
    (T : FamilyRationalMatrix)
    (hpos : FamilyIntervalPositive (familyIntervalCongruence C.hessianIntervals T))
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ) (C.parameter.logUpper.q : ℝ))
    {q : FamilyVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact familyQuadratic_pos_of_interval_congruence (familyHessian_symmetric z q)
    C.hessianIntervals T (C.hessianIntervals_contains hC hz hL hq) hpos hv

end FamilyBoxCertificate
end SparseLowerTail.Certificate

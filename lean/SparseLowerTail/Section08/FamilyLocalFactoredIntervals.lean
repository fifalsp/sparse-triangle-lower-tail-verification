import SparseLowerTail.Section08.FamilyLocalBoxIntervals

/-! Algebraically factored actual Hessian entries reduce interval dependency.
In particular q²-4q+2 is represented as (q-2)²-2. -/
namespace SparseLowerTail.Certificate
open Section04 Numerics
namespace FamilyHessianExpr
abbrev Expr := PolynomialExpr 13
def q (i : Fin 3) : Expr := .var ⟨i.val,by omega⟩
def x (i : Fin 3) : Expr := .var ⟨i.val+3,by omega⟩
def otherX (i : Fin 3) : Expr :=
  ![x 1+x 2,x 0+x 2,x 0+x 1] i
def common : Expr := x 0*x 1*x 2*(1+2*(.var 12)-(.var 12)*(q 0+q 1+q 2))
def diagonal (i : Fin 3) : Expr :=
  x i*((.var 7)+(.var 8)*(2-q i)+(.var 10)*((q i-2)^2-2))+
    (.var 11)*x i*otherX i+common
def offDiagonal (i j : Fin 3) : Expr := (.var 11)*x i*x j+common
def entry (i j : Fin 3) : Expr := if i=j then diagonal i else offDiagonal i j

theorem q_eval (z : ℝ) (v : FamilyVector) (i : Fin 3) :
    (q i).realEval (familyVariables z v) = v i := by
  fin_cases i <;> rfl

theorem x_eval (z : ℝ) (v : FamilyVector) (i : Fin 3) :
    (x i).realEval (familyVariables z v) = Real.exp (-v i) := by
  fin_cases i <;> rfl

theorem otherX_eval (z : ℝ) (v : FamilyVector) (i : Fin 3) :
    (otherX i).realEval (familyVariables z v) =
      Real.exp (-v 0)+Real.exp (-v 1)+Real.exp (-v 2)-Real.exp (-v i) := by
  fin_cases i
  · change Real.exp (-v 1)+Real.exp (-v 2) =
      Real.exp (-v 0)+Real.exp (-v 1)+Real.exp (-v 2)-Real.exp (-v 0)
    ring
  · change Real.exp (-v 0)+Real.exp (-v 2) =
      Real.exp (-v 0)+Real.exp (-v 1)+Real.exp (-v 2)-Real.exp (-v 1)
    ring
  · change Real.exp (-v 0)+Real.exp (-v 1) =
      Real.exp (-v 0)+Real.exp (-v 1)+Real.exp (-v 2)-Real.exp (-v 2)
    ring

theorem common_eval (z : ℝ) (v : FamilyVector) :
    common.realEval (familyVariables z v) = familyHessianCommon z v := by
  simp only [common, PolynomialExpr.realEval_add, PolynomialExpr.realEval_sub,
    PolynomialExpr.realEval_mul, PolynomialExpr.realEval_one, PolynomialExpr.realEval_two,
    x_eval, q_eval]
  change Real.exp (-v 0)*Real.exp (-v 1)*Real.exp (-v 2)*
    (1+2*(branchMu z*c4 z)-(branchMu z*c4 z)*(v 0+v 1+v 2)) = _
  unfold familyHessianCommon
  ring

theorem diagonal_eval (z : ℝ) (v : FamilyVector) (i : Fin 3) :
    (diagonal i).realEval (familyVariables z v) = familyHessianDiagonal z v i := by
  simp only [diagonal, PolynomialExpr.realEval_add, PolynomialExpr.realEval_sub,
    PolynomialExpr.realEval_mul, PolynomialExpr.realEval_pow, PolynomialExpr.realEval_two,
    x_eval, q_eval, otherX_eval, common_eval]
  change Real.exp (-v i)*(c1 z+c2 z*(2-v i)+c4 z*((v i-2)^2-2))+
    (branchMu z*c3 z)*Real.exp (-v i)*
      (Real.exp (-v 0)+Real.exp (-v 1)+Real.exp (-v 2)-Real.exp (-v i))+
    familyHessianCommon z v = _
  unfold familyHessianDiagonal
  ring

theorem offDiagonal_eval (z : ℝ) (v : FamilyVector) (i j : Fin 3) :
    (offDiagonal i j).realEval (familyVariables z v) = familyHessianOffDiagonal z v i j := by
  simp only [offDiagonal, PolynomialExpr.realEval_add, PolynomialExpr.realEval_mul,
    x_eval, common_eval]
  rfl

theorem entry_eval (z : ℝ) (v : FamilyVector) (i j : Fin 3) :
    (entry i j).realEval (familyVariables z v)=familyHessian z v i j := by
  rw [familyHessian_formula]
  by_cases h : i=j
  · simp only [entry, h, if_true, diagonal_eval]
  · simp only [entry, h, if_false, offDiagonal_eval]
end FamilyHessianExpr

namespace FamilyBoxCertificate
def factoredHessianIntervals (C : FamilyBoxCertificate) : FamilyIntervalMatrix :=
  fun i j => (FamilyHessianExpr.entry i j).dyadicEval C.variableIntervals

theorem factoredHessianIntervals_contains (C : FamilyBoxCertificate) (hC : C.Valid)
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ) (C.parameter.logUpper.q : ℝ))
    {q : FamilyVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ)) :
    ∀i j,(C.factoredHessianIntervals i j).contains (familyHessian z q i j) := by
  intro i j
  rw [←FamilyHessianExpr.entry_eval]
  exact PolynomialExpr.dyadicEval_contains _ (C.variableIntervals_contains hC hz hL hq)

theorem factored_hessian_positive (C : FamilyBoxCertificate) (hC : C.Valid)
    (T : FamilyRationalMatrix)
    (hpos : FamilyIntervalPositive (familyIntervalCongruence C.factoredHessianIntervals T))
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ) (C.parameter.logUpper.q : ℝ))
    {q : FamilyVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact familyQuadratic_pos_of_interval_congruence (familyHessian_symmetric z q)
    C.factoredHessianIntervals T (C.factoredHessianIntervals_contains hC hz hL hq) hpos hv
end FamilyBoxCertificate
end SparseLowerTail.Certificate

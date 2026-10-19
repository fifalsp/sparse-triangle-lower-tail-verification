import SparseLowerTail.Section08.FamilyLocalFactoredIntervals

/-! Interval replay for the exponentially scaled family Hessian. Scaling is
performed algebraically before interval evaluation. Extra endpoint certificates
enclose exp(-(qᵢ+qⱼ)/2); no floating-point matrix is trusted. -/
namespace SparseLowerTail.Certificate
open Section04 Numerics

namespace FamilyHessianExpr

def otherProduct (i : Fin 3) : Expr := ![x 1*x 2,x 0*x 2,x 0*x 1] i
def remaining (i j : Fin 3) : Fin 3 := ![![0,2,1],![2,0,0],![1,0,0]] i j
def scaledFactor : Expr := 1+2*(.var 12)-(.var 12)*(q 0+q 1+q 2)
def scaledDiagonal (i : Fin 3) : Expr :=
  (.var 7)+(.var 8)*(2-q i)+(.var 10)*((q i-2)^2-2)+
    (.var 11)*otherX i+otherProduct i*scaledFactor
def scaledOffCore (i j : Fin 3) : Expr :=
  (.var 11)+x (remaining i j)*scaledFactor

theorem scaledDiagonal_eval (z : ℝ) (v : FamilyVector) (i : Fin 3) :
    (scaledDiagonal i).realEval (familyVariables z v)=familyHessianScaled z v i i := by
  have hp : (otherProduct i).realEval (familyVariables z v)=
      ![Real.exp (-v 1)*Real.exp (-v 2),Real.exp (-v 0)*Real.exp (-v 2),
        Real.exp (-v 0)*Real.exp (-v 1)] i := by fin_cases i <;> rfl
  have hs : (otherX i).realEval (familyVariables z v)=
      ![Real.exp (-v 1)+Real.exp (-v 2),Real.exp (-v 0)+Real.exp (-v 2),
        Real.exp (-v 0)+Real.exp (-v 1)] i := by fin_cases i <;> rfl
  simp only [scaledDiagonal,scaledFactor,PolynomialExpr.realEval_add,
    PolynomialExpr.realEval_sub,PolynomialExpr.realEval_mul,
    PolynomialExpr.realEval_pow,PolynomialExpr.realEval_one,PolynomialExpr.realEval_two,
    q_eval,hp,hs]
  fin_cases i
  · change c1 z+c2 z*(2-v 0)+c4 z*((v 0-2)^2-2)+
      (branchMu z*c3 z)*(Real.exp (-v 1)+Real.exp (-v 2))+
      (Real.exp (-v 1)*Real.exp (-v 2))*
        (1+2*(branchMu z*c4 z)-(branchMu z*c4 z)*(v 0+v 1+v 2)) =
        familyHessianScaled z v 0 0
    rw [familyHessianScaled_diagonal_formula z v 0 1 2 (by decide) (by decide) (by decide)]
    unfold familyScaledDiagonal
    ring
  · change c1 z+c2 z*(2-v 1)+c4 z*((v 1-2)^2-2)+
      (branchMu z*c3 z)*(Real.exp (-v 0)+Real.exp (-v 2))+
      (Real.exp (-v 0)*Real.exp (-v 2))*
        (1+2*(branchMu z*c4 z)-(branchMu z*c4 z)*(v 0+v 1+v 2)) =
        familyHessianScaled z v 1 1
    rw [familyHessianScaled_diagonal_formula z v 1 0 2 (by decide) (by decide) (by decide)]
    unfold familyScaledDiagonal
    ring
  · change c1 z+c2 z*(2-v 2)+c4 z*((v 2-2)^2-2)+
      (branchMu z*c3 z)*(Real.exp (-v 0)+Real.exp (-v 1))+
      (Real.exp (-v 0)*Real.exp (-v 1))*
        (1+2*(branchMu z*c4 z)-(branchMu z*c4 z)*(v 0+v 1+v 2)) =
        familyHessianScaled z v 2 2
    rw [familyHessianScaled_diagonal_formula z v 2 0 1 (by decide) (by decide) (by decide)]
    unfold familyScaledDiagonal
    ring

theorem scaledOffCore_eval (z : ℝ) (v : FamilyVector) (i j : Fin 3) (hij : i≠j) :
    Real.exp (-(v i+v j)/2)*(scaledOffCore i j).realEval (familyVariables z v)=
      familyHessianScaled z v i j := by
  have hik : i≠remaining i j := by fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide +kernel
  have hjk : j≠remaining i j := by fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide +kernel
  rw [familyHessianScaled_offDiagonal_formula z v i j (remaining i j) hij hik hjk]
  simp only [scaledOffCore,scaledFactor,PolynomialExpr.realEval_add,
    PolynomialExpr.realEval_sub,PolynomialExpr.realEval_mul,
    PolynomialExpr.realEval_one,PolynomialExpr.realEval_two,x_eval,q_eval]
  change Real.exp (-(v i+v j)/2)*(branchMu z*c3 z+Real.exp (-v (remaining i j))*
    (1+2*(branchMu z*c4 z)-(branchMu z*c4 z)*(v 0+v 1+v 2))) = _
  unfold familyScaledOffDiagonal
  ring

end FamilyHessianExpr

structure FamilyScaledBoxCertificate where
  box : FamilyBoxCertificate
  pairLower : Fin 3 → Fin 3 → ExpEndpointCertificate
  pairUpper : Fin 3 → Fin 3 → ExpEndpointCertificate

namespace FamilyScaledBoxCertificate

def Valid (C : FamilyScaledBoxCertificate) : Prop :=
  C.box.Valid ∧ ∀i j,i≠j →
    (C.pairLower i j).Valid ∧ (C.pairUpper i j).Valid ∧
    (C.pairLower i j).q≤((C.box.qLower i).q+(C.box.qLower j).q)/2 ∧
    ((C.box.qUpper i).q+(C.box.qUpper j).q)/2≤(C.pairUpper i j).q

instance (C : FamilyScaledBoxCertificate) : Decidable C.Valid :=
  inferInstanceAs (Decidable (C.box.Valid ∧ ∀i j,i≠j →
    (C.pairLower i j).Valid ∧ (C.pairUpper i j).Valid ∧
    (C.pairLower i j).q≤((C.box.qLower i).q+(C.box.qLower j).q)/2 ∧
    ((C.box.qUpper i).q+(C.box.qUpper j).q)/2≤(C.pairUpper i j).q))

def hessianIntervals (C : FamilyScaledBoxCertificate) : FamilyIntervalMatrix :=
  fun i j => if i=j then
    (FamilyHessianExpr.scaledDiagonal i).dyadicEval C.box.variableIntervals
  else (expEndpointInterval (C.pairLower i j) (C.pairUpper i j)).mul
    ((FamilyHessianExpr.scaledOffCore i j).dyadicEval C.box.variableIntervals)

theorem hessianIntervals_contains (C : FamilyScaledBoxCertificate) (hC : C.Valid)
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.box.parameter.logLower.q : ℝ)
      (C.box.parameter.logUpper.q : ℝ))
    {q : FamilyVector}
    (hq : ∀i,Bounds (q i) ((C.box.qLower i).q : ℝ) ((C.box.qUpper i).q : ℝ)) :
    ∀i j,(C.hessianIntervals i j).contains (familyHessianScaled z q i j) := by
  intro i j
  have hb := C.box.variableIntervals_contains hC.1 hz hL hq
  by_cases hij : i=j
  · subst j
    simp only [hessianIntervals,if_true]
    rw [←FamilyHessianExpr.scaledDiagonal_eval]
    exact PolynomialExpr.dyadicEval_contains _ hb
  · simp only [hessianIntervals,if_neg hij]
    rcases hC.2 i j hij with ⟨hl,hu,hlo,hup⟩
    have hmid : Bounds ((q i+q j)/2) ((C.pairLower i j).q : ℝ)
        ((C.pairUpper i j).q : ℝ) := by
      have hlo' : ((C.pairLower i j).q : ℝ)≤
          (((C.box.qLower i).q : ℝ)+(C.box.qLower j).q)/2 := by exact_mod_cast hlo
      have hup' : (((C.box.qUpper i).q : ℝ)+(C.box.qUpper j).q)/2≤
          ((C.pairUpper i j).q : ℝ) := by exact_mod_cast hup
      constructor <;> linarith [(hq i).1,(hq i).2,(hq j).1,(hq j).2]
    have he := expEndpointInterval_contains (C.pairLower i j) (C.pairUpper i j) hl hu hmid
    have hmul := DyadicInterval.mul_contains he
      (PolynomialExpr.dyadicEval_contains (FamilyHessianExpr.scaledOffCore i j) hb)
    rw [show -((q i+q j)/2)=-(q i+q j)/2 by ring,
      FamilyHessianExpr.scaledOffCore_eval z q i j hij] at hmul
    exact hmul

theorem hessian_positive (C : FamilyScaledBoxCertificate) (hC : C.Valid)
    (T : FamilyRationalMatrix)
    (hpos : FamilyIntervalPositive (familyIntervalCongruence C.hessianIntervals T))
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.box.parameter.logLower.q : ℝ)
      (C.box.parameter.logUpper.q : ℝ))
    {q : FamilyVector}
    (hq : ∀i,Bounds (q i) ((C.box.qLower i).q : ℝ) ((C.box.qUpper i).q : ℝ))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  familyHessian_pos_of_interval_congruence C.hessianIntervals T
    (C.hessianIntervals_contains hC hz hL hq) hpos hv

end FamilyScaledBoxCertificate
end SparseLowerTail.Certificate

import SparseLowerTail.Section08.FamilyGradientParameter

/-! Checked weights at a fixed q-center. These polynomial expressions are
independent of L; their inputs are rational q coordinates and certified
exponentials. -/
namespace SparseLowerTail.Certificate.FamilyWeightExpr
open Numerics FamilyCoeff
abbrev Expr := PolynomialExpr 6

def q (i : Fin 3) : Expr := .var ⟨i.val,by omega⟩
def x (i : Fin 3) : Expr := .var ⟨i.val+3,by omega⟩
def sumQ : Expr := q 0+q 1+q 2
def productX : Expr := x 0*x 1*x 2

def weights : Fin 7 → Expr :=
  ![3,x 0+x 1+x 2,-(q 0*x 0+q 1*x 1+q 2*x 2),-sumQ,
    (q 0)^2*x 0+(q 1)^2*x 1+(q 2)^2*x 2,
    x 0*x 1+x 1*x 2+x 2*x 0,-sumQ*productX]

def gradientWeights (i : Fin 3) : Fin 7 → Expr :=
  ![0,-x i,-((1-q i)*x i),-1,(2*q i-(q i)^2)*x i,
    -x i*(x 0+x 1+x 2-x i),(sumQ-1)*productX]

noncomputable def weightVariables (v : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![v 0,v 1,v 2,Real.exp (-v 0),Real.exp (-v 1),Real.exp (-v 2)]

theorem q_eval (v : Fin 3 → ℝ) (i : Fin 3) : (q i).realEval (weightVariables v)=v i := by
  fin_cases i <;> rfl

theorem x_eval (v : Fin 3 → ℝ) (i : Fin 3) :
    (x i).realEval (weightVariables v)=Real.exp (-v i) := by
  fin_cases i <;> rfl

theorem weights_eval (v : Fin 3 → ℝ) (i : Fin 7) :
    (weights i).realEval (weightVariables v)=phiWeights v i := by
  fin_cases i <;> simp [weights,phiWeights,sumQ,productX,q_eval,x_eval]
  <;> rfl

theorem gradientWeights_eval (v : Fin 3 → ℝ) (i : Fin 3) (j : Fin 7) :
    (gradientWeights i j).realEval (weightVariables v)=FamilyCoeff.gradientWeights v i j := by
  fin_cases j <;> simp [gradientWeights,FamilyCoeff.gradientWeights,sumQ,productX,q_eval,x_eval]


def centerIntervals (Q : Fin 3 → ExpEndpointCertificate) : Fin 6 → DyadicInterval :=
  ![DyadicInterval.point (Q 0).q,DyadicInterval.point (Q 1).q,DyadicInterval.point (Q 2).q,
    expEndpointInterval (Q 0) (Q 0),expEndpointInterval (Q 1) (Q 1),
    expEndpointInterval (Q 2) (Q 2)]

noncomputable def center (Q : Fin 3 → ExpEndpointCertificate) : Fin 3 → ℝ :=
  fun i => (Q i).q

theorem centerIntervals_contains (Q : Fin 3 → ExpEndpointCertificate)
    (hQ : ∀i,(Q i).Valid) : ∀i,(centerIntervals Q i).contains (weightVariables (center Q) i) := by
  have hx (i : Fin 3) := expEndpointInterval_contains (Q i) (Q i) (hQ i) (hQ i)
    (show Bounds ((Q i).q : ℝ) ((Q i).q : ℝ) ((Q i).q : ℝ) from ⟨le_rfl,le_rfl⟩)
  intro i
  fin_cases i
  · exact DyadicInterval.point_contains (Q 0).q
  · exact DyadicInterval.point_contains (Q 1).q
  · exact DyadicInterval.point_contains (Q 2).q
  · exact hx 0
  · exact hx 1
  · exact hx 2

def weightIntervals (Q : Fin 3 → ExpEndpointCertificate) : Fin 7 → DyadicInterval :=
  fun i => (weights i).dyadicEval (centerIntervals Q)
def gradientIntervals (Q : Fin 3 → ExpEndpointCertificate) (i : Fin 3) : Fin 7 → DyadicInterval :=
  fun j => (gradientWeights i j).dyadicEval (centerIntervals Q)
def productInterval (Q : Fin 3 → ExpEndpointCertificate) : DyadicInterval :=
  productX.dyadicEval (centerIntervals Q)

theorem weightIntervals_contains (Q : Fin 3 → ExpEndpointCertificate)
    (hQ : ∀i,(Q i).Valid) (i : Fin 7) :
    (weightIntervals Q i).contains (phiWeights (center Q) i) := by
  rw [←weights_eval]
  exact PolynomialExpr.dyadicEval_contains _ (centerIntervals_contains Q hQ)

theorem gradientIntervals_contains (Q : Fin 3 → ExpEndpointCertificate)
    (hQ : ∀i,(Q i).Valid) (i : Fin 3) (j : Fin 7) :
    (gradientIntervals Q i j).contains (FamilyCoeff.gradientWeights (center Q) i j) := by
  rw [←gradientWeights_eval]
  exact PolynomialExpr.dyadicEval_contains _ (centerIntervals_contains Q hQ)

theorem productInterval_contains (Q : Fin 3 → ExpEndpointCertificate)
    (hQ : ∀i,(Q i).Valid) :
    (productInterval Q).contains
      (Real.exp (-center Q 0)*Real.exp (-center Q 1)*Real.exp (-center Q 2)) := by
  have h := PolynomialExpr.dyadicEval_contains productX (centerIntervals_contains Q hQ)
  simpa only [productX,PolynomialExpr.realEval_mul,x_eval] using h

end SparseLowerTail.Certificate.FamilyWeightExpr

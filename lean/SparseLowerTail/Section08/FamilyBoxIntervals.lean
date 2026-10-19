import SparseLowerTail.Section08.FamilyParameterIntervals
import SparseLowerTail.Section08.FamilyLocalFormula

/-! Exact interval data for the actual four-variable family certificate:
three logarithmic edge coordinates and the branch parameter. -/
namespace SparseLowerTail.Certificate
open Section04 Numerics

structure FamilyBoxCertificate where
  parameter : FamilyParameterCertificate
  coefficient : Fin 7 → DyadicInterval
  qLower : Fin 3 → ExpEndpointCertificate
  qUpper : Fin 3 → ExpEndpointCertificate

namespace FamilyBoxCertificate

def Valid (C : FamilyBoxCertificate) : Prop :=
  C.parameter.Valid ∧
  (∀i,(FamilyCoeff.coefficientExpr i).dyadicEval C.parameter.parameterBox=some (C.coefficient i)) ∧
  (∀i,(C.qLower i).Valid) ∧ (∀i,(C.qUpper i).Valid)

instance (C : FamilyBoxCertificate) : Decidable C.Valid := inferInstanceAs (Decidable (
  C.parameter.Valid ∧
  (∀i,(FamilyCoeff.coefficientExpr i).dyadicEval C.parameter.parameterBox=some (C.coefficient i)) ∧
  (∀i,(C.qLower i).Valid) ∧ (∀i,(C.qUpper i).Valid)))

def qInterval (C : FamilyBoxCertificate) (i : Fin 3) : DyadicInterval :=
  DyadicInterval.ofRational ⟨(C.qLower i).q,(C.qUpper i).q⟩

def xInterval (C : FamilyBoxCertificate) (i : Fin 3) : DyadicInterval :=
  expEndpointInterval (C.qLower i) (C.qUpper i)

def variableIntervals (C : FamilyBoxCertificate) : Fin 13 → DyadicInterval :=
  ![C.qInterval 0,C.qInterval 1,C.qInterval 2,
    C.xInterval 0,C.xInterval 1,C.xInterval 2,
    C.coefficient 0,C.coefficient 1,C.coefficient 2,C.coefficient 3,
    C.coefficient 4,C.coefficient 5,C.coefficient 6]

theorem variableIntervals_contains (C : FamilyBoxCertificate) (hC : C.Valid)
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ) (C.parameter.logUpper.q : ℝ))
    {q : FamilyVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ)) :
    ∀i,(C.variableIntervals i).contains (familyVariables z q i) := by
  have hc (i : Fin 7) := C.parameter.coefficient_contains hC.1 hz hL i (hC.2.1 i)
  have hx (i : Fin 3) := expEndpointInterval_contains (C.qLower i) (C.qUpper i)
    (hC.2.2.1 i) (hC.2.2.2 i) (hq i)
  have hqi (i : Fin 3) : (C.qInterval i).contains (q i) :=
    DyadicInterval.ofRational_contains (hq i)
  intro i
  fin_cases i
  · exact hqi 0
  · exact hqi 1
  · exact hqi 2
  · exact hx 0
  · exact hx 1
  · exact hx 2
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hc 3
  · exact hc 4
  · exact hc 5
  · exact hc 6

/-- An exact positive lower endpoint proves the actual family certificate
strictly positive throughout the proposed parameter and coordinate box. -/
theorem phi_positive (C : FamilyBoxCertificate) (hC : C.Valid)
    (hpos : 0<(familyPhiExpr.dyadicEval C.variableIntervals).lower)
    {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (C.parameter.logLower.q : ℝ) (C.parameter.logUpper.q : ℝ))
    {q : FamilyVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ)) :
    0<familyPhi z q := by
  rw [←familyPhiExpr_eval]
  exact DyadicInterval.pos_of_lower_pos
    (familyPhiExpr.dyadicEval_contains (C.variableIntervals_contains hC hz hL hq)) hpos

end FamilyBoxCertificate
end SparseLowerTail.Certificate

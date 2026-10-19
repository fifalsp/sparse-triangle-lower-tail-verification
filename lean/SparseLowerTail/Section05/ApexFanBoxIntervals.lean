import SparseLowerTail.Section05.ApexFanIntervals
import SparseLowerTail.Section05.ApexLocalIntervals
import SparseLowerTail.Section08.FamilyParameterIntervals

/-! The exact fan coefficients and critical constants are now enclosed together
with an arbitrary logarithmic box. This connects numeric Hessian tests to the
actual solved fan certificate. -/
namespace SparseLowerTail.Section05
open Numerics Certificate CoverGeometry

structure ApexFanBox where
  qLower : Fin 3 → ExpEndpointCertificate
  qUpper : Fin 3 → ExpEndpointCertificate

namespace ApexFanBox

def Valid (C : ApexFanBox) : Prop :=
  (∀j,(C.qLower j).Valid) ∧ (∀j,(C.qUpper j).Valid)

instance (C : ApexFanBox) : Decidable C.Valid := inferInstanceAs (Decidable (
  (∀j,(C.qLower j).Valid) ∧ (∀j,(C.qUpper j).Valid)))

def qInterval (C : ApexFanBox) (j : Fin 3) : DyadicInterval :=
  DyadicInterval.ofRational ⟨(C.qLower j).q,(C.qUpper j).q⟩
def xInterval (C : ApexFanBox) (j : Fin 3) : DyadicInterval :=
  expEndpointInterval (C.qLower j) (C.qUpper j)

def variableIntervals (C : ApexFanBox) (i : Fin 6) : Fin 24 → DyadicInterval :=
  ![C.qInterval 0,C.qInterval 1,C.qInterval 2,
    C.xInterval 0,C.xInterval 1,C.xInterval 2,
    apexPrimitiveIntervals 4,apexPrimitiveIntervals 5,apexPrimitiveIntervals 6,
    apexPrimitiveIntervals 7,apexPrimitiveIntervals 8,
    apexFanCoefficientIntervals i 0,apexFanCoefficientIntervals i 1,apexFanCoefficientIntervals i 2,apexFanCoefficientIntervals i 3,
    apexFanCoefficientIntervals i 4,apexFanCoefficientIntervals i 5,apexFanCoefficientIntervals i 6,apexFanCoefficientIntervals i 7,
    apexFanCoefficientIntervals i 8,apexFanCoefficientIntervals i 9,apexFanCoefficientIntervals i 10,apexFanCoefficientIntervals i 11,
    DyadicInterval.point (cellLambdaQ (i.castAdd 6))]

theorem variableIntervals_contains (C : ApexFanBox) (hC : C.Valid) (i : Fin 6)
    {q : ApexVector}
    (hq : ∀j,Bounds (q j) ((C.qLower j).q : ℝ) ((C.qUpper j).q : ℝ)) :
    ∀k,(C.variableIntervals i k).contains
      (apexVariables (apexFanTheta i) (cellLambda (i.castAdd 6)) q k) := by
  have hx (j : Fin 3) := expEndpointInterval_contains (C.qLower j) (C.qUpper j)
    (hC.1 j) (hC.2 j) (hq j)
  have hqi (j : Fin 3) : (C.qInterval j).contains (q j) :=
    DyadicInterval.ofRational_contains (hq j)
  intro k
  fin_cases k
  · exact hqi 0
  · exact hqi 1
  · exact hqi 2
  · exact hx 0
  · exact hx 1
  · exact hx 2
  · exact apexPrimitiveIntervals_contains 4
  · exact apexPrimitiveIntervals_contains 5
  · exact apexPrimitiveIntervals_contains 6
  · exact apexPrimitiveIntervals_contains 7
  · exact apexPrimitiveIntervals_contains 8
  · exact apexFanCoefficientIntervals_contains i 0
  · exact apexFanCoefficientIntervals_contains i 1
  · exact apexFanCoefficientIntervals_contains i 2
  · exact apexFanCoefficientIntervals_contains i 3
  · exact apexFanCoefficientIntervals_contains i 4
  · exact apexFanCoefficientIntervals_contains i 5
  · exact apexFanCoefficientIntervals_contains i 6
  · exact apexFanCoefficientIntervals_contains i 7
  · exact apexFanCoefficientIntervals_contains i 8
  · exact apexFanCoefficientIntervals_contains i 9
  · exact apexFanCoefficientIntervals_contains i 10
  · exact apexFanCoefficientIntervals_contains i 11
  · change (DyadicInterval.point (cellLambdaQ (i.castAdd 6))).contains (cellLambda (i.castAdd 6))
    rw [←cellLambdaQ_cast]
    exact DyadicInterval.point_contains _

theorem hessian_positive (C : ApexFanBox) (hC : C.Valid) (i : Fin 6)
    (T : FamilyRationalMatrix)
    (hp : FamilyIntervalPositive (familyIntervalCongruence
      (apexHessianInterval (C.variableIntervals i)) T))
    {q : ApexVector}
    (hq : ∀j,Bounds (q j) ((C.qLower j).q : ℝ) ((C.qUpper j).q : ℝ))
    {v : ApexVector} (hv : v≠0) :
    0<apexHessianForm (apexFanTheta i) (cellLambda (i.castAdd 6)) q v :=
  apexHessianForm_pos_of_interval_congruence _ _ q _ T
    (apexHessianInterval_contains (C.variableIntervals_contains hC i hq)) hp hv

end ApexFanBox
end SparseLowerTail.Section05

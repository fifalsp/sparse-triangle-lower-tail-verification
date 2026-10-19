import SparseLowerTail.Section05.ApexRefinedFanIntervals
import SparseLowerTail.Section05.CoverJobIntervals

/-! The sharper primitive and solved-coefficient bounds enclose the same
actual fan certificates as before. This supplies the exterior replay. -/
namespace SparseLowerTail.Section05
open Numerics Certificate CoverGeometry

def apexRefinedConstants : Fin 5 → DyadicInterval :=
  ![apexRefinedPrimitiveIntervals 4,apexRefinedPrimitiveIntervals 5,
    apexRefinedPrimitiveIntervals 6,apexRefinedPrimitiveIntervals 7,apexRefinedPrimitiveIntervals 8]

theorem apexRefinedConstants_contains (i : Fin 5) :
    (apexRefinedConstants i).contains (coverConstantValues criticalPoint i) := by
  fin_cases i
  · exact apexRefinedPrimitiveIntervals_contains 4
  · exact apexRefinedPrimitiveIntervals_contains 5
  · exact apexRefinedPrimitiveIntervals_contains 6
  · exact apexRefinedPrimitiveIntervals_contains 7
  · exact apexRefinedPrimitiveIntervals_contains 8

def apexRefinedBoxIntervals (C : ApexFanBox) (i : Fin 6) : Fin 24 → DyadicInterval :=
  coverBoxIntervals C apexRefinedConstants (RefinedApex.apexFanCoefficientIntervals i)
    (DyadicInterval.point (cellLambdaQ (i.castAdd 6)))

theorem apexRefinedBoxIntervals_contains (C : ApexFanBox) (hC : C.Valid) (i : Fin 6)
    {q : ApexVector} (hq : ∀j,Bounds (q j) ((C.qLower j).q : ℝ) ((C.qUpper j).q : ℝ)) :
    ∀k,(apexRefinedBoxIntervals C i k).contains
      (apexVariables (apexFanTheta i) (cellLambda (i.castAdd 6)) q k) := by
  apply coverBoxIntervals_contains C hC apexRefinedConstants_contains
    (RefinedApex.apexFanCoefficientIntervals_contains i) _ hq
  rw [←cellLambdaQ_cast]
  exact DyadicInterval.point_contains _

theorem apexRefinedBox_positive (C : ApexFanBox) (hC : C.Valid) (i : Fin 6)
    (hp : 0<(apexCertificateExpr.dyadicEval (apexRefinedBoxIntervals C i)).lower)
    {q : ApexVector} (hq : ∀j,Bounds (q j) ((C.qLower j).q : ℝ) ((C.qUpper j).q : ℝ)) :
    0<apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) q := by
  have hb := (apexCertificateExpr.dyadicEval_contains (apexRefinedBoxIntervals_contains C hC i hq)).1
  have hpos : 0<((apexCertificateExpr.dyadicEval (apexRefinedBoxIntervals C i)).lower : ℝ)/
      DyadicInterval.scale := div_pos (by exact_mod_cast hp) DyadicInterval.scale_real_pos
  have h := hpos.trans_le hb
  simpa only [apexVariables,apexCertificateExpr_realEval,apexPhi] using h

end SparseLowerTail.Section05

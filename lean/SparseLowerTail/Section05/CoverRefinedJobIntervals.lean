import SparseLowerTail.Section05.ApexRefinedBoxIntervals

/-! Sharper actual coefficient and primitive enclosures for every nonapex job.
These are the same mathematical certificates, with refined verified data. -/
namespace SparseLowerTail.Section05.RefinedCover
open Numerics Certificate CoverGeometry

def coverCellThetaIntervals (i : Fin 12) : Fin 12 → DyadicInterval :=
  if h : i.val<6 then RefinedApex.apexFanCoefficientIntervals ⟨i.val,h⟩
  else fun j => DyadicInterval.point (fixedCellThetaQ i j)

theorem coverCellThetaIntervals_contains (i : Fin 12) (j : Fin 12) :
    (coverCellThetaIntervals i j).contains (coverCellTheta i j) := by
  unfold coverCellThetaIntervals coverCellTheta
  split_ifs with h
  · exact RefinedApex.apexFanCoefficientIntervals_contains ⟨i.val,h⟩ j
  · exact DyadicInterval.point_contains _

def coverTriangleInverseInterval : DyadicInterval :=
  ⟨125081438214321049219,125081438214321084530⟩

theorem coverTriangleInverse_checked :
    (apexRefinedPrimitiveIntervals 4).inv?=some coverTriangleInverseInterval := by decide +kernel

theorem coverTriangleInverse_contains : coverTriangleInverseInterval.contains criticalTriangle⁻¹ :=
  DyadicInterval.inv?_contains (apexRefinedPrimitiveIntervals_contains 4) coverTriangleInverse_checked

def nonapexMuInterval (j : Fin 36) : DyadicInterval :=
  (DyadicInterval.point (1-(nonapexVertexQ j).2-(nonapexVertexQ j).1)).mul
    coverTriangleInverseInterval

theorem nonapexMuInterval_contains (j : Fin 36) :
    (nonapexMuInterval j).contains (relaxationMultiplier (nonapexVertex j)) := by
  have hh := DyadicInterval.mul_contains
    (DyadicInterval.point_contains (1-(nonapexVertexQ j).2-(nonapexVertexQ j).1))
    coverTriangleInverse_contains
  simpa only [Rat.cast_sub,Rat.cast_one,nonapexVertex,relaxationMultiplier,div_eq_mul_inv] using hh

def nonapexConstantIntervals (j : Fin 36) : Fin 5 → DyadicInterval :=
  ![apexRefinedPrimitiveIntervals 4,apexRefinedPrimitiveIntervals 5,nonapexMuInterval j,
    DyadicInterval.point (nonapexVertexQ j).1,DyadicInterval.point (nonapexVertexQ j).2]

theorem nonapexConstantIntervals_contains (j : Fin 36) (k : Fin 5) :
    (nonapexConstantIntervals j k).contains (coverConstantValues (nonapexVertex j) k) := by
  fin_cases k
  · exact apexRefinedPrimitiveIntervals_contains 4
  · exact apexRefinedPrimitiveIntervals_contains 5
  · exact nonapexMuInterval_contains j
  · exact DyadicInterval.point_contains _
  · exact DyadicInterval.point_contains _

def nonapexBoxIntervals (C : ApexFanBox) (j : Fin 36) : Fin 24 → DyadicInterval :=
  coverBoxIntervals C (nonapexConstantIntervals j) (coverCellThetaIntervals (nonapexCell j))
    (DyadicInterval.point (cellLambdaQ (nonapexCell j)))

theorem nonapexBoxIntervals_contains (C : ApexFanBox) (hC : C.Valid) (j : Fin 36)
    {q : ApexVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ)) :
    ∀k,(nonapexBoxIntervals C j k).contains
      (coverVariables (coverCellTheta (nonapexCell j)) (cellLambda (nonapexCell j)) (nonapexVertex j) q k) := by
  apply coverBoxIntervals_contains C hC (nonapexConstantIntervals_contains j)
    (coverCellThetaIntervals_contains (nonapexCell j)) _ hq
  rw [←cellLambdaQ_cast]
  exact DyadicInterval.point_contains _

theorem nonapexBox_positive (C : ApexFanBox) (hC : C.Valid) (j : Fin 36)
    (hpos : 0<(apexCertificateExpr.dyadicEval (nonapexBoxIntervals C j)).lower)
    {q : ApexVector} (hq : ∀i,Bounds (q i) ((C.qLower i).q : ℝ) ((C.qUpper i).q : ℝ)) :
    0<coverPhi (coverCellTheta (nonapexCell j)) (cellLambda (nonapexCell j)) (nonapexVertex j) q := by
  have hb := (apexCertificateExpr.dyadicEval_contains (nonapexBoxIntervals_contains C hC j hq)).1
  have hp : 0<((apexCertificateExpr.dyadicEval (nonapexBoxIntervals C j)).lower : ℝ)/
      DyadicInterval.scale := div_pos (by exact_mod_cast hpos) DyadicInterval.scale_real_pos
  have hh := hp.trans_le hb
  simpa only [coverVariables,coverCertificateExpr_realEval,coverPhi] using hh

end SparseLowerTail.Section05.RefinedCover

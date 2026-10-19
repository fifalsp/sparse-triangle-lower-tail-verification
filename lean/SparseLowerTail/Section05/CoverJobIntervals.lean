import SparseLowerTail.Section05.ApexFanBoxIntervals
import SparseLowerTail.Section05.CoverGenericTaylor

/-! Actual coefficient and environment enclosures for all nonapex jobs.
Fan vertices use the exact tangency solution, never the table's null-slot
placeholders. The same box data can be used for direct or Taylor checks. -/
namespace SparseLowerTail.Section05
open Numerics Certificate CoverGeometry

noncomputable def coverCellTheta (i : Fin 12) : Fin 12 → ℝ :=
  if h : i.val<6 then apexFanTheta ⟨i.val,h⟩ else fixedCellTheta i

def coverCellThetaIntervals (i : Fin 12) : Fin 12 → DyadicInterval :=
  if h : i.val<6 then apexFanCoefficientIntervals ⟨i.val,h⟩
  else fun j => DyadicInterval.point (fixedCellThetaQ i j)

theorem coverCellThetaIntervals_contains (i : Fin 12) (j : Fin 12) :
    (coverCellThetaIntervals i j).contains (coverCellTheta i j) := by
  unfold coverCellThetaIntervals coverCellTheta
  split_ifs with h
  · exact apexFanCoefficientIntervals_contains ⟨i.val,h⟩ j
  · exact DyadicInterval.point_contains _

theorem coverCellTheta_fan (i : Fin 6) : coverCellTheta (i.castAdd 6)=apexFanTheta i := by
  simp [coverCellTheta,i.isLt]

def coverTriangleInverseInterval : DyadicInterval :=
  ⟨125081438060515331874,125081438264068228643⟩

theorem coverTriangleInverse_checked :
    (apexPrimitiveIntervals 4).inv?=some coverTriangleInverseInterval := by decide +kernel

theorem coverTriangleInverse_contains : coverTriangleInverseInterval.contains criticalTriangle⁻¹ :=
  DyadicInterval.inv?_contains (apexPrimitiveIntervals_contains 4) coverTriangleInverse_checked

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
  ![apexPrimitiveIntervals 4,apexPrimitiveIntervals 5,nonapexMuInterval j,
    DyadicInterval.point (nonapexVertexQ j).1,DyadicInterval.point (nonapexVertexQ j).2]

/-- The five constant slots are triangle, omega, multiplier, mean, and cost. -/
noncomputable def coverConstantValues (π : ℝ×ℝ) : Fin 5 → ℝ :=
  ![criticalTriangle,criticalOmega,relaxationMultiplier π,π.1,π.2]

theorem nonapexConstantIntervals_contains (j : Fin 36) (k : Fin 5) :
    (nonapexConstantIntervals j k).contains (coverConstantValues (nonapexVertex j) k) := by
  fin_cases k
  · exact apexPrimitiveIntervals_contains 4
  · exact apexPrimitiveIntervals_contains 5
  · exact nonapexMuInterval_contains j
  · exact DyadicInterval.point_contains _
  · exact DyadicInterval.point_contains _

/-- Endpoint boxes have no coefficient dependence. All job-specific constants
are supplied separately, so this enclosure works at arbitrary vertices. -/
def coverBoxIntervals (C : ApexFanBox) (constant : Fin 5 → DyadicInterval)
    (theta : Fin 12 → DyadicInterval) (lam : DyadicInterval) : Fin 24 → DyadicInterval :=
  ![C.qInterval 0,C.qInterval 1,C.qInterval 2,C.xInterval 0,C.xInterval 1,C.xInterval 2,
    constant 0,constant 1,constant 2,constant 3,constant 4,
    theta 0,theta 1,theta 2,theta 3,theta 4,theta 5,theta 6,theta 7,theta 8,theta 9,theta 10,theta 11,lam]

theorem coverBoxIntervals_contains (C : ApexFanBox) (hC : C.Valid)
    {θ : Fin 12 → ℝ} {lam : ℝ} {π : ℝ×ℝ}
    {constant : Fin 5 → DyadicInterval} {theta : Fin 12 → DyadicInterval} {lamI : DyadicInterval}
    (hc : ∀k,(constant k).contains (coverConstantValues π k))
    (ht : ∀k,(theta k).contains (θ k)) (hl : lamI.contains lam)
    {q : ApexVector} (hq : ∀j,Bounds (q j) ((C.qLower j).q : ℝ) ((C.qUpper j).q : ℝ)) :
    ∀k,(coverBoxIntervals C constant theta lamI k).contains (coverVariables θ lam π q k) := by
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
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hc 3
  · exact hc 4
  · exact ht 0
  · exact ht 1
  · exact ht 2
  · exact ht 3
  · exact ht 4
  · exact ht 5
  · exact ht 6
  · exact ht 7
  · exact ht 8
  · exact ht 9
  · exact ht 10
  · exact ht 11
  · exact hl

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

end SparseLowerTail.Section05

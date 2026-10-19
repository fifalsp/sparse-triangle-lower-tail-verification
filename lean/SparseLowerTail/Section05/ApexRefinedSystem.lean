import SparseLowerTail.Section05.ApexRefinedPrimitives
import SparseLowerTail.Numerics.MatrixInterval4

/-! One kernel-checked determinant enclosure proves invertibility of the common
apex tangency matrix. Each entry is checked separately to keep replay small. -/
namespace SparseLowerTail.Section05.RefinedApex
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def apexTangencyMatrixIntervals : Fin 4 → Fin 4 → DyadicInterval :=
  ![![⟨479795735026678575,479795735026678600⟩,⟨-519753682158485487,-519753682158485409⟩,⟨4691546597025133171,4691546597025133398⟩,⟨79915894263613707,79915894263613734⟩],![⟨6546295636981791,6546295636981794⟩,⟨-26660069241363357,-26660069241363344⟩,⟨386824227746952600,386824227746952605⟩,⟨-20049460143905234,-20049460143905222⟩],![⟨6546295636981791,6546295636981794⟩,⟨-26660069241363357,-26660069241363344⟩,⟨509812301339648605,509812301339648658⟩,⟨139782328383322180,139782328383322248⟩],![⟨326410118988100845,326410118988100857⟩,⟨-53298700662567942,-53298700662567906⟩,⟨3576015995893389185,3576015995893389763⟩,⟨433007520313236653,433007520313236745⟩]]

theorem apexTangencyMatrixIntervals_checked (i j : Fin 4) :
    (apexTangencyMatrixExpr i j).dyadicEval apexRefinedPrimitiveIntervals=
      some (apexTangencyMatrixIntervals i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem apexTangencyMatrixIntervals_contains (i j : Fin 4) :
    (apexTangencyMatrixIntervals i j).contains (apexTangencyMatrix i j) := by
  rw [←apexTangencyMatrixExpr_eval]
  exact RationalExpr.dyadicEval_contains _ apexRefinedPrimitiveIntervals_contains
    (apexTangencyMatrixIntervals_checked i j)

def apexTangencyDetInterval : DyadicInterval :=
  ⟨5186330360641586,5186330360641654⟩

theorem apexTangencyDetInterval_checked :
    matrixDetInterval4 apexTangencyMatrixIntervals=some apexTangencyDetInterval := by
  decide +kernel

theorem apexTangencyDetInterval_apart : apexTangencyDetInterval.ApartZero := by
  decide +kernel

theorem apexTangencyMatrix_det_ne_zero : apexTangencyMatrix.det≠0 :=
  matrixDet_ne_zero_of_interval apexTangencyMatrixIntervals_contains
    apexTangencyDetInterval_checked apexTangencyDetInterval_apart

/-- No determinant hypothesis remains in the exact tangency construction. -/
theorem apexExactCoefficients_tangent_checked (base : Fin 12 → ℚ) (lam : ℚ) :
    apexTangencyResidual (apexExactCoefficients base lam) (lam : ℝ)=0 :=
  apexExactCoefficients_tangent base lam apexTangencyMatrix_det_ne_zero

theorem apexExactCoefficients_contacts_checked (base : Fin 12 → ℚ) (lam : ℚ) :
    (apexPhi (apexExactCoefficients base lam) (lam : ℝ) apexContactAAA=0 ∧
      ∀i,apexGradient (apexExactCoefficients base lam) (lam : ℝ) apexContactAAA i=0) ∧
    (apexPhi (apexExactCoefficients base lam) (lam : ℝ) apexContactABB=0 ∧
      ∀i,apexGradient (apexExactCoefficients base lam) (lam : ℝ) apexContactABB i=0) :=
  apexExactCoefficients_contacts base lam apexTangencyMatrix_det_ne_zero

end SparseLowerTail.Section05.RefinedApex

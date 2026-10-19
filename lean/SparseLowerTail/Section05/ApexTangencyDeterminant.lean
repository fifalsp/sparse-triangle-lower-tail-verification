import SparseLowerTail.Section05.ApexPrimitiveIntervals
import SparseLowerTail.Numerics.MatrixInterval4

/-! One kernel-checked determinant enclosure proves invertibility of the common
apex tangency matrix. Each entry is checked separately to keep replay small. -/
namespace SparseLowerTail.Section05
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def apexTangencyMatrixIntervals : Fin 4 → Fin 4 → DyadicInterval :=
  ![![⟨479795735012655039,479795735093359548⟩,⟨-519753682367064961,-519753681950922730⟩,⟨4691546596558132293,4691546597257663502⟩,⟨79915894240480285,79915894299311586⟩],![⟨6546295635738446,6546295639581519⟩,⟨-26660069257095135,-26660069229830137⟩,⟨386824227744711315,386824227749896845⟩,⟨-20049460157094185,-20049460133527177⟩],![⟨6546295635738446,6546295639581519⟩,⟨-26660069257095135,-26660069229830137⟩,⟨509812301250613971,509812301450271275⟩,⟨139782328270985601,139782328536298626⟩],![⟨326410118985194616,326410119023625335⟩,⟨-53298700711128189,-53298700585558181⟩,⟨3576015994195585428,3576015997804559551⟩,⟨433007520191620544,433007520539402572⟩]]

theorem apexTangencyMatrixIntervals_checked (i j : Fin 4) :
    (apexTangencyMatrixExpr i j).dyadicEval apexPrimitiveIntervals=
      some (apexTangencyMatrixIntervals i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem apexTangencyMatrixIntervals_contains (i j : Fin 4) :
    (apexTangencyMatrixIntervals i j).contains (apexTangencyMatrix i j) := by
  rw [←apexTangencyMatrixExpr_eval]
  exact RationalExpr.dyadicEval_contains _ apexPrimitiveIntervals_contains
    (apexTangencyMatrixIntervals_checked i j)

def apexTangencyDetInterval : DyadicInterval := ⟨5186330326774856,5186330397267159⟩

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

end SparseLowerTail.Section05

import SparseLowerTail.Section05.ApexContactValues
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The four exact tangency equations used by F1--F6. The coefficients left
unspecified in the printed tables must be the exact solution of this system.
The determinant enclosure remains a numerical obligation. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05
open Numerics Certificate Section04

def apexContactAAA : ApexVector := fun _ => -Real.log criticalA

def apexContactABB : ApexVector := ![-Real.log criticalA,-Real.log criticalB,-Real.log criticalB]

theorem apexContactAAA_edges : logBoxEdges ((apexContactAAA 0,apexContactAAA 1),apexContactAAA 2)=apexAAA := by
  have ha : 0<criticalA := branchA_pos transitionParameter_mem_Ioo.1
  simp only [logBoxEdges,apexContactAAA,neg_neg,Real.exp_log ha,apexAAA]

theorem apexContactABB_edges : logBoxEdges ((apexContactABB 0,apexContactABB 1),apexContactABB 2)=apexABB := by
  have ha : 0<criticalA := branchA_pos transitionParameter_mem_Ioo.1
  have hb : 0<criticalB := branchB_pos transitionParameter
  simp only [logBoxEdges,apexContactABB,Matrix.cons_val,neg_neg,Real.exp_log ha,Real.exp_log hb,apexABB]

theorem apexPhi_ABB_zero_of_AAA {θ : Fin 12 → ℝ} {lam : ℝ}
    (h : apexPhi θ lam apexContactAAA=0) : apexPhi θ lam apexContactABB=0 := by
  simp only [apexPhi,logCertificate,apexContactAAA_edges] at h
  simp only [apexPhi,logCertificate,apexContactABB_edges]
  exact apexCertificate_ABB_zero_of_AAA h

def apexCoordinate (i : Fin 3) : ApexVector := fun j => if j=i then 1 else 0

theorem apexPhi_coordinate_deriv (θ : Fin 12 → ℝ) (lam : ℝ) (p : ApexVector) (i : Fin 3) :
    HasDerivAt (fun t => apexPhi θ lam (familySegment p (apexCoordinate i) t))
      (apexGradient θ lam p i) 0 := by
  have h := apexPhi_segment_deriv θ lam p (apexCoordinate i) 0
  fin_cases i <;> simpa [familySegment_zero,sumThree,apexCoordinate] using h

/-- Linearity jointly in coefficient vector and Hoeffding multiplier. -/
theorem apexPhi_add (θ φ : Fin 12 → ℝ) (lam mu : ℝ) (q : ApexVector) :
    apexPhi (θ+φ) (lam+mu) q=apexPhi θ lam q+apexPhi φ mu q := by
  simp only [apexPhi,logCertificate,coverCertificate,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  ring

theorem apexPhi_smul (c : ℝ) (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) :
    apexPhi (c • θ) (c*lam) q=c*apexPhi θ lam q := by
  simp only [apexPhi,logCertificate,coverCertificate,Pi.smul_apply,smul_eq_mul,
    mul_assoc,←Finset.mul_sum]
  ring

theorem apexGradient_add (θ φ : Fin 12 → ℝ) (lam mu : ℝ) (q : ApexVector) (i : Fin 3) :
    apexGradient (θ+φ) (lam+mu) q i=apexGradient θ lam q i+apexGradient φ mu q i := by
  have h := (apexPhi_coordinate_deriv θ lam q i).add (apexPhi_coordinate_deriv φ mu q i)
  have hfun : (fun t => apexPhi (θ+φ) (lam+mu) (familySegment q (apexCoordinate i) t))=
      (fun t => apexPhi θ lam (familySegment q (apexCoordinate i) t)+
        apexPhi φ mu (familySegment q (apexCoordinate i) t)) := by
    funext t
    exact apexPhi_add θ φ lam mu _
  have h' := apexPhi_coordinate_deriv (θ+φ) (lam+mu) q i
  rw [hfun] at h'
  exact h'.unique h

theorem apexGradient_smul (c : ℝ) (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) (i : Fin 3) :
    apexGradient (c • θ) (c*lam) q i=c*apexGradient θ lam q i := by
  have h := (apexPhi_coordinate_deriv θ lam q i).const_mul c
  have hfun : (fun t => apexPhi (c • θ) (c*lam) (familySegment q (apexCoordinate i) t))=
      (fun t => c*apexPhi θ lam (familySegment q (apexCoordinate i) t)) := by
    funext t
    exact apexPhi_smul c θ lam _
  have h' := apexPhi_coordinate_deriv (c • θ) (c*lam) q i
  rw [hfun] at h'
  exact h'.unique h

/-- The original four equations: AAA value, AAA first derivative, and the two
inequivalent ABB derivatives. -/
def apexTangencyResidual (θ : Fin 12 → ℝ) (lam : ℝ) : Fin 4 → ℝ :=
  ![apexPhi θ lam apexContactAAA,apexGradient θ lam apexContactAAA 0,
    apexGradient θ lam apexContactABB 0,apexGradient θ lam apexContactABB 1]

theorem apexTangencyResidual_add (θ φ : Fin 12 → ℝ) (lam mu : ℝ) :
    apexTangencyResidual (θ+φ) (lam+mu)=apexTangencyResidual θ lam+apexTangencyResidual φ mu := by
  funext i
  fin_cases i
  · exact apexPhi_add θ φ lam mu _
  · exact apexGradient_add θ φ lam mu _ _
  · exact apexGradient_add θ φ lam mu _ _
  · exact apexGradient_add θ φ lam mu _ _

theorem apexTangencyResidual_smul (c : ℝ) (θ : Fin 12 → ℝ) (lam : ℝ) :
    apexTangencyResidual (c • θ) (c*lam)=c • apexTangencyResidual θ lam := by
  funext i
  fin_cases i
  · exact apexPhi_smul c θ lam _
  · exact apexGradient_smul c θ lam _ _
  · exact apexGradient_smul c θ lam _ _
  · exact apexGradient_smul c θ lam _ _

def apexUnknownIndex : Fin 4 → Fin 12 := ![0,2,3,4]

def apexCoefficientBasis (j : Fin 4) : Fin 12 → ℝ :=
  fun i => if i=apexUnknownIndex j then 1 else 0

def apexTangencyMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => apexTangencyResidual (apexCoefficientBasis j) 0 i

/-- Insert the four solved coefficients into a base vector whose unknown slots
are zero. The identity below actually holds for every base vector. -/
def apexSolvedCoefficients (base : Fin 12 → ℝ) (x : Fin 4 → ℝ) : Fin 12 → ℝ :=
  base+x 0 • apexCoefficientBasis 0+x 1 • apexCoefficientBasis 1+
    x 2 • apexCoefficientBasis 2+x 3 • apexCoefficientBasis 3

theorem apexTangencyResidual_add_zero (θ φ : Fin 12 → ℝ) (lam : ℝ) :
    apexTangencyResidual (θ+φ) lam=apexTangencyResidual θ lam+apexTangencyResidual φ 0 := by
  simpa only [add_zero] using apexTangencyResidual_add θ φ lam 0

theorem apexTangencyResidual_smul_zero (c : ℝ) (θ : Fin 12 → ℝ) :
    apexTangencyResidual (c • θ) 0=c • apexTangencyResidual θ 0 := by
  simpa only [mul_zero] using apexTangencyResidual_smul c θ 0

/-- Exact bridge from the actual certificate equations to a four-by-four
linear system. No invertibility, interval enclosure, or tangency is assumed. -/
theorem apexSolvedCoefficients_residual (base : Fin 12 → ℝ) (lam : ℝ) (x : Fin 4 → ℝ) :
    apexTangencyResidual (apexSolvedCoefficients base x) lam=
      apexTangencyResidual base lam+apexTangencyMatrix.mulVec x := by
  simp only [apexSolvedCoefficients,apexTangencyResidual_add_zero,apexTangencyResidual_smul_zero]
  funext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Fin.sum_univ_zero]
  change apexTangencyResidual base lam i+x 0*apexTangencyMatrix i 0+
    x 1*apexTangencyMatrix i 1+x 2*apexTangencyMatrix i 2+x 3*apexTangencyMatrix i 3 =
    apexTangencyResidual base lam i+(apexTangencyMatrix i 0*x 0+
    (apexTangencyMatrix i 1*x 1+(apexTangencyMatrix i 2*x 2+(apexTangencyMatrix i 3*x 3+0))))
  ring

/-- Any checked exact linear-system solution supplies the four tangencies. -/
theorem apexSolvedCoefficients_tangent (base : Fin 12 → ℝ) (lam : ℝ) {x : Fin 4 → ℝ}
    (hx : apexTangencyMatrix.mulVec x= -apexTangencyResidual base lam) :
    apexTangencyResidual (apexSolvedCoefficients base x) lam=0 := by
  rw [apexSolvedCoefficients_residual,hx,add_neg_cancel]

end SparseLowerTail.Section05

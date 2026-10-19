import SparseLowerTail.Section08.FamilyLocalDominance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The congruence step used by the family Hessian replay. An arbitrary
proposed matrix is permitted: strict positivity of its checked congruence
already forces it to be invertible. No floating-point eigenvector claim is
used. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Numerics

abbrev FamilyMatrix := Matrix (Fin 3) (Fin 3) ℝ

def familyQuadratic (H : FamilyMatrix) (v : FamilyVector) : ℝ :=
  sumThree (fun i => sumThree (fun j => v i*v j*H i j))

def familyCongruence (H T : FamilyMatrix) : FamilyMatrix := T.transpose*H*T

@[simp] theorem familyQuadratic_zero (H : FamilyMatrix) : familyQuadratic H 0=0 := by
  simp [familyQuadratic,sumThree]

/-- Exact expansion of the matrix congruence; this is the bridge from the
interval replay's transformed matrix to the original quadratic form. -/
theorem familyQuadratic_congruence (H T : FamilyMatrix) (v : FamilyVector) :
    familyQuadratic (familyCongruence H T) v=familyQuadratic H (T.mulVec v) := by
  simp only [familyQuadratic,familyCongruence,sumThree,Matrix.mul_apply,
    Matrix.mulVec,dotProduct,Matrix.transpose_apply,Fin.sum_univ_three]
  ring

/-- Strict positivity of a square congruence automatically supplies the
missing invertibility of the proposed change of coordinates. -/
theorem familyCongruence_mulVec_surjective (H T : FamilyMatrix)
    (hpos : ∀v : FamilyVector,v≠0 → 0<familyQuadratic (familyCongruence H T) v) :
    Function.Surjective T.mulVec := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w he
  by_contra hne
  have hp := hpos (v-w) (sub_ne_zero.mpr hne)
  rw [familyQuadratic_congruence,Matrix.mulVec_sub,he,sub_self,
    familyQuadratic_zero] at hp
  exact (lt_irrefl 0) hp

/-- Symmetry is preserved by any square congruence. -/
theorem familyCongruence_symmetric (H T : FamilyMatrix)
    (hH : ∀i j,H i j=H j i) (i j : Fin 3) :
    familyCongruence H T i j=familyCongruence H T j i := by
  have ht : H.transpose=H := by
    funext i j
    exact hH j i
  have hh : (familyCongruence H T).transpose=familyCongruence H T := by
    simp only [familyCongruence,Matrix.transpose_mul,Matrix.transpose_transpose,
      ht,Matrix.mul_assoc]
  exact (congrFun (congrFun hh i) j).symm

/-- Only positivity of the checked congruence is needed; the proposed
matrix requires no separate condition. -/
theorem familyQuadratic_pos_of_congruence (H T : FamilyMatrix)
    (hpos : ∀v : FamilyVector,v≠0 → 0<familyQuadratic (familyCongruence H T) v)
    {v : FamilyVector} (hv : v≠0) : 0<familyQuadratic H v := by
  obtain ⟨w,hw⟩ := familyCongruence_mulVec_surjective H T hpos v
  have hw0 : w≠0 := by
    intro he
    subst w
    simp only [Matrix.mulVec_zero] at hw
    exact hv hw.symm
  have hp := hpos w hw0
  rwa [familyQuadratic_congruence,hw] at hp

/-- Scalar diagonal-dominance checks on the proposed congruence certify
strict positivity of the original matrix. -/
theorem familyQuadratic_pos_of_congruence_dominance (H T : FamilyMatrix) {η : ℝ}
    (hη : 0<η)
    (hs01 : familyCongruence H T 1 0=familyCongruence H T 0 1)
    (hs02 : familyCongruence H T 2 0=familyCongruence H T 0 2)
    (hs12 : familyCongruence H T 2 1=familyCongruence H T 1 2)
    (h0 : η+|familyCongruence H T 0 1|+|familyCongruence H T 0 2|≤familyCongruence H T 0 0)
    (h1 : η+|familyCongruence H T 0 1|+|familyCongruence H T 1 2|≤familyCongruence H T 1 1)
    (h2 : η+|familyCongruence H T 0 2|+|familyCongruence H T 1 2|≤familyCongruence H T 2 2)
    {v : FamilyVector} (hv : v≠0) : 0<familyQuadratic H v := by
  apply familyQuadratic_pos_of_congruence H T (v := v) (hv := hv)
  intro w hw
  exact (mul_pos hη (familyNormSq_pos hw)).trans_le
    (quadratic_lower_of_diagonal_dominance _ η hs01 hs02 hs12 h0 h1 h2 w)

end SparseLowerTail.Certificate

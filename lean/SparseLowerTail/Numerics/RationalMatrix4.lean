import SparseLowerTail.Numerics.RationalExpr
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact four-dimensional linear solves for tangency certificates. The
rational expressions are checked against Cramer's rule, and interval bounds
must certify that the actual determinant is separated from zero. -/
namespace SparseLowerTail.Numerics
namespace RationalExpr

def det3 {n : ℕ} (A : Fin 3 → Fin 3 → RationalExpr n) : RationalExpr n :=
  A 0 0*A 1 1*A 2 2-A 0 0*A 1 2*A 2 1-A 0 1*A 1 0*A 2 2+
    A 0 1*A 1 2*A 2 0+A 0 2*A 1 0*A 2 1-A 0 2*A 1 1*A 2 0

def minor4 {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n) (j : Fin 4) :
    Fin 3 → Fin 3 → RationalExpr n := fun i k => A i.succ (j.succAbove k)

def det4 {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n) : RationalExpr n :=
  A 0 0*det3 (minor4 A 0)-A 0 1*det3 (minor4 A 1)+
    A 0 2*det3 (minor4 A 2)-A 0 3*det3 (minor4 A 3)

noncomputable def matrixEval {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (x : Fin n → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => (A i j).realEval x

theorem det3_eval {n : ℕ} (A : Fin 3 → Fin 3 → RationalExpr n) (x : Fin n → ℝ) :
    (det3 A).realEval x = Matrix.det (fun i j => (A i j).realEval x) := by
  rw [Matrix.det_fin_three]
  simp only [det3,realEval_add,realEval_sub,realEval_mul]

theorem det4_eval {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n) (x : Fin n → ℝ) :
    (det4 A).realEval x = (matrixEval A x).det := by
  rw [Matrix.det_succ_row_zero]
  simp only [det4,realEval_add,realEval_sub,realEval_mul,det3_eval,
    Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ]
  norm_num [matrixEval,minor4,Matrix.submatrix]
  let f : Fin 4 → ℝ := fun j => (A 0 j).realEval x *
    Matrix.det (fun i k : Fin 3 => (A i.succ (j.succAbove k)).realEval x)
  change f 0-f 1+f 2-f 3=f 0+(-f 1+(f 2+ -f 3))
  ring

def replaceColumn4 {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (b : Fin 4 → RationalExpr n) (k : Fin 4) : Fin 4 → Fin 4 → RationalExpr n :=
  fun i j => if j=k then b i else A i j

def cramer4 {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (b : Fin 4 → RationalExpr n) (i : Fin 4) : RationalExpr n :=
  det4 (replaceColumn4 A b i)/det4 A

theorem replaceColumn4_eval {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (b : Fin 4 → RationalExpr n) (k : Fin 4) (x : Fin n → ℝ) :
    matrixEval (replaceColumn4 A b k) x =
      (matrixEval A x).updateCol k (fun i => (b i).realEval x) := by
  funext i j
  simp only [matrixEval,replaceColumn4,Matrix.updateCol_apply]
  split_ifs <;> rfl

theorem cramer4_eval {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (b : Fin 4 → RationalExpr n) (i : Fin 4) (x : Fin n → ℝ) :
    (cramer4 A b i).realEval x =
      Matrix.cramer (matrixEval A x) (fun j => (b j).realEval x) i/(matrixEval A x).det := by
  simp only [cramer4,realEval_div,det4_eval,replaceColumn4_eval,Matrix.cramer_apply]

/-- The exact rational expression vector solves the actual system. -/
theorem cramer4_solves {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (b : Fin 4 → RationalExpr n) (x : Fin n → ℝ) (hd : (matrixEval A x).det≠0) :
    (matrixEval A x).mulVec (fun i => (cramer4 A b i).realEval x) =
      fun i => (b i).realEval x := by
  have he : (fun i => (cramer4 A b i).realEval x) =
      (matrixEval A x).det⁻¹ • Matrix.cramer (matrixEval A x) (fun i => (b i).realEval x) := by
    funext i
    simp only [cramer4_eval,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [he,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hd,one_smul]

/-- Any solution must be the checked Cramer vector. -/
theorem cramer4_unique {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (b : Fin 4 → RationalExpr n) (x : Fin n → ℝ) (hd : (matrixEval A x).det≠0)
    {v : Fin 4 → ℝ} (hv : (matrixEval A x).mulVec v=fun i => (b i).realEval x) :
    v=fun i => (cramer4 A b i).realEval x := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det (matrixEval A x)).mpr (isUnit_iff_ne_zero.mpr hd)))
  exact hv.trans (cramer4_solves A b x hd).symm

end RationalExpr

namespace DyadicInterval

def ApartZero (I : DyadicInterval) : Prop := 0<I.lower ∨ I.upper<0
instance (I : DyadicInterval) : Decidable I.ApartZero := inferInstanceAs (Decidable (_∨_))

theorem ne_zero_of_contains {I : DyadicInterval} {x : ℝ}
    (hI : I.ApartZero) (hx : I.contains x) : x≠0 := by
  rcases hI with hp | hn
  · exact ne_of_gt ((div_pos (by exact_mod_cast hp) scale_real_pos).trans_le hx.1)
  · exact ne_of_lt (hx.2.trans_lt (div_neg_of_neg_of_pos (by exact_mod_cast hn) scale_real_pos))
end DyadicInterval

namespace RationalExpr

theorem det4_ne_zero_of_interval {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    {x : Fin n → ℝ} {box : Fin n → DyadicInterval} {I : DyadicInterval}
    (hx : ∀i,(box i).contains (x i))
    (he : (det4 A).dyadicEval box=some I) (hI : I.ApartZero) :
    (matrixEval A x).det≠0 := by
  apply DyadicInterval.ne_zero_of_contains hI
  rw [←det4_eval]
  exact dyadicEval_contains (det4 A) hx he

theorem cramer4_interval {n : ℕ} (A : Fin 4 → Fin 4 → RationalExpr n)
    (b : Fin 4 → RationalExpr n) {x : Fin n → ℝ} {box : Fin n → DyadicInterval}
    {D I : DyadicInterval} (hx : ∀i,(box i).contains (x i))
    (hD : (det4 A).dyadicEval box=some D) (hn : D.ApartZero)
    {v : Fin 4 → ℝ} (hv : (matrixEval A x).mulVec v=fun i => (b i).realEval x)
    (i : Fin 4) (he : (cramer4 A b i).dyadicEval box=some I) : I.contains (v i) := by
  rw [cramer4_unique A b x (det4_ne_zero_of_interval A hx hD hn) hv]
  exact dyadicEval_contains (cramer4 A b i) hx he

end RationalExpr
end SparseLowerTail.Numerics

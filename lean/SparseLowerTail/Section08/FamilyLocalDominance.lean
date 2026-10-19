import SparseLowerTail.Section08.FamilyLocalBridge

/-! A three-dimensional diagonal-dominance bridge for the local Hessian
replay. Every input is an explicit scalar matrix-entry inequality. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Numerics

/-- The two off-diagonal contributions can be paid for by the corresponding
absolute-value diagonal terms. -/
theorem offDiagonal_square_bound (a x y : ℝ) :
    0≤|a| *(x^2+y^2)+2*a*x*y := by
  by_cases ha : 0≤a
  · rw [abs_of_nonneg ha]
    have h := mul_nonneg ha (sq_nonneg (x+y))
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge ha)]
    have h := mul_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) (sq_nonneg (x-y))
    nlinarith

/-- The squared Euclidean norm used by the family replay is positive away
from the zero vector. -/
theorem familyNormSq_pos {v : FamilyVector} (hv : v≠0) : 0<familyNormSq v := by
  have he : ∃i,v i≠0 := by
    by_contra h
    apply hv
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i,hi⟩ := he
  have hp := sq_pos_of_ne_zero hi
  fin_cases i
  · change 0 < (v 0)^2 at hp
    simp only [familyNormSq,sumThree]
    nlinarith [sq_nonneg (v 1),sq_nonneg (v 2)]
  · change 0 < (v 1)^2 at hp
    simp only [familyNormSq,sumThree]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 2)]
  · change 0 < (v 2)^2 at hp
    simp only [familyNormSq,sumThree]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]

/-- Quantitative Gershgorin bound, expanded in dimension three. Symmetry is
needed only in the three off-diagonal positions. -/
theorem quadratic_lower_of_diagonal_dominance
    (H : Fin 3→Fin 3→ℝ) (η : ℝ)
    (hs01 : H 1 0=H 0 1) (hs02 : H 2 0=H 0 2) (hs12 : H 2 1=H 1 2)
    (h0 : η+|H 0 1|+|H 0 2|≤H 0 0)
    (h1 : η+|H 0 1|+|H 1 2|≤H 1 1)
    (h2 : η+|H 0 2|+|H 1 2|≤H 2 2) (v : FamilyVector) :
    η*familyNormSq v≤sumThree (fun i => sumThree (fun j => v i*v j*H i j)) := by
  have hd0 := mul_nonneg (sub_nonneg.mpr h0) (sq_nonneg (v 0))
  have hd1 := mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg (v 1))
  have hd2 := mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg (v 2))
  have ho01 := offDiagonal_square_bound (H 0 1) (v 0) (v 1)
  have ho02 := offDiagonal_square_bound (H 0 2) (v 0) (v 2)
  have ho12 := offDiagonal_square_bound (H 1 2) (v 1) (v 2)
  simp only [familyNormSq,sumThree,hs01,hs02,hs12]
  nlinarith

theorem familyHessian_symmetric (z : ℝ) (q : FamilyVector) (i j : Fin 3) :
    familyHessian z q i j=familyHessian z q j i := by
  rw [familyHessian_formula,familyHessian_formula]
  by_cases he : i=j
  · subst j; rfl
  · rw [if_neg he,if_neg (Ne.symm he)]
    unfold familyHessianOffDiagonal
    ring

/-- A directly checked row-sum margin supplies the actual Hessian
quadratic-form bound required by `familyPhi_local_quadratic_lower`. -/
theorem familyHessian_lower_of_diagonal_dominance (z : ℝ) (q : FamilyVector) (η : ℝ)
    (h0 : η+|familyHessian z q 0 1|+|familyHessian z q 0 2|≤familyHessian z q 0 0)
    (h1 : η+|familyHessian z q 0 1|+|familyHessian z q 1 2|≤familyHessian z q 1 1)
    (h2 : η+|familyHessian z q 0 2|+|familyHessian z q 1 2|≤familyHessian z q 2 2)
    (v : FamilyVector) : η*familyNormSq v≤familyHessianForm z q v := by
  exact quadratic_lower_of_diagonal_dominance _ η
    (familyHessian_symmetric z q 1 0) (familyHessian_symmetric z q 2 0)
    (familyHessian_symmetric z q 2 1) h0 h1 h2 v

/-- Positive row-sum margins prove strict positivity for every nonzero
actual displacement; there is no certificate-positivity assumption. -/
theorem familyHessian_pos_of_diagonal_dominance (z : ℝ) (q : FamilyVector) {η : ℝ}
    (hη : 0<η)
    (h0 : η+|familyHessian z q 0 1|+|familyHessian z q 0 2|≤familyHessian z q 0 0)
    (h1 : η+|familyHessian z q 0 1|+|familyHessian z q 1 2|≤familyHessian z q 1 1)
    (h2 : η+|familyHessian z q 0 2|+|familyHessian z q 1 2|≤familyHessian z q 2 2)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  (mul_pos hη (familyNormSq_pos hv)).trans_le
    (familyHessian_lower_of_diagonal_dominance z q η h0 h1 h2 v)

end SparseLowerTail.Certificate

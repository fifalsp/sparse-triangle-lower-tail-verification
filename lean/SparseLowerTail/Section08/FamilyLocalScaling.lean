import SparseLowerTail.Section08.FamilyLocalCongruence

/-! Exact exponential diagonal scaling of the actual family Hessian, as
used by `verification/family/core.py` with `scaled=True`. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Section04 Numerics

def familyHessianScaled (z : ℝ) (q : FamilyVector) : FamilyMatrix :=
  fun i j => Real.exp (q i/2)*familyHessian z q i j*Real.exp (q j/2)

def familyScaledVector (q v : FamilyVector) : FamilyVector :=
  fun i => Real.exp (-(q i/2))*v i

theorem familyHessianScaled_symmetric (z : ℝ) (q : FamilyVector) (i j : Fin 3) :
    familyHessianScaled z q i j=familyHessianScaled z q j i := by
  simp only [familyHessianScaled]
  rw [familyHessian_symmetric z q i j]
  ring

/-- Exact cancellation of the positive diagonal scaling. -/
theorem familyQuadratic_scaled (z : ℝ) (q v : FamilyVector) :
    familyQuadratic (familyHessianScaled z q) (familyScaledVector q v)=
      familyHessianForm z q v := by
  have he (i j : Fin 3) : familyScaledVector q v i*familyScaledVector q v j*
      familyHessianScaled z q i j=v i*v j*familyHessian z q i j := by
    simp only [familyScaledVector,familyHessianScaled,Real.exp_neg]
    field_simp
  simp only [familyQuadratic,familyHessianForm,he]

/-- Positivity of the scaled Hessian transfers to the actual Hessian. -/
theorem familyHessian_pos_of_scaled (z : ℝ) (q : FamilyVector)
    (hpos : ∀v : FamilyVector,v≠0 → 0<familyQuadratic (familyHessianScaled z q) v)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  have hn : familyScaledVector q v≠0 := by
    intro he
    apply hv
    funext i
    have hh := congrFun he i
    change Real.exp (-(q i/2))*v i=0 at hh
    exact (mul_eq_zero.mp hh).resolve_left (Real.exp_ne_zero _)
  simpa only [familyQuadratic_scaled] using hpos _ hn

/-- The scaled diagonal entry with the other two indices displayed. -/
def familyScaledDiagonal (z : ℝ) (q : FamilyVector) (i j k : Fin 3) : ℝ :=
  c1 z+c2 z*(2-q i)+c4 z*((q i)^2-4*q i+2)+
    branchMu z*c3 z*(Real.exp (-q j)+Real.exp (-q k))+
    Real.exp (-q j)*Real.exp (-q k)*
      (1+2*branchMu z*c4 z-branchMu z*c4 z*(q 0+q 1+q 2))

/-- The scaled off-diagonal entry with its remaining index displayed. -/
def familyScaledOffDiagonal (z : ℝ) (q : FamilyVector) (i j k : Fin 3) : ℝ :=
  Real.exp (-(q i+q j)/2)*(branchMu z*c3 z+Real.exp (-q k)*
    (1+2*branchMu z*c4 z-branchMu z*c4 z*(q 0+q 1+q 2)))

private theorem exp_neg_eq_half_inv_sq (t : ℝ) :
    Real.exp (-t)=(Real.exp (t/2)^2)⁻¹ := by
  rw [← Real.exp_nat_mul,← Real.exp_neg]
  congr 1
  norm_num
  ring

private theorem exp_neg_add_half (s t : ℝ) :
    Real.exp (-(s+t)/2)=(Real.exp (s/2)*Real.exp (t/2))⁻¹ := by
  rw [← Real.exp_add,← Real.exp_neg]
  congr 1
  ring

theorem familyHessianScaled_diagonal_formula (z : ℝ) (q : FamilyVector)
    (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    familyHessianScaled z q i i=familyScaledDiagonal z q i j k := by
  unfold familyHessianScaled
  rw [familyHessian_formula,if_pos rfl]
  simp only [familyHessianDiagonal,familyHessianCommon,familyScaledDiagonal]
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try exact (hij rfl).elim
  all_goals try exact (hik rfl).elim
  all_goals try exact (hjk rfl).elim
  all_goals simp only [Fin.mk_zero,Fin.mk_one,
    show (⟨2,by decide⟩ : Fin 3)=2 from rfl]
  all_goals simp only [exp_neg_eq_half_inv_sq]
  all_goals field_simp
  all_goals ring

theorem familyHessianScaled_offDiagonal_formula (z : ℝ) (q : FamilyVector)
    (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    familyHessianScaled z q i j=familyScaledOffDiagonal z q i j k := by
  unfold familyHessianScaled
  rw [familyHessian_formula,if_neg hij]
  simp only [familyHessianOffDiagonal,familyHessianCommon,familyScaledOffDiagonal]
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try exact (hij rfl).elim
  all_goals try exact (hik rfl).elim
  all_goals try exact (hjk rfl).elim
  all_goals simp only [Fin.mk_zero,Fin.mk_one,
    show (⟨2,by decide⟩ : Fin 3)=2 from rfl]
  all_goals simp only [exp_neg_add_half,exp_neg_eq_half_inv_sq]
  all_goals field_simp

/-- Complete analytic bridge for the scaled congruence replay. -/
theorem familyHessian_pos_of_scaled_congruence_dominance (z : ℝ) (q : FamilyVector)
    (T : FamilyMatrix) {η : ℝ} (hη : 0<η)
    (h0 : η+|familyCongruence (familyHessianScaled z q) T 0 1|+|familyCongruence (familyHessianScaled z q) T 0 2|≤familyCongruence (familyHessianScaled z q) T 0 0)
    (h1 : η+|familyCongruence (familyHessianScaled z q) T 0 1|+|familyCongruence (familyHessianScaled z q) T 1 2|≤familyCongruence (familyHessianScaled z q) T 1 1)
    (h2 : η+|familyCongruence (familyHessianScaled z q) T 0 2|+|familyCongruence (familyHessianScaled z q) T 1 2|≤familyCongruence (familyHessianScaled z q) T 2 2)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  apply familyHessian_pos_of_scaled z q (v := v) (hv := hv)
  intro w hw
  exact familyQuadratic_pos_of_congruence_dominance _ T hη
    (familyCongruence_symmetric _ T (familyHessianScaled_symmetric z q) 1 0)
    (familyCongruence_symmetric _ T (familyHessianScaled_symmetric z q) 2 0)
    (familyCongruence_symmetric _ T (familyHessianScaled_symmetric z q) 2 1) h0 h1 h2 hw

end SparseLowerTail.Certificate

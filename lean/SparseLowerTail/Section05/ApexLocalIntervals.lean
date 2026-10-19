import SparseLowerTail.Section05.ApexLocalBridge
import SparseLowerTail.Section08.FamilyLocalIntervalMatrix

/-! Dyadic matrix bounds for the actual apex Hessian. We use its symmetric
part, whose quadratic form is identical, so no unproved symmetry or mixed
partial identity is needed. The remaining row-margin checks are integer arithmetic. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05
open Numerics Certificate

def apexSymmetricHessian (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) : FamilyMatrix :=
  fun i j => (apexHessian θ lam q i j+apexHessian θ lam q j i)/2

theorem apexSymmetricHessian_symmetric (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) :
    ∀i j,apexSymmetricHessian θ lam q i j=apexSymmetricHessian θ lam q j i := by
  intro i j
  simp only [apexSymmetricHessian,add_comm]

theorem apexSymmetricHessian_form (θ : Fin 12 → ℝ) (lam : ℝ) (q v : ApexVector) :
    familyQuadratic (apexSymmetricHessian θ lam q) v=apexHessianForm θ lam q v := by
  simp only [familyQuadratic,apexSymmetricHessian,apexHessianForm,sumThree]
  ring

/-- A finite dyadic enclosure with positive congruence row margins proves
positive definiteness of the actual quadratic Hessian form. -/
theorem apexHessianForm_pos_of_interval_congruence (θ : Fin 12 → ℝ) (lam : ℝ)
    (q : ApexVector) (H : FamilyIntervalMatrix) (T : FamilyRationalMatrix)
    (hH : ∀i j,(H i j).contains (apexSymmetricHessian θ lam q i j))
    (hp : FamilyIntervalPositive (familyIntervalCongruence H T))
    {v : ApexVector} (hv : v≠0) : 0<apexHessianForm θ lam q v := by
  rw [←apexSymmetricHessian_form]
  exact familyQuadratic_pos_of_interval_congruence
    (apexSymmetricHessian_symmetric θ lam q) H T hH hp hv

/-- A single interval matrix enclosing a contact cube closes its local
positivity and zero classification, once exact tangency has been proved. -/
theorem apexPhi_cube_of_interval (θ : Fin 12 → ℝ) (lam : ℝ)
    (p : ApexVector) {δ : ℝ} (hδ : 0≤δ)
    (hval : apexPhi θ lam p=0) (hgrad : ∀i,apexGradient θ lam p i=0)
    (H : FamilyIntervalMatrix) (T : FamilyRationalMatrix)
    (hH : ∀q∈familyCube p δ,∀i j,(H i j).contains (apexSymmetricHessian θ lam q i j))
    (hp : FamilyIntervalPositive (familyIntervalCongruence H T))
    {q : ApexVector} (hq : q∈familyCube p δ) :
    0≤apexPhi θ lam q ∧ (apexPhi θ lam q=0 ↔ q=p) := by
  exact apexPhi_local_nonneg_zero_iff (familyCube_convex _ _)
    (by intro i; simpa using hδ) hval hgrad
    (fun q hq v hv => apexHessianForm_pos_of_interval_congruence θ lam q H T
      (hH q hq) hp hv) hq

/-- The symbolic symmetric Hessian is evaluated directly by the checked
integer interval evaluator. More efficient equivalent expressions may later
replace these derivatives without changing their semantics. -/
def apexSymmetricHessianExpr (i j : Fin 3) : ApexExpr :=
  (((apexCertificateExpr.along (apexPartials i)).along (apexPartials j)).simplify+
    ((apexCertificateExpr.along (apexPartials j)).along (apexPartials i)).simplify)*
    .rational (1/2)

theorem apexSymmetricHessianExpr_eval (θ : Fin 12 → ℝ) (lam : ℝ)
    (q : ApexVector) (i j : Fin 3) :
    (apexSymmetricHessianExpr i j).realEval (apexVariables θ lam q)=
      apexSymmetricHessian θ lam q i j := by
  simp only [apexSymmetricHessianExpr,PolynomialExpr.realEval_mul,
    PolynomialExpr.realEval_add,PolynomialExpr.realEval_rational,
    PolynomialExpr.realEval_simplify,
    apexSymmetricHessian,apexHessian]
  norm_num
  ring

def apexHessianInterval (box : Fin 24 → DyadicInterval) : FamilyIntervalMatrix :=
  fun i j => (apexSymmetricHessianExpr i j).dyadicEval box

theorem apexHessianInterval_contains {θ : Fin 12 → ℝ} {lam : ℝ}
    {q : ApexVector} {box : Fin 24 → DyadicInterval}
    (hbox : ∀k,(box k).contains (apexVariables θ lam q k)) :
    ∀i j,(apexHessianInterval box i j).contains (apexSymmetricHessian θ lam q i j) := by
  intro i j
  simpa only [apexSymmetricHessianExpr_eval] using
    (apexSymmetricHessianExpr i j).dyadicEval_contains hbox

/-- Fully symbolic-to-numeric local bridge: exact contact equations, one
box enclosing the actual environment on the cube, and integer row margins. -/
theorem apexPhi_cube_of_dyadic_box (θ : Fin 12 → ℝ) (lam : ℝ)
    (p : ApexVector) {δ : ℝ} (hδ : 0≤δ)
    (hval : apexPhi θ lam p=0) (hgrad : ∀i,apexGradient θ lam p i=0)
    (box : Fin 24 → DyadicInterval) (T : FamilyRationalMatrix)
    (hbox : ∀q∈familyCube p δ,∀k,(box k).contains (apexVariables θ lam q k))
    (hp : FamilyIntervalPositive (familyIntervalCongruence (apexHessianInterval box) T))
    {q : ApexVector} (hq : q∈familyCube p δ) :
    0≤apexPhi θ lam q ∧ (apexPhi θ lam q=0 ↔ q=p) := by
  exact apexPhi_cube_of_interval θ lam p hδ hval hgrad (apexHessianInterval box) T
    (fun q hq => apexHessianInterval_contains (hbox q hq)) hp hq

end SparseLowerTail.Section05

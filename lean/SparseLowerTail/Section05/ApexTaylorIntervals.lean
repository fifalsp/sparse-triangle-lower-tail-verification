import SparseLowerTail.Section05.ApexTaylorLocal

/-! Integer interval obligations for the actual third-order apex certificate.
The center Hessian is shifted by a proposed rational lower bound; all third
partials are enclosed on the full neighborhood. -/
namespace SparseLowerTail.Section05
open Numerics Certificate

def apexThirdExpr (i j k : Fin 3) : ApexExpr :=
  (((apexCertificateExpr.along (apexPartials i)).along (apexPartials j)).along
    (apexPartials k)).simplify

theorem apexThirdExpr_eval (θ : Fin 12 → ℝ) (lam : ℝ)
    (q : ApexVector) (i j k : Fin 3) :
    (apexThirdExpr i j k).realEval (apexVariables θ lam q)=apexThird θ lam q i j k := by
  exact PolynomialExpr.realEval_simplify _ _

def apexThirdIntervalBound (box : Fin 24 → DyadicInterval) (i j k : Fin 3) : ℤ :=
  intervalAbsBound ((apexThirdExpr i j k).dyadicEval box)

theorem apexThirdIntervalBound_sound {θ : Fin 12 → ℝ} {lam : ℝ}
    {q : ApexVector} {box : Fin 24 → DyadicInterval}
    (hbox : ∀k,(box k).contains (apexVariables θ lam q k)) (i j k : Fin 3) :
    |apexThird θ lam q i j k|≤(apexThirdIntervalBound box i j k : ℝ)/DyadicInterval.scale := by
  simpa only [apexThirdExpr_eval] using
    intervalAbsBound_sound ((apexThirdExpr i j k).dyadicEval_contains hbox)

def apexShiftedHessianInterval (H : FamilyIntervalMatrix) (ell : ℚ) :
    FamilyIntervalMatrix := fun i j =>
  if i=j then (H i j).add (DyadicInterval.point (-ell)) else H i j

noncomputable def apexShiftedHessian (θ : Fin 12 → ℝ) (lam : ℝ)
    (q : ApexVector) (ell : ℝ) : FamilyMatrix := fun i j =>
  apexSymmetricHessian θ lam q i j - if i=j then ell else 0

theorem apexShiftedHessian_symmetric (θ : Fin 12 → ℝ) (lam : ℝ)
    (q : ApexVector) (ell : ℝ) (i j : Fin 3) :
    apexShiftedHessian θ lam q ell i j=apexShiftedHessian θ lam q ell j i := by
  simp only [apexShiftedHessian,apexSymmetricHessian_symmetric θ lam q i j,eq_comm]

theorem apexShiftedHessian_form (θ : Fin 12 → ℝ) (lam : ℝ)
    (q v : ApexVector) (ell : ℝ) :
    familyQuadratic (apexShiftedHessian θ lam q ell) v=
      apexHessianForm θ lam q v-ell*apexNormSq v := by
  simp [familyQuadratic,apexShiftedHessian,apexSymmetricHessian,
    apexHessianForm,apexNormSq,sumThree]
  ring

theorem apexShiftedHessianInterval_contains {θ : Fin 12 → ℝ} {lam : ℝ}
    {q : ApexVector} {H : FamilyIntervalMatrix}
    (hH : ∀i j,(H i j).contains (apexSymmetricHessian θ lam q i j)) (ell : ℚ) :
    ∀i j,(apexShiftedHessianInterval H ell i j).contains
      (apexShiftedHessian θ lam q (ell : ℝ) i j) := by
  intro i j
  by_cases he : i=j
  · simpa only [apexShiftedHessianInterval,apexShiftedHessian,he,ite_true,
      Rat.cast_neg,sub_eq_add_neg] using
      DyadicInterval.add_contains (hH i j) (DyadicInterval.point_contains (-ell))
  · simpa only [apexShiftedHessianInterval,apexShiftedHessian,he,ite_false,sub_zero] using hH i j

theorem apexHessian_lower_of_shifted_interval {θ : Fin 12 → ℝ} {lam : ℝ}
    {q : ApexVector} {H : FamilyIntervalMatrix}
    (hH : ∀i j,(H i j).contains (apexSymmetricHessian θ lam q i j))
    (ell : ℚ) (T : FamilyRationalMatrix)
    (hp : FamilyIntervalPositive
      (familyIntervalCongruence (apexShiftedHessianInterval H ell) T))
    (v : ApexVector) : (ell : ℝ)*apexNormSq v≤apexHessianForm θ lam q v := by
  by_cases hv : v=0
  · subst v
    simp [apexNormSq,apexHessianForm,sumThree]
  · have hh := familyQuadratic_pos_of_interval_congruence
      (apexShiftedHessian_symmetric θ lam q (ell : ℝ)) _ T
      (apexShiftedHessianInterval_contains hH ell) hp hv
    rw [apexShiftedHessian_form] at hh
    linarith

/-- One kernel-checked rational margin assembles the actual Taylor certificate.
The two boxes separately enclose the center and the entire stated cube. -/
theorem apexPhi_local_of_interval_taylor {θ : Fin 12 → ℝ} {lam : ℝ}
    {p q : ApexVector} (radius ell : ℚ)
    (hradius : 0≤radius) (hell : 0<ell)
    (hval : apexPhi θ lam p=0) (hgrad : ∀i,apexGradient θ lam p i=0)
    (centerBox cubeBox : Fin 24 → DyadicInterval) (T : FamilyRationalMatrix)
    (hcenter : ∀k,(centerBox k).contains (apexVariables θ lam p k))
    (hcube : ∀r∈familyCube p (radius : ℝ),∀k,(cubeBox k).contains (apexVariables θ lam r k))
    (hH : FamilyIntervalPositive (familyIntervalCongruence
      (apexShiftedHessianInterval (apexHessianInterval centerBox) ell) T))
    (hmargin : radius*((∑i,∑j,∑k,apexThirdIntervalBound cubeBox i j k : ℤ) : ℚ)/
      (DyadicInterval.scale : ℚ)<3*ell)
    (hq : q∈familyCube p (radius : ℝ)) :
    0≤apexPhi θ lam q ∧ (apexPhi θ lam q=0 ↔ q=p) := by
  apply apexPhi_local_of_third_bounds (by exact_mod_cast hradius)
    (by exact_mod_cast hell) hval hgrad
    (apexHessian_lower_of_shifted_interval (apexHessianInterval_contains hcenter) ell T hH)
    (fun i j k => (apexThirdIntervalBound cubeBox i j k : ℝ)/DyadicInterval.scale)
    (fun r hr i j k => apexThirdIntervalBound_sound (hcube r hr) i j k) _ hq
  have hh : (radius : ℝ)*((∑i,∑j,∑k,apexThirdIntervalBound cubeBox i j k : ℤ) : ℝ)/
      (DyadicInterval.scale : ℝ)<3*(ell : ℝ) := by exact_mod_cast hmargin
  simpa only [Int.cast_sum,Finset.sum_div,mul_div_assoc] using hh

end SparseLowerTail.Section05

import SparseLowerTail.Section07.CodegreeAverages

/-! Elementary exponential Lipschitz and nonnegative surrogate-codegree bounds
for the approximate Euler--Lagrange equations. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- On nonnegative arguments, exp(-μx) is μ-Lipschitz. The proof uses only
exp(u)≥1+u and multiplication, avoiding a separate mean-value argument. -/
theorem abs_exp_neg_mul_sub_le {μ a b : ℝ} (hμ : 0≤μ) (ha : 0≤a) (hb : 0≤b) :
    |Real.exp (-μ*a)-Real.exp (-μ*b)|≤μ*|a-b| := by
  wlog hab : a≤b generalizing a b
  · have hba : b≤a := le_of_not_ge hab
    have hh := this hb ha hba
    simpa only [abs_sub_comm] using hh
  have he : Real.exp (-μ*b)=Real.exp (-μ*a)*Real.exp (-μ*(b-a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmono : Real.exp (-μ*b)≤Real.exp (-μ*a) := Real.exp_le_exp.mpr (by nlinarith)
  have hfirst : Real.exp (-μ*a)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hexp := Real.add_one_le_exp (-μ*(b-a))
  have hh := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-μ*a)).le
  have hh' := mul_le_mul_of_nonneg_right hfirst (mul_nonneg hμ (sub_nonneg.mpr hab))
  rw [abs_of_nonneg (sub_nonneg.mpr hmono),abs_of_nonpos (sub_nonpos.mpr hab),he]
  nlinarith

/-- A polynomial form of the AM--GM step that keeps both surrogate codegrees
nonnegative. -/
theorem surrogate_codegree_bound {m ev d ψ : ℝ} (hm : 0≤m) (hev : 0≤ev)
    (hem : ev≤m) (hdiag : ev*ψ^2≤2*d-m) : ev^2*|ψ|≤m*d := by
  have hh := mul_le_mul_of_nonneg_left hdiag hm
  have h₁ := mul_nonneg (sub_nonneg.mpr hem) (add_nonneg hm hev)
  have h₂ := mul_nonneg (mul_nonneg hev (sub_nonneg.mpr hem)) (sq_nonneg |ψ|)
  have h₃ := mul_nonneg (sq_nonneg ev) (sq_nonneg (|ψ|-1))
  rw [← sq_abs ψ] at hh
  nlinarith only [hh,h₁,h₂,h₃]

theorem centered_surrogate_codegrees_nonneg (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    ∀ᵐ x ∂unitMeasure,
      0≤edgeDensity U*rowDegree U x+S.eigenvalue 0^2*S.eigenfunction 0 x ∧
      0≤edgeDensity U*rowDegree U x-S.eigenvalue 0^2*S.eigenfunction 0 x := by
  filter_upwards [centeredEigenfunction_diagonal_bound U S 0] with x hx
  have hh := surrogate_codegree_bound (Section02.edgeDensity_mem_Icc U).1
    (S.eigenvalue_nonneg 0) (centeredEigenvalue_le_mean U S 0) hx
  constructor
  · have h := mul_le_mul_of_nonneg_left (neg_le_abs (S.eigenfunction 0 x)) (sq_nonneg (S.eigenvalue 0))
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (le_abs_self (S.eigenfunction 0 x)) (sq_nonneg (S.eigenvalue 0))
    nlinarith

/-- Averaging an actual exponential equation preserves its L¹ error bound. -/
theorem setAverage_exp_equation_error {u C : ℝ → ℝ} {P : Set ℝ} {μ c : ℝ}
    (hu : Integrable u unitMeasure) (hC : Integrable C unitMeasure)
    (hp : 0<unitMeasure.real P) (hμ : 0≤μ) (hc : 0≤c)
    (hpos : ∀ᵐ y ∂unitMeasure.restrict P, 0≤C y)
    (heq : ∀ᵐ y ∂unitMeasure.restrict P, u y=Real.exp (-μ*C y)) :
    |setAverage P u-Real.exp (-μ*c)|≤μ*setAverage P (fun y => |C y-c|) := by
  rw [← setAverage_const P hp (Real.exp (-μ*c)),← setAverage_sub P hu (integrable_const _)]
  apply (abs_setAverage_le _ _).trans
  rw [← setAverage_const_mul]
  apply setAverage_mono_ae (hu.sub (integrable_const _)).norm
    ((hC.sub (integrable_const _)).norm.const_mul μ)
  filter_upwards [hpos,heq] with y hy he
  simp only [Pi.sub_apply,Real.norm_eq_abs]
  rw [he]
  exact abs_exp_neg_mul_sub_le hμ hy hc

end SparseLowerTail.Section07

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Scalar coercivity in Step 4 of `thm:smalltail`.
A Taylor bound at 4.86 plus the quadratic exp bound proves the uniform growth
estimate directly; differentiating exp(0.27μ)/μ² is unnecessary. -/
noncomputable section
namespace SparseLowerTail.Section07

/-- Nine nonnegative Taylor terms already certify the required strict bound. -/
theorem exp_486_gt_120 : (120:ℝ)<Real.exp (243/50) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤243/50) 9
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

/-- The uniform exponential margin needed to identify all same-block rows. -/
theorem small_rigidity_exp_margin {μ : ℝ} (hμ : 18≤μ) :
    μ+μ^2/4 < Real.exp ((27/100)*μ) := by
  have hx : 0≤(27/100:ℝ)*(μ-18) := by nlinarith
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hp : 0<1+(27/100:ℝ)*(μ-18)+((27/100:ℝ)*(μ-18))^2/2 := by positivity
  have he := mul_lt_mul_of_pos_right exp_486_gt_120 hp
  have hm := mul_le_mul_of_nonneg_left hq (Real.exp_pos (243/50)).le
  have hprod : Real.exp (243/50)*Real.exp ((27/100:ℝ)*(μ-18))=
      Real.exp ((27/100)*μ) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hprod] at hm
  have hh := he.trans_le hm
  nlinarith [sq_nonneg (μ-18)]

/-- Inverse within-block weight and multiplier bounds used in the determinant. -/
theorem small_rigidity_weight_bounds {μ : ℝ} (hμ : 18≤μ) :
    let a := Real.exp (-((27/100)*μ))
    0<a ∧ a≤1 ∧ μ*a<1 ∧ μ+μ^2/4<a⁻¹ := by
  have ha : 0<Real.exp (-((27/100:ℝ)*μ)) := Real.exp_pos _
  have ha1 : Real.exp (-((27/100:ℝ)*μ))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have he := small_rigidity_exp_margin hμ
  have hinv : (Real.exp (-((27/100:ℝ)*μ)))⁻¹ = Real.exp ((27/100)*μ) := by
    rw [Real.exp_neg,inv_inv]
  have hm : μ<Real.exp ((27/100:ℝ)*μ) := by nlinarith [sq_nonneg μ]
  have hmul := mul_lt_mul_of_pos_right hm ha
  have hone : Real.exp ((27/100:ℝ)*μ)*Real.exp (-((27/100:ℝ)*μ))=1 := by
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  rw [hone] at hmul
  exact ⟨ha,ha1,hmul,hinv ▸ he⟩

/-- Algebraic block determinant estimate, independent of the exponential choice. -/
theorem block_rigidity_determinant {μ a p : ℝ}
    (hμ : 0≤μ) (ha : 0<a) (ha1 : a≤1) (hp : 0≤p) (hp1 : p≤1)
    (hmargin : μ+μ^2/4<a⁻¹) :
    0<1-μ*a*(1-p) ∧
    0<(a⁻¹-μ*a*p)*(1-μ*a*(1-p))-μ^2*p*(1-p) := by
  have hia : a⁻¹*a=1 := inv_mul_cancel₀ ha.ne'
  have hma : μ*a<1 := by
    have hm : μ<a⁻¹ := by nlinarith [sq_nonneg μ]
    have hh := mul_lt_mul_of_pos_right hm ha
    rwa [hia] at hh
  have hmap : 0≤μ*a*p := mul_nonneg (mul_nonneg hμ ha.le) hp
  have hpq : 0≤p*(1-p) := mul_nonneg hp (by linarith)
  have hpq1 : p*(1-p)≤1/4 := by nlinarith [sq_nonneg (p-1/2)]
  have hm2 := mul_le_mul_of_nonneg_left hpq1 (sq_nonneg μ)
  have hpos1 : 0≤μ*p*(1-a) := mul_nonneg (mul_nonneg hμ hp) (by linarith)
  have hpos2 : 0≤μ^2*(p*(1-p))*a^2 :=
    mul_nonneg (mul_nonneg (sq_nonneg μ) hpq) (sq_nonneg a)
  have heq : (a⁻¹-μ*a*p)*(1-μ*a*(1-p))-μ^2*p*(1-p)=
      a⁻¹-μ-μ^2*(p*(1-p))+μ*p*(1-a)+μ^2*(p*(1-p))*a^2 := by
    field_simp
    ring
  refine ⟨by nlinarith,?_⟩
  rw [heq]
  nlinarith

/-- A nonpositive value of this positive definite form forces both entries zero. -/
theorem quadratic_zero_of_positive_determinant {A B C X Y : ℝ}
    (hC : 0<C) (hdet : 0<A*C-B^2)
    (hQ : A*X^2-2*B*X*Y+C*Y^2≤0) : X=0 ∧ Y=0 := by
  have hmult := mul_nonpos_of_nonneg_of_nonpos hC.le hQ
  have heq : C*(A*X^2-2*B*X*Y+C*Y^2)=
      (C*Y-B*X)^2+(A*C-B^2)*X^2 := by ring
  rw [heq] at hmult
  have hx : X=0 := by
    have hle : (A*C-B^2)*X^2≤0 := by nlinarith [sq_nonneg (C*Y-B*X)]
    have : X^2≤0 := le_of_not_gt (fun h => (not_lt_of_ge hle) (mul_pos hdet h))
    nlinarith [sq_nonneg X]
  subst X
  norm_num at hQ
  have hy : Y^2≤0 := le_of_not_gt (fun h => (not_lt_of_ge hQ) (mul_pos hC h))
  exact ⟨rfl,by nlinarith [sq_nonneg Y]⟩

/-- Full scalar conclusion for the two block-norm variables in small-tail Step 4. -/
theorem small_rigidity_block_norms_zero {μ p X Y : ℝ} (hμ : 18≤μ)
    (hp : 0≤p) (hp1 : p≤1)
    (hQ : let a := Real.exp (-((27/100)*μ))
      (a⁻¹-μ*a*p)*X^2-2*μ*Real.sqrt (p*(1-p))*X*Y+
        (1-μ*a*(1-p))*Y^2≤0) : X=0 ∧ Y=0 := by
  obtain ⟨ha,ha1,_,hmargin⟩ := small_rigidity_weight_bounds hμ
  obtain ⟨hC,hdet⟩ := block_rigidity_determinant (by linarith : 0≤μ) ha ha1 hp hp1 hmargin
  have hsq : (μ*Real.sqrt (p*(1-p)))^2=μ^2*p*(1-p) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hp (by linarith))]
    ring
  apply quadratic_zero_of_positive_determinant hC (by rwa [hsq])
  convert hQ using 1
  ring

end SparseLowerTail.Section07

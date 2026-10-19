import SparseLowerTail.Section08.CertificateBridge
import SparseLowerTail.Numerics.RationalExpr

/-! Checked rational expressions for the seven coefficients of the logarithmic
family certificate. The independent variables are z, L=log(1/z), and b(z).
No interval is accepted if a computed denominator could contain zero. -/
namespace SparseLowerTail.Certificate
open Section04 Numerics
set_option linter.unusedSimpArgs false
namespace FamilyCoeff
abbrev Expr := RationalExpr 3
def z : Expr := .var 0
def L : Expr := .var 1
def b : Expr := .var 2
def gammaExpr : Expr := 6*L^2*z^2+3*L*z^3-L*z^2-L*z-L-z^3+3*z^2-3*z+1
def d1Expr : Expr := z*(z-1)*(z+1)*(L+z-1)*(2*L+z-1)/(2*gammaExpr)
def d2Expr : Expr := z*(z-1)^2*(2*L*z+z^2-1)/(2*gammaExpr)
def d3Expr : Expr := -z*(z-1)^3*(3*L*z+L+2*z^2-2)/(2*(z+1)*gammaExpr)
def d4Expr : Expr := (z-1)^4*(2*L*z+z^2-1)/(2*L*(z+1)*gammaExpr)
def multiplierExpr : Expr := 2*L/(1-z)^2
def densityExpr : Expr := (z^3+3*z)/4
def d0Expr : Expr := -d1Expr*((1+z)/2)+d2Expr*multiplierExpr*densityExpr-densityExpr/3

/-- c₀,c₁,c₂,c₃,c₄,μc₃,μc₄; the final product simplifies before evaluation. -/
def coefficientExpr : Fin 7→Expr :=
  ![b^3*d0Expr,b^2*d1Expr,b^2*d2Expr,b^3*d3Expr,b^2*d4Expr,
    b*multiplierExpr*d3Expr,multiplierExpr*d4Expr]

set_option linter.unusedSimpArgs false in
theorem rational_formulas (v : Fin 3→ℝ) :
    gammaExpr.realEval v=gamma (v 0) (v 1) ∧
    d1Expr.realEval v=d1 (v 0) (v 1) ∧
    d2Expr.realEval v=d2 (v 0) (v 1) ∧
    d3Expr.realEval v=d3 (v 0) (v 1) ∧
    d4Expr.realEval v=d4 (v 0) (v 1) ∧
    multiplierExpr.realEval v=multiplier (v 0) (v 1) ∧
    d0Expr.realEval v=d0 (v 0) (v 1) := by
  norm_num [RationalExpr.realEval,gammaExpr,d1Expr,d2Expr,d3Expr,d4Expr,multiplierExpr,d0Expr,densityExpr,
    z,L,gamma,d1,d2,d3,d4,multiplier,d0,mean,density]
  simp only [sub_eq_add_neg,true_and,div_eq_mul_inv,mul_inv_rev,←inv_pow]
  ring

noncomputable def coefficientValues (z : ℝ) : Fin 7→ℝ :=
  ![c0 z,c1 z,c2 z,c3 z,c4 z,branchMu z*c3 z,branchMu z*c4 z]

/-- Exact source correspondence, before any numerical enclosures. -/
theorem coefficientExpr_eval (z₀ : ℝ) (i : Fin 7) :
    (coefficientExpr i).realEval ![z₀,branchLog z₀,branchB z₀]=coefficientValues z₀ i := by
  have hf := rational_formulas ![z₀,branchLog z₀,branchB z₀]
  simp only [Matrix.cons_val] at hf
  fin_cases i
  · change ((b^3*d0Expr):Expr).realEval ![z₀,branchLog z₀,branchB z₀]=c0 z₀
    rw [RationalExpr.realEval_mul,RationalExpr.realEval_pow]
    change branchB z₀^3*d0Expr.realEval ![z₀,branchLog z₀,branchB z₀]=c0 z₀
    rw [hf.2.2.2.2.2.2]
    exact (c0_scaled z₀).symm
  · change ((b^2*d1Expr):Expr).realEval ![z₀,branchLog z₀,branchB z₀]=c1 z₀
    rw [RationalExpr.realEval_mul,RationalExpr.realEval_pow]
    change branchB z₀^2*d1Expr.realEval ![z₀,branchLog z₀,branchB z₀]=c1 z₀
    rw [hf.2.1]
    rfl
  · change ((b^2*d2Expr):Expr).realEval ![z₀,branchLog z₀,branchB z₀]=c2 z₀
    rw [RationalExpr.realEval_mul,RationalExpr.realEval_pow]
    change branchB z₀^2*d2Expr.realEval ![z₀,branchLog z₀,branchB z₀]=c2 z₀
    rw [hf.2.2.1]
    rfl
  · change ((b^3*d3Expr):Expr).realEval ![z₀,branchLog z₀,branchB z₀]=c3 z₀
    rw [RationalExpr.realEval_mul,RationalExpr.realEval_pow]
    change branchB z₀^3*d3Expr.realEval ![z₀,branchLog z₀,branchB z₀]=c3 z₀
    rw [hf.2.2.2.1]
    rfl
  · change ((b^2*d4Expr):Expr).realEval ![z₀,branchLog z₀,branchB z₀]=c4 z₀
    rw [RationalExpr.realEval_mul,RationalExpr.realEval_pow]
    change branchB z₀^2*d4Expr.realEval ![z₀,branchLog z₀,branchB z₀]=c4 z₀
    rw [hf.2.2.2.2.1]
    rfl
  · change ((b*multiplierExpr*d3Expr):Expr).realEval ![z₀,branchLog z₀,branchB z₀]=branchMu z₀*c3 z₀
    simp only [RationalExpr.realEval_mul,hf.2.2.2.2.2.1,hf.2.2.2.1]
    change branchB z₀*multiplier z₀ (branchLog z₀)*d3 z₀ (branchLog z₀)=branchMu z₀*c3 z₀
    rw [←branchMu_scaled z₀]
    unfold c3
    ring
  · change ((multiplierExpr*d4Expr):Expr).realEval ![z₀,branchLog z₀,branchB z₀]=branchMu z₀*c4 z₀
    simp only [RationalExpr.realEval_mul,hf.2.2.2.2.2.1,hf.2.2.2.2.1]
    rw [←branchMu_scaled z₀]
    unfold c4
    ring

/-- Any successful interval computation is a proof of an actual coefficient
bound, once z, L and b have been enclosed. -/
theorem coefficient_interval {z₀ : ℝ} {box : Fin 3→DyadicInterval}
    (hx : ∀ i,(box i).contains (![z₀,branchLog z₀,branchB z₀] i))
    (i : Fin 7) {I : DyadicInterval}
    (hI : (coefficientExpr i).dyadicEval box=some I) :
    I.contains (coefficientValues z₀ i) := by
  rw [←coefficientExpr_eval z₀ i]
  exact (coefficientExpr i).dyadicEval_contains hx hI

end FamilyCoeff
end SparseLowerTail.Certificate

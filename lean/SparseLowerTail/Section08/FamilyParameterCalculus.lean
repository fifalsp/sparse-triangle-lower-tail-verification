import SparseLowerTail.Numerics.RationalExprCalculus
import SparseLowerTail.Section08.FamilyParameterIntervals

/-! Actual L-derivatives of the family coefficients. The primitive curve is
(exp(-L), L, b(exp(-L))). Its velocity is rational in the same three inputs,
so repeated symbolic chain rules stay inside the checked rational evaluator. -/
noncomputable section
namespace SparseLowerTail.Certificate.FamilyCoeff
open Numerics Section04

def parameterB (t : ℝ) : ℝ := Real.exp (-2*Real.exp (-t)*t/(1-Real.exp (-t))^2)
def parameterCurve (t : ℝ) : Fin 3 → ℝ := ![Real.exp (-t),t,parameterB t]

theorem parameterCurve_eq (t : ℝ) :
    parameterCurve t=![Real.exp (-t),branchLog (Real.exp (-t)),branchB (Real.exp (-t))] := by
  have hL : branchLog (Real.exp (-t))=t := by rw [branchLog_eq_neg_log,Real.log_exp,neg_neg]
  simp only [parameterCurve,parameterB,branchB,hL]

def parameterVelocity : Fin 3 → Expr :=
  ![-z,1,-2*z*(1-L-z-L*z)*b/(1-z)^3]

theorem parameterVelocity_eval (t : ℝ) :
    (fun i => (parameterVelocity i).realEval (parameterCurve t))=
      ![-Real.exp (-t),1,
        -2*Real.exp (-t)*(1-t-Real.exp (-t)-t*Real.exp (-t))*parameterB t/
          (1-Real.exp (-t))^3] := by
  funext i
  fin_cases i <;> norm_num [parameterVelocity,parameterCurve,z,L,b] <;> rfl

theorem parameterCurve_hasDerivAt {t : ℝ} (ht : 0<t) (i : Fin 3) :
    HasDerivAt (fun u => parameterCurve u i)
      ((parameterVelocity i).realEval (parameterCurve t)) t := by
  have hZ : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hn : 1-Real.exp (-t)≠0 := by
    have hlt : Real.exp (-t)<1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hd : HasDerivAt (fun u : ℝ => -2*Real.exp (-u)*u/(1-Real.exp (-u))^2)
      (-2*Real.exp (-t)*(1-t-Real.exp (-t)-t*Real.exp (-t))/(1-Real.exp (-t))^3) t := by
    convert (((hZ.mul (hasDerivAt_id t)).const_mul (-2)).div
      (((hasDerivAt_const t (1:ℝ)).sub hZ).pow 2) (pow_ne_zero 2 hn)) using 1
    · funext u
      simp only [Pi.div_apply,Pi.pow_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
      ring
    · simp only [Pi.pow_apply,Pi.sub_apply,Pi.mul_apply,id_eq]
      field_simp [hn]
      ring
  have hb : HasDerivAt parameterB
      (-2*Real.exp (-t)*(1-t-Real.exp (-t)-t*Real.exp (-t))*parameterB t/
        (1-Real.exp (-t))^3) t := by
    convert hd.exp using 1
    unfold parameterB
    ring
  have he := congrFun (parameterVelocity_eval t) i
  rw [he]
  fin_cases i
  · exact hZ
  · exact hasDerivAt_id t
  · exact hb

/-- Repeated differentiation uses exactly the paper's rational coefficient
formula and the proved primitive velocity. No numerical derivative oracle. -/
def derivativeExpr (i : Fin 7) : ℕ → Expr
  | 0 => coefficientExpr i
  | n+1 => (derivativeExpr i n).along parameterVelocity

def coefficientDerivative (i : Fin 7) (n : ℕ) (t : ℝ) : ℝ :=
  (derivativeExpr i n).realEval (parameterCurve t)

theorem coefficientDerivative_zero (i : Fin 7) (t : ℝ) :
    coefficientDerivative i 0 t=coefficientValues (Real.exp (-t)) i := by
  unfold coefficientDerivative derivativeExpr
  rw [parameterCurve_eq,coefficientExpr_eval]

theorem coefficientDerivative_hasDerivAt (i : Fin 7) (n : ℕ) {t : ℝ}
    (ht : 0<t) (he : (derivativeExpr i n).Domain (parameterCurve t)) :
    HasDerivAt (coefficientDerivative i n) (coefficientDerivative i (n+1) t) t :=
  (derivativeExpr i n).hasDerivAt_realEval parameterVelocity
    (parameterCurve_hasDerivAt ht) he

/-- Successful coefficient/derivative enclosures supply the domain checks
needed for every step of the Taylor chain, uniformly over an L interval. -/
theorem derivative_hasDerivAt_of_checked (C : FamilyParameterCertificate) (hC : C.Valid)
    (i : Fin 7) (n : ℕ) {I : DyadicInterval}
    (he : (derivativeExpr i n).dyadicEval C.parameterBox=some I)
    {t : ℝ} (ht : 0<t) (hL : Bounds t (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    HasDerivAt (coefficientDerivative i n) (coefficientDerivative i (n+1) t) t := by
  apply coefficientDerivative_hasDerivAt i n ht
  apply RationalExpr.domain_of_dyadicEval _ _ he
  rw [parameterCurve_eq]
  apply C.parameterBox_contains hC (Real.exp_pos _)
  simpa only [branchLog_eq_neg_log,Real.log_exp,neg_neg] using hL

theorem coefficientDerivative_interval (C : FamilyParameterCertificate) (hC : C.Valid)
    (i : Fin 7) (n : ℕ) {I : DyadicInterval}
    (he : (derivativeExpr i n).dyadicEval C.parameterBox=some I)
    {t : ℝ} (hL : Bounds t (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    I.contains (coefficientDerivative i n t) := by
  apply RationalExpr.dyadicEval_contains _ _ he
  rw [parameterCurve_eq]
  apply C.parameterBox_contains hC (Real.exp_pos _)
  simpa only [branchLog_eq_neg_log,Real.log_exp,neg_neg] using hL

end SparseLowerTail.Certificate.FamilyCoeff

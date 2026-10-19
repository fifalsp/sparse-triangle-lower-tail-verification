import SparseLowerTail.Section05.ApexExpr
import SparseLowerTail.Section08.FamilyLocalContacts

/-! Actual first and second derivatives of the apex logarithmic certificate.
The certificate is smooth on all logarithmic coordinates; coefficient variables
are constant along segments. No derivative identity is assumed. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05
set_option linter.unnecessarySeqFocus false
open Numerics PolynomialExpr Certificate

abbrev ApexVector := Fin 3 → ℝ

def apexPhi (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) : ℝ :=
  logCertificate θ lam criticalPoint ((q 0,q 1),q 2)

def apexVariables (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) : Fin 24 → ℝ :=
  apexEnvironment θ lam ((q 0,q 1),q 2)

def apexPartials : Fin 3 → Fin 24 → ApexExpr :=
  ![![(.rational 1),(.rational 0),(.rational 0),(.neg (.var 3)),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0)],![(.rational 0),(.rational 1),(.rational 0),(.rational 0),(.neg (.var 4)),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0)],![(.rational 0),(.rational 0),(.rational 1),(.rational 0),(.rational 0),(.neg (.var 5)),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0),(.rational 0)]]

def apexGradient (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) (i : Fin 3) : ℝ :=
  (apexCertificateExpr.along (apexPartials i)).realEval (apexVariables θ lam q)

def apexHessian (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) (i j : Fin 3) : ℝ :=
  ((apexCertificateExpr.along (apexPartials i)).along (apexPartials j)).realEval
    (apexVariables θ lam q)

theorem apexVariables_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ)
    (p v : ApexVector) (s : ℝ) (i : Fin 24) :
    HasDerivAt (fun t => apexVariables θ lam (familySegment p v t) i)
      (v 0*(apexPartials 0 i).realEval (apexVariables θ lam (familySegment p v s))+
       v 1*(apexPartials 1 i).realEval (apexVariables θ lam (familySegment p v s))+
       v 2*(apexPartials 2 i).realEval (apexVariables θ lam (familySegment p v s))) s := by
  have hq (j : Fin 3) : HasDerivAt (fun t => p j+t*v j) (v j) s := by
    simpa using ((hasDerivAt_id s).mul_const (v j)).const_add (p j)
  have he (j : Fin 3) : HasDerivAt (fun t => Real.exp (-(p j+t*v j)))
      (-v j*Real.exp (-(p j+s*v j))) s := by
    simpa only [Pi.neg_apply,mul_comm] using (hq j).neg.exp
  fin_cases i
  · change HasDerivAt (fun t : ℝ => p 0+t*v 0) (v 0*((1:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hq 0 using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => p 1+t*v 1) (v 0*((0:ℚ):ℝ)+v 1*((1:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hq 1 using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => p 2+t*v 2) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((1:ℚ):ℝ)) s
    convert hq 2 using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => Real.exp (-(p 0+t*v 0))) (v 0*(-Real.exp (-(p 0+s*v 0)))+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert he 0 using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => Real.exp (-(p 1+t*v 1))) (v 0*((0:ℚ):ℝ)+v 1*(-Real.exp (-(p 1+s*v 1)))+v 2*((0:ℚ):ℝ)) s
    convert he 1 using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => Real.exp (-(p 2+t*v 2))) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*(-Real.exp (-(p 2+s*v 2)))) s
    convert he 2 using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => criticalTriangle) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (criticalTriangle) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => criticalOmega) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (criticalOmega) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => relaxationMultiplier criticalPoint) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (relaxationMultiplier criticalPoint) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => criticalMean) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (criticalMean) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => criticalCost) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (criticalCost) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 0) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 0) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 1) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 1) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 2) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 2) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 3) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 3) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 4) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 4) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 5) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 5) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 6) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 6) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 7) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 7) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 8) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 8) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 9) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 9) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 10) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 10) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => θ 11) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (θ 11) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => lam) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (lam) using 1 <;> norm_num

theorem apexPhi_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ)
    (p v : ApexVector) (s : ℝ) :
    HasDerivAt (fun t => apexPhi θ lam (familySegment p v t))
      (sumThree (fun i => v i*apexGradient θ lam (familySegment p v s) i)) s := by
  have h := apexCertificateExpr.hasDerivAt_three apexPartials v
    (apexVariables_segment_deriv θ lam p v s)
  simpa only [apexVariables,apexCertificateExpr_realEval,apexPhi,apexGradient,
    sumThree,derivative,realEval_simplify] using h

theorem apexGradient_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ)
    (p v : ApexVector) (s : ℝ) (i : Fin 3) :
    HasDerivAt (fun t => apexGradient θ lam (familySegment p v t) i)
      (sumThree (fun j => v j*apexHessian θ lam (familySegment p v s) i j)) s := by
  simpa only [apexGradient,apexHessian,sumThree,derivative,realEval_simplify] using
    (apexCertificateExpr.along (apexPartials i)).hasDerivAt_three apexPartials v
      (apexVariables_segment_deriv θ lam p v s)

end SparseLowerTail.Section05

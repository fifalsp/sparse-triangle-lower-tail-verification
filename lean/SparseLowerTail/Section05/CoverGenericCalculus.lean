import SparseLowerTail.Section05.CoverGenericEnvironment
import SparseLowerTail.Section05.ApexCalculus

/-! The same symbolic partial directions work at every parameter vertex.
All twenty-four-variable expression and derivative definitions are shared. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr Certificate

def coverPhi (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : ApexVector) : ℝ :=
  logCertificate θ lam π ((q 0,q 1),q 2)

def coverVariables (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : ApexVector) : Fin 24 → ℝ :=
  coverEnvironment θ lam π ((q 0,q 1),q 2)

def coverGradient (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : ApexVector) (i : Fin 3) : ℝ :=
  (apexCertificateExpr.along (apexPartials i)).realEval (coverVariables θ lam π q)

def coverHessian (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : ApexVector) (i j : Fin 3) : ℝ :=
  ((apexCertificateExpr.along (apexPartials i)).along (apexPartials j)).realEval
    (coverVariables θ lam π q)

theorem coverVariables_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ)
    (p v : ApexVector) (s : ℝ) (i : Fin 24) :
    HasDerivAt (fun t => coverVariables θ lam π (familySegment p v t) i)
      (v 0*(apexPartials 0 i).realEval (coverVariables θ lam π (familySegment p v s))+
       v 1*(apexPartials 1 i).realEval (coverVariables θ lam π (familySegment p v s))+
       v 2*(apexPartials 2 i).realEval (coverVariables θ lam π (familySegment p v s))) s := by
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
  · change HasDerivAt (fun t : ℝ => relaxationMultiplier π) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (relaxationMultiplier π) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => π.1) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (π.1) using 1 <;> norm_num
  · change HasDerivAt (fun t : ℝ => π.2) (v 0*((0:ℚ):ℝ)+v 1*((0:ℚ):ℝ)+v 2*((0:ℚ):ℝ)) s
    convert hasDerivAt_const s (π.2) using 1 <;> norm_num
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

theorem coverPhi_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ)
    (p v : ApexVector) (s : ℝ) :
    HasDerivAt (fun t => coverPhi θ lam π (familySegment p v t))
      (sumThree (fun i => v i*coverGradient θ lam π (familySegment p v s) i)) s := by
  have h := apexCertificateExpr.hasDerivAt_three apexPartials v
    (coverVariables_segment_deriv θ lam π p v s)
  simpa only [coverVariables,coverCertificateExpr_realEval,coverPhi,coverGradient,
    sumThree,derivative,realEval_simplify] using h

theorem coverGradient_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ)
    (p v : ApexVector) (s : ℝ) (i : Fin 3) :
    HasDerivAt (fun t => coverGradient θ lam π (familySegment p v t) i)
      (sumThree (fun j => v j*coverHessian θ lam π (familySegment p v s) i j)) s := by
  simpa only [coverGradient,coverHessian,sumThree,derivative,realEval_simplify] using
    (apexCertificateExpr.along (apexPartials i)).hasDerivAt_three apexPartials v
      (coverVariables_segment_deriv θ lam π p v s)

end SparseLowerTail.Section05

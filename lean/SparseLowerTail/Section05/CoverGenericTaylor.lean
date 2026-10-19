import SparseLowerTail.Section05.CoverGenericCalculus
import SparseLowerTail.Numerics.DyadicTaylorFactored

/-! One Taylor checker for all cover jobs, with coefficients as interval inputs.
The actual fan tangency coefficients may be enclosed without being rational. -/
noncomputable section
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr Certificate Set

def coverGradientExpr (i : Fin 3) : ApexExpr :=
  apexCertificateExpr.derivative (apexPartials i)
def coverHessianExpr (i j : Fin 3) : ApexExpr :=
  (coverGradientExpr i).derivative (apexPartials j)

theorem coverGradientExpr_correct (i : Fin 3) (y : Fin 24 → ℝ) :
    (coverGradientExpr i).realEval y =
      (apexCertificateExpr.derivative (apexPartials i)).realEval y := rfl

theorem coverHessianExpr_correct (i j : Fin 3) (y : Fin 24 → ℝ) :
    (coverHessianExpr i j).realEval y =
      ((apexCertificateExpr.derivative (apexPartials i)).derivative (apexPartials j)).realEval y := rfl

/-- Any semantically checked factorization of the shared derivatives can be used.
All interval hypotheses refer to the exact real coefficients of this job. -/
theorem cover_factored_taylor_positive
    (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ)
    (g : Fin 3 → ApexExpr) (h : Fin 3 → Fin 3 → ApexExpr)
    (hg : ∀ i y,(g i).realEval y=
      (apexCertificateExpr.derivative (apexPartials i)).realEval y)
    (hh : ∀ i j y,(h i j).realEval y=
      ((apexCertificateExpr.derivative (apexPartials i)).derivative (apexPartials j)).realEval y)
    (p v : ApexVector) (start whole : Fin 24 → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval)
    (hv : ∀ i,(velocity i).contains (v i))
    (hs : ∀ i,(start i).contains (coverVariables θ lam π (familySegment p v 0) i))
    (hw : ∀ s∈Icc (0:ℝ) 1,∀ i,
      (whole i).contains (coverVariables θ lam π (familySegment p v s) i))
    (hm : 0<dyadicFactoredTaylorMargin apexCertificateExpr g h start whole velocity) :
    0<coverPhi θ lam π (familySegment p v 1) := by
  have H := dyadic_factored_taylor_positive apexCertificateExpr apexPartials g h hg hh
    v (fun s => coverVariables θ lam π (familySegment p v s)) start whole velocity hv
    (fun s _ i => coverVariables_segment_deriv θ lam π p v s i) hs hw hm
  simpa only [coverVariables,coverCertificateExpr_realEval,coverPhi] using H

end SparseLowerTail.Section05

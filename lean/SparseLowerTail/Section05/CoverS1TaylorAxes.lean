import SparseLowerTail.Numerics.IntervalTaylorAxes
import SparseLowerTail.Section05.CoverS1Taylor

/-! Partial-gradient and Hessian Taylor bridge for the actual S1 certificate. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr Set
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def s1PartialDirections : Fin 3 → Fin 9 → S1Expr :=
  ![![1,0,0,-(.var 3),0,0,0,0,0],
    ![0,1,0,0,-(.var 4),0,0,0,0],
    ![0,0,1,0,0,-(.var 5),0,0,0]]

def s1Partial (i : Fin 3) : S1Expr := s1CertificateExpr.derivative (s1PartialDirections i)
def s1Partial2 (i j : Fin 3) : S1Expr := (s1Partial i).derivative (s1PartialDirections j)

theorem s1PartialEnvironment_hasDerivAt (c v : EdgeTriple) (s : ℝ) (i : Fin 9) :
    HasDerivAt (fun t => s1Environment (s1LinePoint c v t) i)
      (v.1.1*(s1PartialDirections 0 i).realEval (s1Environment (s1LinePoint c v s))+
       v.1.2*(s1PartialDirections 1 i).realEval (s1Environment (s1LinePoint c v s))+
       v.2*(s1PartialDirections 2 i).realEval (s1Environment (s1LinePoint c v s))) s := by
  have h := s1LineEnvironment_hasDerivAt c v s (i.castAdd 3)
  have he : (fun t => s1LineEnvironment c v t (i.castAdd 3)) =
      (fun t => s1Environment (s1LinePoint c v t) i) := by
    funext t
    fin_cases i <;> rfl
  rw [he] at h
  convert h using 1
  fin_cases i
  · change v.1.1*((1:ℚ):ℝ)+v.1.2*((0:ℚ):ℝ)+v.2*((0:ℚ):ℝ) = v.1.1
    norm_num
  · change v.1.1*((0:ℚ):ℝ)+v.1.2*((1:ℚ):ℝ)+v.2*((0:ℚ):ℝ) = v.1.2
    norm_num
  · change v.1.1*((0:ℚ):ℝ)+v.1.2*((0:ℚ):ℝ)+v.2*((1:ℚ):ℝ) = v.2
    norm_num
  · change v.1.1*(-Real.exp (-(c.1.1+s*v.1.1)))+v.1.2*((0:ℚ):ℝ)+v.2*((0:ℚ):ℝ) = -(v.1.1*Real.exp (-(c.1.1+s*v.1.1)))
    norm_num
  · change v.1.1*((0:ℚ):ℝ)+v.1.2*(-Real.exp (-(c.1.2+s*v.1.2)))+v.2*((0:ℚ):ℝ) = -(v.1.2*Real.exp (-(c.1.2+s*v.1.2)))
    norm_num
  · change v.1.1*((0:ℚ):ℝ)+v.1.2*((0:ℚ):ℝ)+v.2*(-Real.exp (-(c.2+s*v.2))) = -(v.2*Real.exp (-(c.2+s*v.2)))
    norm_num
  · change v.1.1*((0:ℚ):ℝ)+v.1.2*((0:ℚ):ℝ)+v.2*((0:ℚ):ℝ) = ((0:ℚ):ℝ)
    norm_num
  · change v.1.1*((0:ℚ):ℝ)+v.1.2*((0:ℚ):ℝ)+v.2*((0:ℚ):ℝ) = ((0:ℚ):ℝ)
    norm_num
  · change v.1.1*((0:ℚ):ℝ)+v.1.2*((0:ℚ):ℝ)+v.2*((0:ℚ):ℝ) = ((0:ℚ):ℝ)
    norm_num

/-- Actual S1 Taylor estimate with the scalar partial derivatives enclosed
before combining the displacement intervals. -/
theorem coverS1_taylor_axes_positive (c v : EdgeTriple)
    (start whole : Fin 9 → RationalInterval) (velocity : Fin 3 → RationalInterval) {L : ℚ}
    (hv : ∀ i, (velocity i).contains (edgeCoordinate v i))
    (hstart : ∀ i, (start i).contains (s1Environment (s1LinePoint c v 0) i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i,
      (whole i).contains (s1Environment (s1LinePoint c v s) i))
    (hL : L < (s1CertificateExpr.intervalEval start).lower+
      (gradientInterval s1CertificateExpr s1PartialDirections start velocity).lower+
      (hessianInterval s1CertificateExpr s1PartialDirections whole velocity).lower/2) :
    (L : ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 (s1LinePoint c v 1) := by
  rw [← s1CertificateExpr_realEval]
  exact interval_taylor_axes_positive s1CertificateExpr s1PartialDirections
    (edgeCoordinate v) (fun s => s1Environment (s1LinePoint c v s)) start whole velocity hv
    (fun s _ i => s1PartialEnvironment_hasDerivAt c v s i) hstart hwhole hL

end SparseLowerTail.Section05

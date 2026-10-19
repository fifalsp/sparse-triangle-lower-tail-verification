import SparseLowerTail.Numerics.IntervalTaylor
import SparseLowerTail.Section05.CoverS1Expr
import SparseLowerTail.Section05.LogBoxSubdivision

/-! Actual symbolic Taylor derivatives of the S1 certificate along line segments.
Three additional variables store the constant displacement. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr Set
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

abbrev S1PathExpr := PolynomialExpr 12

def s1LiftedExpr : S1PathExpr := s1CertificateExpr.rename (fun i => i.castAdd 3)

def s1Direction : Fin 12 → S1PathExpr :=
  ![.var 9,.var 10,.var 11,-(.var 9*.var 3),-(.var 10*.var 4),-(.var 11*.var 5),
    0,0,0,0,0,0]

noncomputable def s1ExtendedEnvironment (q v : EdgeTriple) : Fin 12 → ℝ :=
  ![q.1.1,q.1.2,q.2,Real.exp (-q.1.1),Real.exp (-q.1.2),Real.exp (-q.2),
    criticalTriangle,criticalOmega,relaxationMultiplier coverS1Vertex0,v.1.1,v.1.2,v.2]

def s1LinePoint (c v : EdgeTriple) (s : ℝ) : EdgeTriple :=
  ((c.1.1+s*v.1.1,c.1.2+s*v.1.2),c.2+s*v.2)

noncomputable def s1LineEnvironment (c v : EdgeTriple) (s : ℝ) : Fin 12 → ℝ :=
  s1ExtendedEnvironment (s1LinePoint c v s) v

theorem s1LiftedExpr_realEval (q v : EdgeTriple) :
    s1LiftedExpr.realEval (s1ExtendedEnvironment q v) =
      logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  rw [s1LiftedExpr,realEval_rename]
  have h : (fun i : Fin 9 => s1ExtendedEnvironment q v (i.castAdd 3)) =
      s1Environment q := by
    funext i
    fin_cases i <;> rfl
  rw [h,s1CertificateExpr_realEval]

theorem s1LineEnvironment_hasDerivAt (c v : EdgeTriple) (s : ℝ) (i : Fin 12) :
    HasDerivAt (fun t => s1LineEnvironment c v t i)
      ((s1Direction i).realEval (s1LineEnvironment c v s)) s := by
  have h0 : HasDerivAt (fun t : ℝ => c.1.1+t*v.1.1) v.1.1 s := by
    simpa using ((hasDerivAt_id s).mul_const v.1.1).const_add c.1.1
  have h1 : HasDerivAt (fun t : ℝ => c.1.2+t*v.1.2) v.1.2 s := by
    simpa using ((hasDerivAt_id s).mul_const v.1.2).const_add c.1.2
  have h2 : HasDerivAt (fun t : ℝ => c.2+t*v.2) v.2 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2).const_add c.2
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change HasDerivAt (fun t : ℝ => Real.exp (-(c.1.1+t*v.1.1)))
      (-(v.1.1*Real.exp (-(c.1.1+s*v.1.1)))) s
    convert h0.neg.exp using 1 <;> dsimp <;> ring
  · change HasDerivAt (fun t : ℝ => Real.exp (-(c.1.2+t*v.1.2)))
      (-(v.1.2*Real.exp (-(c.1.2+s*v.1.2)))) s
    convert h1.neg.exp using 1 <;> dsimp <;> ring
  · change HasDerivAt (fun t : ℝ => Real.exp (-(c.2+t*v.2)))
      (-(v.2*Real.exp (-(c.2+s*v.2)))) s
    convert h2.neg.exp using 1 <;> dsimp <;> ring
  · change HasDerivAt (fun _ : ℝ => criticalTriangle) ((0:ℚ):ℝ) s
    simpa only [Rat.cast_zero] using hasDerivAt_const s _
  · change HasDerivAt (fun _ : ℝ => criticalOmega) ((0:ℚ):ℝ) s
    simpa only [Rat.cast_zero] using hasDerivAt_const s _
  · change HasDerivAt (fun _ : ℝ => relaxationMultiplier coverS1Vertex0) ((0:ℚ):ℝ) s
    simpa only [Rat.cast_zero] using hasDerivAt_const s _
  · change HasDerivAt (fun _ : ℝ => v.1.1) ((0:ℚ):ℝ) s
    simpa only [Rat.cast_zero] using hasDerivAt_const s _
  · change HasDerivAt (fun _ : ℝ => v.1.2) ((0:ℚ):ℝ) s
    simpa only [Rat.cast_zero] using hasDerivAt_const s _
  · change HasDerivAt (fun _ : ℝ => v.2) ((0:ℚ):ℝ) s
    simpa only [Rat.cast_zero] using hasDerivAt_const s _

/-- Complete analytic Taylor bridge for the actual certificate. Only rational
interval comparisons and actual bounds for its elementary variables remain. -/
theorem coverS1_taylor2_positive (c v : EdgeTriple)
    (start whole : Fin 12 → RationalInterval) {L : ℚ}
    (hstart : ∀ i, (start i).contains (s1LineEnvironment c v 0 i))
    (hwhole : ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (whole i).contains (s1LineEnvironment c v s i))
    (hL : L < (s1LiftedExpr.intervalEval start).lower+
      ((s1LiftedExpr.derivative s1Direction).intervalEval start).lower+
      (((s1LiftedExpr.derivative s1Direction).derivative s1Direction).intervalEval whole).lower/2) :
    (L : ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 (s1LinePoint c v 1) := by
  rw [← s1LiftedExpr_realEval (s1LinePoint c v 1) v]
  exact interval_taylor2_positive s1LiftedExpr s1Direction (s1LineEnvironment c v)
    start whole (fun s _ i => s1LineEnvironment_hasDerivAt c v s i) hstart hwhole hL

end SparseLowerTail.Section05

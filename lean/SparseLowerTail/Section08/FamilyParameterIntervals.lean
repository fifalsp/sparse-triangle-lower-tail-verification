import SparseLowerTail.Section08.FamilyCoefficientIntervals
import SparseLowerTail.Numerics.ExpEndpoints

/-! End-to-end parameter enclosures for the logarithmic family certificate.
All numerical data are checked by rational Taylor inequalities and dyadic
arithmetic; no interval-software output is trusted as an analytic premise. -/
namespace SparseLowerTail.Certificate
open Section04 Numerics

/-- The two endpoint certificates are ordered by their arguments, so their
exponential bounds occur in the opposite order. -/
def expEndpointInterval (lo hi : ExpEndpointCertificate) : DyadicInterval :=
  DyadicInterval.ofRational ⟨hi.lower,lo.upper⟩

theorem expEndpointInterval_contains (lo hi : ExpEndpointCertificate)
    (hlo : lo.Valid) (hhi : hi.Valid) {x : ℝ}
    (hx : Bounds x (lo.q : ℝ) (hi.q : ℝ)) :
    (expEndpointInterval lo hi).contains (Real.exp (-x)) := by
  apply DyadicInterval.ofRational_contains
  exact exp_neg_bounds_on_interval hx (lo.bounds hlo).2 (hi.bounds hhi).1

/-- Rational expression for -log b(z). Its third variable is unused. -/
def familyDeltaExpr : RationalExpr 3 :=
  2*(.var 0)*(.var 1)/(1-(.var 0))^2

theorem familyDeltaExpr_eval (x : Fin 3→ℝ) :
    familyDeltaExpr.realEval x=2*x 0*x 1/(1-x 0)^2 := by
  simp [familyDeltaExpr,RationalExpr.realEval,sub_eq_add_neg]

/-- Numerical proposal for one logarithmic parameter interval. The four
endpoint objects each include their own exact rational Taylor witnesses. -/
structure FamilyParameterCertificate where
  logLower : ExpEndpointCertificate
  logUpper : ExpEndpointCertificate
  deltaLower : ExpEndpointCertificate
  deltaUpper : ExpEndpointCertificate
  delta : DyadicInterval
  deriving Repr

namespace FamilyParameterCertificate

def logInterval (C : FamilyParameterCertificate) : DyadicInterval :=
  DyadicInterval.ofRational ⟨C.logLower.q,C.logUpper.q⟩
def zInterval (C : FamilyParameterCertificate) : DyadicInterval :=
  expEndpointInterval C.logLower C.logUpper
def bInterval (C : FamilyParameterCertificate) : DyadicInterval :=
  expEndpointInterval C.deltaLower C.deltaUpper
def deltaBox (C : FamilyParameterCertificate) : Fin 3→DyadicInterval :=
  ![C.zInterval,C.logInterval,DyadicInterval.point 0]
def parameterBox (C : FamilyParameterCertificate) : Fin 3→DyadicInterval :=
  ![C.zInterval,C.logInterval,C.bInterval]

def Valid (C : FamilyParameterCertificate) : Prop :=
  C.logLower.Valid ∧ C.logUpper.Valid ∧ C.deltaLower.Valid ∧ C.deltaUpper.Valid ∧
  familyDeltaExpr.dyadicEval C.deltaBox=some C.delta ∧
  C.deltaLower.q≤(C.delta.lower : ℚ)/DyadicInterval.scale ∧
  (C.delta.upper : ℚ)/DyadicInterval.scale≤C.deltaUpper.q

instance (C : FamilyParameterCertificate) : Decidable C.Valid := inferInstanceAs (Decidable (
  C.logLower.Valid ∧ C.logUpper.Valid ∧ C.deltaLower.Valid ∧ C.deltaUpper.Valid ∧
  familyDeltaExpr.dyadicEval C.deltaBox=some C.delta ∧
  C.deltaLower.q≤(C.delta.lower : ℚ)/DyadicInterval.scale ∧
  (C.delta.upper : ℚ)/DyadicInterval.scale≤C.deltaUpper.q))

theorem logInterval_contains (C : FamilyParameterCertificate) {z₀ : ℝ}
    (hL : Bounds (branchLog z₀) (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    C.logInterval.contains (branchLog z₀) :=
  DyadicInterval.ofRational_contains hL

theorem zInterval_contains (C : FamilyParameterCertificate) (hC : C.Valid)
    {z₀ : ℝ} (hz : 0<z₀)
    (hL : Bounds (branchLog z₀) (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    C.zInterval.contains z₀ := by
  have he : Real.exp (-branchLog z₀)=z₀ := by
    rw [branchLog_eq_neg_log,neg_neg,Real.exp_log hz]
  simpa only [zInterval,he] using expEndpointInterval_contains
    C.logLower C.logUpper hC.1 hC.2.1 hL

theorem delta_contains (C : FamilyParameterCertificate) (hC : C.Valid)
    {z₀ : ℝ} (hz : 0<z₀)
    (hL : Bounds (branchLog z₀) (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    C.delta.contains (2*z₀*branchLog z₀/(1-z₀)^2) := by
  have hx : ∀i,(C.deltaBox i).contains (![z₀,branchLog z₀,0] i) := by
    intro i
    fin_cases i
    · exact C.zInterval_contains hC hz hL
    · exact C.logInterval_contains hL
    · simpa using DyadicInterval.point_contains 0
  have he := familyDeltaExpr.dyadicEval_contains hx hC.2.2.2.2.1
  simpa only [familyDeltaExpr_eval,Matrix.cons_val] using he

theorem delta_endpoint_bounds (C : FamilyParameterCertificate) (hC : C.Valid)
    {z₀ : ℝ} (hz : 0<z₀)
    (hL : Bounds (branchLog z₀) (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    Bounds (2*z₀*branchLog z₀/(1-z₀)^2) (C.deltaLower.q : ℝ) (C.deltaUpper.q : ℝ) := by
  have h := C.delta_contains hC hz hL
  have hlo : (C.deltaLower.q : ℝ)≤(C.delta.lower : ℝ)/DyadicInterval.scale := by
    exact_mod_cast hC.2.2.2.2.2.1
  have hhi : (C.delta.upper : ℝ)/DyadicInterval.scale≤(C.deltaUpper.q : ℝ) := by
    exact_mod_cast hC.2.2.2.2.2.2
  exact ⟨hlo.trans h.1,h.2.trans hhi⟩

theorem bInterval_contains (C : FamilyParameterCertificate) (hC : C.Valid)
    {z₀ : ℝ} (hz : 0<z₀)
    (hL : Bounds (branchLog z₀) (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    C.bInterval.contains (branchB z₀) := by
  have he : branchB z₀=Real.exp (-(2*z₀*branchLog z₀/(1-z₀)^2)) := by
    unfold branchB
    congr 1
    ring
  rw [he]
  exact expEndpointInterval_contains C.deltaLower C.deltaUpper hC.2.2.1 hC.2.2.2.1
    (C.delta_endpoint_bounds hC hz hL)

/-- The actual inputs to every rational coefficient are now enclosed. -/
theorem parameterBox_contains (C : FamilyParameterCertificate) (hC : C.Valid)
    {z₀ : ℝ} (hz : 0<z₀)
    (hL : Bounds (branchLog z₀) (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    ∀i,(C.parameterBox i).contains (![z₀,branchLog z₀,branchB z₀] i) := by
  intro i
  fin_cases i
  · exact C.zInterval_contains hC hz hL
  · exact C.logInterval_contains hL
  · exact C.bInterval_contains hC hz hL

/-- Successful coefficient evaluation after a valid parameter certificate
is an enclosure of the paper's actual coefficient, uniformly in L. -/
theorem coefficient_contains (C : FamilyParameterCertificate) (hC : C.Valid)
    {z₀ : ℝ} (hz : 0<z₀)
    (hL : Bounds (branchLog z₀) (C.logLower.q : ℝ) (C.logUpper.q : ℝ))
    (i : Fin 7) {I : DyadicInterval}
    (hI : (FamilyCoeff.coefficientExpr i).dyadicEval C.parameterBox=some I) :
    I.contains (FamilyCoeff.coefficientValues z₀ i) :=
  FamilyCoeff.coefficient_interval (C.parameterBox_contains hC hz hL) i hI

end FamilyParameterCertificate
end SparseLowerTail.Certificate

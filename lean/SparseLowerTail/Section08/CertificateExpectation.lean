import SparseLowerTail.Section08.CertificateBridge
import SparseLowerTail.Section08.GraphonIntegration

/-! Actual graphon-integral certificate expectation identity (`s8:expect`). -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Certificate
open Section04 TriangleIntegration

/-- One cyclic summand in `s8:rewrite`. -/
def localTerm (z x y w : ℝ) := c0 z+c1 z*x+c2 z*x*Real.log x +
  (c3 z+c4 z*x*Real.log x)*(Real.log x+branchMu z*y*w)

theorem psi_cyclic_rewrite (z x y w : ℝ) :
    psi z x y w = localTerm z x y w+localTerm z y w x+localTerm z w x y+x*y*w := by
  unfold psi potential localTerm
  ring

theorem localTerm_bounded {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (z : ℝ) {f g h : α → ℝ}
    (hf : BoundedObservable ν f) (hg : BoundedObservable ν g) (hh : BoundedObservable ν h)
    (hl : BoundedObservable ν (fun p => Real.log (f p))) :
    BoundedObservable ν (fun p => localTerm z (f p) (g p) (h p)) := by
  exact (((BoundedObservable.const (c0 z)).add (hf.const_mul (c1 z))).add
    ((hf.const_mul (c2 z)).mul hl)).add
    (((BoundedObservable.const (c3 z)).add ((hf.const_mul (c4 z)).mul hl)).mul
      (hl.add ((hg.const_mul (branchMu z)).mul hh)))

/-- Integrability of the actual certificate follows from the stipulated positive
lower bound on U, not from an extra integrability assumption. -/
theorem psi_integrable (z : ℝ) (U : Graphon) {ell : ℝ} (hell : 0 < ell)
    (hU : ∀ᵐ p ∂squareMeasure, ell ≤ U p) :
    Integrable (fun p => psi z (X U p) (Y U p) (Z U p)) tripleMeasure := by
  have hl := graphon_log_boundedObservable U hell hU
  have h1 := localTerm_bounded z (boundedX U) (boundedY U) (boundedZ U) (hl.comp edgeX_qmp)
  have h2 := localTerm_bounded z (boundedY U) (boundedZ U) (boundedX U) (hl.comp edgeY_qmp)
  have h3 := localTerm_bounded z (boundedZ U) (boundedX U) (boundedY U) (hl.comp edgeZ_qmp)
  simpa only [psi_cyclic_rewrite] using
    (((h1.add h2).add h3).add (((boundedX U).mul (boundedY U)).mul (boundedZ U))).integrable

/-- The expected certificate, with three independent Lebesgue vertices. -/
def expectation (z : ℝ) (U : Graphon) : ℝ :=
  ∫ p, psi z (X U p) (Y U p) (Z U p) ∂tripleMeasure

private theorem integral_first {f : ℝ × ℝ → ℝ} (hf : BoundedObservable squareMeasure f) :
    (∫ p, f p.1 ∂tripleMeasure) = ∫ p, f p ∂squareMeasure := by
  rw [integral_prod _ (hf.comp edgeX_qmp).integrable]
  simp

/-- A bounded test of the Euler–Lagrange residual, evaluated by Fubini. -/
theorem integral_test_residual (U : Graphon) {ell μ μTilde : ℝ} (hell : 0 < ell)
    (hU : ∀ᵐ p ∂squareMeasure, ell ≤ U p)
    (hEL : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μTilde*codegree U p.1 p.2)
    {f : ℝ × ℝ → ℝ} (hf : BoundedObservable squareMeasure f) :
    (∫ p, f p.1*(Real.log (U p.1)+μ*Y U p*Z U p) ∂tripleMeasure) =
      (μ-μTilde)*(∫ p, f p*codegree U p.1 p.2 ∂squareMeasure) := by
  have hl := graphon_log_boundedObservable U hell hU
  have hc := codegree_boundedObservable U
  have hfL := hf.mul hl
  have hfC := hf.mul hc
  have hfirst := (hfL.comp edgeX_qmp).integrable
  have hsecond := ((((hf.comp edgeX_qmp).mul (boundedY U)).mul (boundedZ U)).const_mul μ).integrable
  have hid : (∫ p, f p*Real.log (U p) ∂squareMeasure) =
      -μTilde*(∫ p, f p*codegree U p.1 p.2 ∂squareMeasure) := by
    calc
      _ = ∫ p, -μTilde*(f p*codegree U p.1 p.2) ∂squareMeasure := by
        apply integral_congr_ae
        filter_upwards [hEL] with p hp
        rw [hp]
        ring
      _ = _ := integral_const_mul _ _
  calc
    _ = ∫ p, (f p.1*Real.log (U p.1)) + μ*(f p.1*Y U p*Z U p) ∂tripleMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by ring
    _ = (∫ p, f p.1*Real.log (U p.1) ∂tripleMeasure) +
        μ*(∫ p, f p.1*Y U p*Z U p ∂tripleMeasure) := by
      rw [integral_add hfirst hsecond, integral_const_mul]
    _ = _ := by rw [integral_first hfL, integral_test_codegree U hf, hid]; ring

theorem integral_mul_log_of_EL (U : Graphon) {μTilde : ℝ}
    (hEL : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μTilde*codegree U p.1 p.2) :
    (∫ p, U p*Real.log (U p) ∂squareMeasure) = -μTilde*triangle U := by
  rw [triangle_eq_integral_codegree]
  calc
    _ = ∫ p, -μTilde*(U p*codegree U p.1 p.2) ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [hEL] with p hp
      rw [hp]
      ring
    _ = _ := integral_const_mul _ _

/-- The cyclic expansion reduces the full expectation to one tested edge. -/
theorem expectation_cyclic (z : ℝ) (U : Graphon) {ell : ℝ} (hell : 0 < ell)
    (hU : ∀ᵐ p ∂squareMeasure, ell ≤ U p) :
    expectation z U = 3*(∫ p, localTerm z (X U p) (Y U p) (Z U p) ∂tripleMeasure)+triangle U := by
  have hl := graphon_log_boundedObservable U hell hU
  have h1 := localTerm_bounded z (boundedX U) (boundedY U) (boundedZ U) (hl.comp edgeX_qmp)
  have h2 := localTerm_bounded z (boundedY U) (boundedZ U) (boundedX U) (hl.comp edgeY_qmp)
  have h3 := localTerm_bounded z (boundedZ U) (boundedX U) (boundedY U) (hl.comp edgeZ_qmp)
  have ht := ((boundedX U).mul (boundedY U)).mul (boundedZ U)
  unfold expectation
  simp_rw [psi_cyclic_rewrite]
  rw [integral_add ((h1.add h2).add h3).integrable ht.integrable,
    integral_add (h1.add h2).integrable h3.integrable,
    integral_add h1.integrable h2.integrable, integral_XYZ]
  rw [integral_cycle U (localTerm z)]
  have hrot := integral_cycle U (fun x y w => localTerm z w x y)
  change (∫ p, localTerm z (X U p) (Y U p) (Z U p) ∂tripleMeasure) =
    ∫ p, localTerm z (Z U p) (X U p) (Y U p) ∂tripleMeasure at hrot
  rw [← hrot]
  ring

/-- Evaluation of one cyclic term, with every integrability condition derived
from the graphon bounds and its positive lower bound. -/
theorem integral_localTerm_of_EL (z : ℝ) (U : Graphon) {ell μTilde : ℝ} (hell : 0 < ell)
    (hU : ∀ᵐ p ∂squareMeasure, ell ≤ U p)
    (hEL : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μTilde*codegree U p.1 p.2) :
    (∫ p, localTerm z (X U p) (Y U p) (Z U p) ∂tripleMeasure) =
      c0 z+c1 z*edgeDensity U-c2 z*μTilde*triangle U +
      (branchMu z-μTilde)*(c3 z*(∫ p, codegree U p.1 p.2 ∂squareMeasure)+
        c4 z*(∫ p, U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure)) := by
  have hu := graphon_boundedObservable U
  have hl := graphon_log_boundedObservable U hell hU
  have hul := hu.mul hl
  have hc := codegree_boundedObservable U
  let f : ℝ × ℝ → ℝ := fun p => c3 z+c4 z*U p*Real.log (U p)
  have hf : BoundedObservable squareMeasure f :=
    (BoundedObservable.const (c3 z)).add ((hu.const_mul (c4 z)).mul hl)
  have h0 : BoundedObservable tripleMeasure (fun _ => c0 z) := BoundedObservable.const _
  have h1 := (boundedX U).const_mul (c1 z)
  have h2 := ((boundedX U).const_mul (c2 z)).mul (hl.comp edgeX_qmp)
  have hR := (hf.comp edgeX_qmp).mul
    ((hl.comp edgeX_qmp).add (((boundedY U).const_mul (branchMu z)).mul (boundedZ U)))
  have hfC : (∫ p, f p*codegree U p.1 p.2 ∂squareMeasure) =
      c3 z*(∫ p, codegree U p.1 p.2 ∂squareMeasure)+
        c4 z*(∫ p, U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure) := by
    calc
      _ = ∫ p, c3 z*codegree U p.1 p.2+
          c4 z*(U p*Real.log (U p)*codegree U p.1 p.2) ∂squareMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by dsimp [f]; ring
      _ = _ := by rw [integral_add (hc.const_mul _).integrable
        ((hul.mul hc).const_mul _).integrable, integral_const_mul, integral_const_mul]
  change BoundedObservable tripleMeasure (fun p => c2 z*X U p*Real.log (X U p)) at h2
  change BoundedObservable tripleMeasure (fun p =>
    (c3 z+c4 z*X U p*Real.log (X U p))*(Real.log (X U p)+branchMu z*Y U p*Z U p)) at hR
  unfold localTerm
  rw [integral_add ((h0.add h1).add h2).integrable hR.integrable,
    integral_add (h0.add h1).integrable h2.integrable,
    integral_add h0.integrable h1.integrable]
  have hterm2 : (∫ p, c2 z*X U p*Real.log (X U p) ∂tripleMeasure) =
      c2 z*(∫ p, U p*Real.log (U p) ∂squareMeasure) := by
    calc
      _ = ∫ p, c2 z*(X U p*Real.log (X U p)) ∂tripleMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by ring
      _ = _ := by rw [integral_const_mul, integral_X U (f := fun x => x*Real.log x) hul]
  rw [hterm2, integral_mul_log_of_EL U hEL]
  have hres := integral_test_residual U hell hU (μ := branchMu z) hEL hf
  change (∫ p, (c3 z+c4 z*X U p*Real.log (X U p))*
    (Real.log (X U p)+branchMu z*Y U p*Z U p) ∂tripleMeasure) = _ at hres
  rw [hres, hfC, integral_const_mul, integral_X U (f := fun x => x) hu]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  unfold edgeDensity
  ring

/-- `s8:expectid`: the certificate expectation identity for actual graphons.
The matching triangle density, positive lower bound, and EL equation are
exactly the manuscript hypotheses. No certificate positivity is assumed. -/
theorem expectation_identity (z : ℝ) (U : Graphon) {ell μTilde : ℝ} (hell : 0 < ell)
    (hU : ∀ᵐ p ∂squareMeasure, ell ≤ U p)
    (ht : triangle U = balancedTriangle (branchA z) (branchB z))
    (hEL : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μTilde*codegree U p.1 p.2) :
    expectation z U = 3*c1 z*(edgeDensity U-(branchA z+branchB z)/2) +
      3*(branchMu z-μTilde)*
        (c2 z*balancedTriangle (branchA z) (branchB z) +
          c3 z*(∫ p, codegree U p.1 p.2 ∂squareMeasure) +
          c4 z*(∫ p, U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure)) := by
  rw [expectation_cyclic z U hell hU, integral_localTerm_of_EL z U hell hU hEL, ht]
  unfold c0
  ring

/-- The expected certificate vanishes on its own stationary balanced graphon,
using the graphon expectation identity and its actual EL equation. -/
theorem expectation_branch_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    expectation z (branchGraphon z hz hz1) = 0 := by
  classical
  let U := branchGraphon z hz hz1
  have hbal : IsBalanced U (branchA z) (branchB z) := branchGraphon_isBalanced hz hz1
  have hlow : ∀ᵐ p ∂squareMeasure, branchA z ≤ U p := by
    obtain ⟨P, _, _, _, heq⟩ := hbal
    filter_upwards [heq] with p hp
    rw [hp]
    split_ifs
    · exact le_rfl
    · exact (branchA_lt_branchB hz1).le
  obtain ⟨ha, hb⟩ := hbal.values_mem_Icc
  have ht := hbal.triangle_eq ha hb
  have h := expectation_identity z U (branchA_pos hz) hlow ht
    (branchGraphon_ae_log_equation hz hz1)
  rw [hbal.edgeDensity_eq] at h
  simpa using h

end SparseLowerTail.Certificate

import SparseLowerTail.Section05.SupportBounds
import SparseLowerTail.Section08.CertificateExpectation

/-! Actual minimizer moment identities used by `lem:valid`, conditions T2/T3.
The test is an arbitrary bounded observable on the sampled edge, so the
paper's polynomial and u log u tests are special cases. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section05
open Section04 TriangleIntegration

/-- Euler tests have zero expectation under the actual sampled-triangle law. -/
theorem minimizer_edge_test {r : ℝ} (hr : r ∈ Ioo 0 1)
    {U : Graphon} (hU : IsMinimizer r U) {f : ℝ × ℝ → ℝ}
    (hf : BoundedObservable squareMeasure f) :
    (∫ p, f p.1 * (Real.log (X U p) + graphonMultiplier U r*Y U p*Z U p)
      ∂tripleMeasure) = 0 := by
  have h := Certificate.integral_test_residual U
    (μ := graphonMultiplier U r) (Real.exp_pos _)
    (minimizer_lower_bound hr hU) (minimizer_log_equation hr hU) hf
  simpa [X] using h

/-- The vertex entropy has the specified constant row integral. -/
theorem minimizer_vertex_row (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, (∫ y, vertexEntropy (U (x,y)) ∂unitMeasure) = vertexMean U r := by
  filter_upwards [minimizer_row_vertexEntropy hr hU,
    minimizer_vertex_stationary hSampling hr hU] with x hx hy
  exact hx.trans hy

/-- Vertex tests have zero expectation. Fubini is justified by boundedness;
the row equation is derived from minimizer optimality, not assumed. -/
theorem minimizer_vertex_test_moment (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U)
    {f : ℝ × ℝ → ℝ} (hf : BoundedObservable squareMeasure f) :
    (∫ p, f p.1 * (vertexEntropy (Y U p)+vertexEntropy (Z U p)-2*vertexMean U r)
      ∂tripleMeasure) = 0 := by
  have hk := graphon_vertexEntropy_bounded U
  have hy := hk.comp edgeY_qmp
  have hz := hk.comp edgeZ_qmp
  have hb := (hf.comp edgeX_qmp).mul
    ((hy.add hz).add (BoundedObservable.const (-2*vertexMean U r)))
  have hi : Integrable (fun p => f p.1 *
      (vertexEntropy (Y U p)+vertexEntropy (Z U p)-2*vertexMean U r)) tripleMeasure := by
    simpa only [sub_eq_add_neg, neg_mul] using hb.integrable
  rw [integral_prod _ hi]
  apply integral_eq_zero_of_ae
  have hrow := minimizer_vertex_row hSampling hr hU
  have hri := hk.integrable.prod_right_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrow,
    Measure.quasiMeasurePreserving_snd.ae hrow,
    Measure.quasiMeasurePreserving_fst.ae hri,
    Measure.quasiMeasurePreserving_snd.ae hri] with p hx hy hix hiy
  change (∫ z, f p * (vertexEntropy (U (p.2,z)) +
    vertexEntropy (U (p.1,z))-2*vertexMean U r) ∂unitMeasure) = 0
  rw [integral_const_mul]
  have hadd : Integrable (fun z => vertexEntropy (U (p.2,z)) +
      vertexEntropy (U (p.1,z))) unitMeasure := hiy.add hix
  rw [integral_sub hadd (integrable_const (2*vertexMean U r)),
    integral_add hiy hix, hx, hy]
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  ring

end SparseLowerTail.Section05

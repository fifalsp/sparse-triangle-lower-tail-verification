import SparseLowerTail.Foundations

/-! Triangle integrability and invariance under changing null sets. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace SparseLowerTail

private theorem edge12_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.1))
      cubeMeasure squareMeasure :=
  MeasureTheory.QuasiMeasurePreserving.prodMap
    (QuasiMeasurePreserving.id unitMeasure) quasiMeasurePreserving_fst

private theorem edge23_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.2.1, p.2.2))
      cubeMeasure squareMeasure := quasiMeasurePreserving_snd

private theorem edge13_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.2))
      cubeMeasure squareMeasure :=
  MeasureTheory.QuasiMeasurePreserving.prodMap
    (QuasiMeasurePreserving.id unitMeasure) quasiMeasurePreserving_snd

theorem triangle_integrand_bounds (U : Graphon) :
    ∀ᵐ p : ℝ × (ℝ × ℝ) ∂cubeMeasure,
      U (p.1, p.2.1) * U (p.2.1, p.2.2) * U (p.1, p.2.2) ∈ Icc 0 1 := by
  filter_upwards [edge12_qmp.ae U.bounded, edge23_qmp.ae U.bounded,
    edge13_qmp.ae U.bounded] with p h12 h23 h13
  constructor
  · exact mul_nonneg (mul_nonneg h12.1 h23.1) h13.1
  · calc
      _ ≤ 1 * 1 * 1 := mul_le_mul
        (mul_le_mul h12.2 h23.2 h23.1 (by norm_num)) h13.2 h13.1 (by norm_num)
      _ = 1 := by norm_num

theorem triangle_integrable (U : Graphon) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      U (p.1, p.2.1) * U (p.2.1, p.2.2) * U (p.1, p.2.2)) cubeMeasure := by
  have hm := ((U.measurable.comp_quasiMeasurePreserving edge12_qmp).mul
    (U.measurable.comp_quasiMeasurePreserving edge23_qmp)).mul
    (U.measurable.comp_quasiMeasurePreserving edge13_qmp)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [triangle_integrand_bounds U] with p hp
  change ‖U (p.1, p.2.1) * U (p.2.1, p.2.2) * U (p.1, p.2.2)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
  exact hp.2

theorem triangle_nonneg (U : Graphon) : 0 ≤ triangle U :=
  integral_nonneg_of_ae ((triangle_integrand_bounds U).mono fun _ hp => hp.1)

theorem triangle_le_one (U : Graphon) : triangle U ≤ 1 := by
  have h := integral_mono_ae (triangle_integrable U) (integrable_const (1 : ℝ))
    ((triangle_integrand_bounds U).mono fun _ hp => hp.2)
  simpa [triangle] using h

theorem cost_congr_ae {U W : Graphon} (heq : U.toFun =ᵐ[squareMeasure] W.toFun) :
    cost U = cost W := integral_congr_ae (heq.fun_comp entropy)

theorem triangle_congr_ae {U W : Graphon}
    (heq : U.toFun =ᵐ[squareMeasure] W.toFun) : triangle U = triangle W := by
  apply integral_congr_ae
  filter_upwards [edge12_qmp.ae heq, edge23_qmp.ae heq, edge13_qmp.ae heq]
    with p h12 h23 h13
  change U (p.1, p.2.1) = W (p.1, p.2.1) at h12
  change U (p.2.1, p.2.2) = W (p.2.1, p.2.2) at h23
  change U (p.1, p.2.2) = W (p.1, p.2.2) at h13
  rw [h12, h23, h13]

theorem isMinimizer_congr_ae {r : ℝ} {U W : Graphon}
    (heq : U.toFun =ᵐ[squareMeasure] W.toFun) :
    IsMinimizer r U ↔ IsMinimizer r W := by
  simp only [isMinimizer_iff, Feasible, cost_congr_ae heq, triangle_congr_ae heq]

end SparseLowerTail

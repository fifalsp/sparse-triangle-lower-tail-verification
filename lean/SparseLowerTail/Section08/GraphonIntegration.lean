import SparseLowerTail.Section04.BalancedStationary

/-! Bounded observables and genuine product-measure identities used by `s8:expect`. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace SparseLowerTail

/-- A measurable real observable with a finite almost-everywhere uniform bound. -/
structure BoundedObservable {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) : Prop where
  measurable : AEMeasurable f μ
  bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ K

namespace BoundedObservable
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {f g : α → ℝ}

theorem integrable [IsFiniteMeasure μ] (hf : BoundedObservable μ f) : Integrable f μ := by
  obtain ⟨K, _, hK⟩ := hf.bound
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable K hK

theorem const (c : ℝ) : BoundedObservable μ (fun _ => c) :=
  ⟨aemeasurable_const, |c|, abs_nonneg c, Filter.Eventually.of_forall (by simp)⟩

theorem add (hf : BoundedObservable μ f) (hg : BoundedObservable μ g) :
    BoundedObservable μ (fun x => f x+g x) := by
  obtain ⟨K, hK, hfK⟩ := hf.bound
  obtain ⟨L, hL, hgL⟩ := hg.bound
  refine ⟨hf.measurable.add hg.measurable, K+L, add_nonneg hK hL, ?_⟩
  filter_upwards [hfK, hgL] with x hx hy
  exact (norm_add_le _ _).trans (add_le_add hx hy)

theorem mul (hf : BoundedObservable μ f) (hg : BoundedObservable μ g) :
    BoundedObservable μ (fun x => f x*g x) := by
  obtain ⟨K, hK, hfK⟩ := hf.bound
  obtain ⟨L, hL, hgL⟩ := hg.bound
  refine ⟨hf.measurable.mul hg.measurable, K*L, mul_nonneg hK hL, ?_⟩
  filter_upwards [hfK, hgL] with x hx hy
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) hK

theorem const_mul (hf : BoundedObservable μ f) (c : ℝ) :
    BoundedObservable μ (fun x => c*f x) := (const c).mul hf

theorem mul_const (hf : BoundedObservable μ f) (c : ℝ) :
    BoundedObservable μ (fun x => f x*c) := hf.mul (const c)

theorem comp {T : β → α} (hf : BoundedObservable μ f)
    (hT : QuasiMeasurePreserving T ν μ) : BoundedObservable ν (fun x => f (T x)) := by
  obtain ⟨K, hK, hfK⟩ := hf.bound
  exact ⟨hf.measurable.comp_quasiMeasurePreserving hT, K, hK, hT.ae hfK⟩

theorem integral_left [SFinite μ] [IsProbabilityMeasure ν] {F : α × β → ℝ}
    (hF : BoundedObservable (μ.prod ν) F) :
    BoundedObservable μ (fun x => ∫ y, F (x,y) ∂ν) := by
  obtain ⟨K, hK, hFK⟩ := hF.bound
  refine ⟨hF.measurable.aestronglyMeasurable.integral_prod_right'.aemeasurable, K, hK, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hFK] with x hx
  simpa using norm_integral_le_of_norm_le_const hx

end BoundedObservable

theorem graphon_boundedObservable (U : Graphon) : BoundedObservable squareMeasure U.toFun := by
  refine ⟨U.measurable, 1, by norm_num, ?_⟩
  filter_upwards [U.bounded] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
  exact hp.2

theorem graphon_log_boundedObservable (U : Graphon) {ell : ℝ} (hell : 0 < ell)
    (hU : ∀ᵐ p ∂squareMeasure, ell ≤ U p) :
    BoundedObservable squareMeasure (fun p => Real.log (U p)) := by
  refine ⟨Real.measurable_log.comp_aemeasurable U.measurable, |Real.log ell|,
    abs_nonneg _, ?_⟩
  filter_upwards [hU, U.bounded] with p hp hbp
  have hlogL := Real.log_le_log hell hp
  have hlogU := Real.log_nonpos hbp.1 hbp.2
  rw [Real.norm_eq_abs, abs_of_nonpos hlogU]
  linarith [neg_le_abs (Real.log ell)]

namespace TriangleIntegration

abbrev tripleMeasure : Measure ((ℝ × ℝ) × ℝ) := squareMeasure.prod unitMeasure

def X (U : Graphon) (p : (ℝ × ℝ) × ℝ) := U (p.1.1,p.1.2)
def Y (U : Graphon) (p : (ℝ × ℝ) × ℝ) := U (p.1.2,p.2)
def Z (U : Graphon) (p : (ℝ × ℝ) × ℝ) := U (p.1.1,p.2)

theorem edgeX_qmp : QuasiMeasurePreserving (fun p : (ℝ × ℝ) × ℝ => p.1)
    tripleMeasure squareMeasure := Measure.quasiMeasurePreserving_fst

theorem edgeY_qmp : QuasiMeasurePreserving (fun p : (ℝ × ℝ) × ℝ => (p.1.2,p.2))
    tripleMeasure squareMeasure :=
  MeasureTheory.QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_snd
    (QuasiMeasurePreserving.id unitMeasure)

theorem edgeZ_qmp : QuasiMeasurePreserving (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.2))
    tripleMeasure squareMeasure :=
  MeasureTheory.QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_fst
    (QuasiMeasurePreserving.id unitMeasure)

theorem boundedX (U : Graphon) : BoundedObservable tripleMeasure (X U) :=
  (graphon_boundedObservable U).comp edgeX_qmp

theorem boundedY (U : Graphon) : BoundedObservable tripleMeasure (Y U) :=
  (graphon_boundedObservable U).comp edgeY_qmp

theorem boundedZ (U : Graphon) : BoundedObservable tripleMeasure (Z U) :=
  (graphon_boundedObservable U).comp edgeZ_qmp

/-- Cyclic permutation of independently sampled vertices preserves measure. -/
def cycle : ((ℝ × ℝ) × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm

theorem cycle_preserving : MeasurePreserving cycle tripleMeasure tripleMeasure :=
  Measure.measurePreserving_swap.comp
    (measurePreserving_prodAssoc unitMeasure unitMeasure unitMeasure)

/-- Cyclic symmetry of triangle-edge observables, including a.e.-symmetric
rather than pointwise-symmetric graphon representatives. -/
theorem integral_cycle (U : Graphon) (F : ℝ → ℝ → ℝ → ℝ) :
    (∫ p, F (Y U p) (Z U p) (X U p) ∂tripleMeasure) =
      ∫ p, F (X U p) (Y U p) (Z U p) ∂tripleMeasure := by
  calc
    _ = ∫ p, F (X U (cycle p)) (Y U (cycle p)) (Z U (cycle p)) ∂tripleMeasure := by
      apply integral_congr_ae
      filter_upwards [edgeZ_qmp.ae U.symmetric, edgeX_qmp.ae U.symmetric] with p hZ hX
      change U (p.2,p.1.1) = U (p.1.1,p.2) at hZ
      change U (p.1.2,p.1.1) = U (p.1.1,p.1.2) at hX
      change F (Y U p) (Z U p) (X U p) =
        F (U (p.1.2,p.2)) (U (p.2,p.1.1)) (U (p.1.2,p.1.1))
      rw [hZ, hX]
      rfl
    _ = _ := cycle_preserving.integral_comp cycle.measurableEmbedding
      (fun p => F (X U p) (Y U p) (Z U p))

/-- Fubini isolates the conditional codegree without a conditional-expectation
abstraction. The test function is genuinely bounded and measurable. -/
theorem integral_test_codegree (U : Graphon) {f : ℝ × ℝ → ℝ}
    (hf : BoundedObservable squareMeasure f) :
    (∫ p, f p.1*Y U p*Z U p ∂tripleMeasure) =
      ∫ p, f p*codegree U p.1 p.2 ∂squareMeasure := by
  have hF := ((hf.comp edgeX_qmp).mul (boundedY U)).mul (boundedZ U)
  rw [integral_prod _ hF.integrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    change (∫ z, f p*U (p.2,z)*U (p.1,z) ∂unitMeasure) = _
    rw [show (fun z => f p*U (p.2,z)*U (p.1,z)) =
      (fun z => f p*(U (p.1,z)*U (p.2,z))) by funext z; ring,
      integral_const_mul]
    rfl

theorem integral_X (U : Graphon) {f : ℝ → ℝ}
    (hf : BoundedObservable squareMeasure (fun p => f (U p))) :
    (∫ p, f (X U p) ∂tripleMeasure) = ∫ p, f (U p) ∂squareMeasure := by
  change (∫ p, f (U p.1) ∂tripleMeasure) = _
  rw [integral_prod _ (hf.comp edgeX_qmp).integrable]
  simp

/-- Compatibility of the left-associated product integral with the existing
triangle density definition. -/
theorem integral_XYZ (U : Graphon) :
    (∫ p, X U p*Y U p*Z U p ∂tripleMeasure) = triangle U := by
  exact (measurePreserving_prodAssoc unitMeasure unitMeasure unitMeasure).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
      (fun p : ℝ × (ℝ × ℝ) => U (p.1,p.2.1)*U (p.2.1,p.2.2)*U (p.1,p.2.2))

end TriangleIntegration

/-- `lem:trilinear`: the actual triangle density is the integral of U times its
codegree kernel. -/
theorem triangle_eq_integral_codegree (U : Graphon) :
    triangle U = ∫ p, U p*codegree U p.1 p.2 ∂squareMeasure := by
  rw [← TriangleIntegration.integral_XYZ]
  exact TriangleIntegration.integral_test_codegree U (graphon_boundedObservable U)

theorem codegree_boundedObservable (U : Graphon) :
    BoundedObservable squareMeasure (fun p : ℝ × ℝ => codegree U p.1 p.2) := by
  have h := ((TriangleIntegration.boundedZ U).mul (TriangleIntegration.boundedY U)).integral_left
  exact h

end SparseLowerTail

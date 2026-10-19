import SparseLowerTail.Section02.CutNorm

/-! Genuine measure-preserving pullbacks and their graphon integral invariances. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- A measure-preserving vertex map. Bijections are included; invertibility is unnecessary here. -/
structure Relabeling where
  toFun : ℝ → ℝ
  preserving : MeasurePreserving toFun unitMeasure unitMeasure

instance : CoeFun Relabeling (fun _ => ℝ → ℝ) := ⟨Relabeling.toFun⟩

def relabel (U : Graphon) (φ : Relabeling) : Graphon where
  toFun p := U (φ p.1,φ p.2)
  measurable := U.measurable.comp_quasiMeasurePreserving (φ.preserving.prod φ.preserving).quasiMeasurePreserving
  symmetric := (φ.preserving.prod φ.preserving).quasiMeasurePreserving.ae U.symmetric
  bounded := (φ.preserving.prod φ.preserving).quasiMeasurePreserving.ae U.bounded

/-- Change of variables needs no injectivity when the integrand is integrable. -/
theorem integral_comp_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {φ : α → β} (hφ : MeasurePreserving φ μ ν)
    {f : β → ℝ} (hf : Integrable f ν) : (∫ x, f (φ x) ∂μ) = ∫ y, f y ∂ν := by
  have hm : AEStronglyMeasurable f (Measure.map φ μ) := by
    rw [hφ.map_eq]
    exact hf.aestronglyMeasurable
  have h := integral_map hφ.measurable.aemeasurable hm
  rw [hφ.map_eq] at h
  exact h.symm

@[simp] theorem cost_relabel (U : Graphon) (φ : Relabeling) : cost (relabel U φ)=cost U :=
  integral_comp_preserving (φ.preserving.prod φ.preserving) (cost_integrable U)

@[simp] theorem triangle_relabel (U : Graphon) (φ : Relabeling) : triangle (relabel U φ)=triangle U :=
  integral_comp_preserving (φ.preserving.prod (φ.preserving.prod φ.preserving)) (triangle_integrable U)

@[simp] theorem edgeDensity_relabel (U : Graphon) (φ : Relabeling) : edgeDensity (relabel U φ)=edgeDensity U :=
  integral_comp_preserving (φ.preserving.prod φ.preserving) (graphon_integrable U)

/-- Classical graphon compactness modulo measure-preserving vertex maps.
This exact input contains no variational or entropy assertion. -/
def ClassicalGraphonCompactness : Prop :=
  ∀ U : ℕ → Graphon, ∃ W : Graphon, ∃ σ : ℕ → ℕ, ∃ φ : ℕ → Relabeling,
    StrictMono σ ∧ CutConverges (fun n => relabel (U (σ n)) (φ n)) W

/-- The classical triangle counting bound for the actual rectangle cut norm. -/
def ClassicalTriangleCounting : Prop :=
  ∀ U W : Graphon, |triangle U-triangle W| ≤ 3*cutNorm (fun p => U p-W p)

/-- The counting input implies triangle-density convergence. -/
theorem CutConverges.triangle (hcount : ClassicalTriangleCounting)
    {U : ℕ → Graphon} {W : Graphon} (h : CutConverges U W) :
    Tendsto (fun n => triangle (U n)) atTop (𝓝 (triangle W)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => hcount (U n) W)
  simpa only [mul_zero] using h.const_mul 3

end SparseLowerTail.Section02

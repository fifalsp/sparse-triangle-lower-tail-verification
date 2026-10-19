import SparseLowerTail.Section08.GraphonIntegration
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The genuine rectangle cut norm on the Lebesgue unit square. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- Integrating a kernel over a measurable rectangle. Measures already restrict to [0,1]. -/
def rectangleIntegral (K : ℝ × ℝ → ℝ) (S T : Set ℝ) : ℝ :=
  ∫ p in S ×ˢ T, K p ∂squareMeasure

/-- The usual cut norm as a supremum of absolute rectangle integrals. -/
def cutNorm (K : ℝ × ℝ → ℝ) : ℝ :=
  sSup {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧ |rectangleIntegral K S T|=v}

private theorem rectangle_values_nonempty (K : ℝ × ℝ → ℝ) :
    {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧ |rectangleIntegral K S T|=v}.Nonempty := by
  exact ⟨0, ∅, ∅, MeasurableSet.empty, MeasurableSet.empty, by simp [rectangleIntegral]⟩

theorem abs_rectangleIntegral_le_l1 {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure)
    (S T : Set ℝ) : |rectangleIntegral K S T| ≤ ∫ p, |K p| ∂squareMeasure := by
  calc
    _ ≤ ∫ p in S ×ˢ T, |K p| ∂squareMeasure := by
      simpa only [rectangleIntegral, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f := K) (μ := squareMeasure.restrict (S ×ˢ T))
    _ ≤ _ := setIntegral_le_integral hK.norm (Filter.Eventually.of_forall fun p => abs_nonneg (K p))

private theorem rectangle_values_bddAbove {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure) :
    BddAbove {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧ |rectangleIntegral K S T|=v} := by
  refine ⟨∫ p, |K p| ∂squareMeasure, ?_⟩
  rintro v ⟨S,T,_,_,rfl⟩
  exact abs_rectangleIntegral_le_l1 hK S T

/-- Every measurable rectangle integral is controlled by the genuine cut norm. -/
theorem abs_rectangleIntegral_le_cutNorm {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    |rectangleIntegral K S T| ≤ cutNorm K :=
  le_csSup (rectangle_values_bddAbove hK) ⟨S,T,hS,hT,rfl⟩

theorem cutNorm_nonneg {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure) : 0 ≤ cutNorm K := by
  have h := abs_rectangleIntegral_le_cutNorm hK MeasurableSet.empty MeasurableSet.empty
  simpa only [rectangleIntegral, empty_prod, Measure.restrict_empty, integral_zero_measure, abs_zero] using h

/-- The cut norm is at most the L¹ norm. -/
theorem cutNorm_le_l1 {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure) :
    cutNorm K ≤ ∫ p, |K p| ∂squareMeasure := by
  apply csSup_le (rectangle_values_nonempty K)
  rintro v ⟨S,T,_,_,rfl⟩
  exact abs_rectangleIntegral_le_l1 hK S T

theorem rectangleIntegral_sub {K L : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure) (S T : Set ℝ) :
    rectangleIntegral (fun p => K p-L p) S T = rectangleIntegral K S T-rectangleIntegral L S T :=
  integral_sub hK.integrableOn hL.integrableOn

theorem cutNorm_add_le {K L : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure) :
    cutNorm (fun p => K p+L p) ≤ cutNorm K+cutNorm L := by
  apply csSup_le (rectangle_values_nonempty _)
  rintro v ⟨S,T,hS,hT,rfl⟩
  have he : rectangleIntegral (fun p => K p+L p) S T = rectangleIntegral K S T+rectangleIntegral L S T :=
    integral_add hK.integrableOn hL.integrableOn
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_rectangleIntegral_le_cutNorm hK hS hT)
    (abs_rectangleIntegral_le_cutNorm hL hS hT))

@[simp] theorem cutNorm_zero : cutNorm (fun _ : ℝ × ℝ => (0:ℝ)) = 0 := by
  apply le_antisymm
  · simpa using cutNorm_le_l1 (integrable_const (μ := squareMeasure) (0:ℝ))
  · exact cutNorm_nonneg (integrable_const (0:ℝ))

/-- Cut convergence of actual graphon representatives, before any quotient/relabeling. -/
def CutConverges (U : ℕ → Graphon) (W : Graphon) : Prop :=
  Tendsto (fun n => cutNorm (fun p => U n p-W p)) atTop (𝓝 0)

/-- The basic finite-block consequence of cut convergence. -/
theorem CutConverges.rectangle_integral {U : ℕ → Graphon} {W : Graphon}
    (h : CutConverges U W) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Tendsto (fun n => rectangleIntegral (U n).toFun S T) atTop (𝓝 (rectangleIntegral W.toFun S T)) := by
  have hb : ∀ n, |rectangleIntegral (U n).toFun S T-rectangleIntegral W.toFun S T| ≤
      cutNorm (fun p => U n p-W p) := by
    intro n
    rw [← rectangleIntegral_sub (graphon_integrable (U n)) (graphon_integrable W)]
    exact abs_rectangleIntegral_le_cutNorm ((graphon_integrable (U n)).sub (graphon_integrable W)) hS hT
  have ha := squeeze_zero (fun n => abs_nonneg
    (rectangleIntegral (U n).toFun S T-rectangleIntegral W.toFun S T)) hb h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ha)

end SparseLowerTail.Section02

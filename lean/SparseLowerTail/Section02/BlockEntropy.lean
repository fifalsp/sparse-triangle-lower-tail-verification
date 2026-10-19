import SparseLowerTail.Section02.CutNorm
import SparseLowerTail.Section04.EntropyGeometry
import Mathlib.Analysis.Convex.Integral

/-! The finite-rectangle Jensen and continuity steps in manuscript lem:lsc. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- Average graphon value on a rectangle, with value zero on null rectangles. -/
def rectangleMean (U : Graphon) (S T : Set ℝ) : ℝ :=
  (squareMeasure.real (S ×ˢ T))⁻¹*rectangleIntegral U.toFun S T

/-- Contribution of one averaged rectangle to the entropy integral. -/
def rectangleEntropy (U : Graphon) (S T : Set ℝ) : ℝ :=
  squareMeasure.real (S ×ˢ T)*entropy (rectangleMean U S T)

/-- Jensen's inequality on an actual measurable rectangle, including null rectangles. -/
theorem rectangleEntropy_le (U : Graphon) (S T : Set ℝ) :
    rectangleEntropy U S T ≤ ∫ p in S ×ˢ T, entropy (U p) ∂squareMeasure := by
  by_cases hnull : squareMeasure (S ×ˢ T)=0
  · simp [rectangleEntropy, measureReal_def, hnull, Measure.restrict_eq_zero.mpr hnull]
  · have hw : 0 < squareMeasure.real (S ×ˢ T) :=
      ENNReal.toReal_pos hnull (measure_ne_top _ _)
    have hj := Section04.strictConvexOn_entropy.convexOn.map_set_average_le
      continuous_entropy.continuousOn isClosed_Ici hnull (measure_ne_top _ _)
      (show ∀ᵐ p ∂squareMeasure.restrict (S ×ˢ T), U p ∈ Ici (0:ℝ) from
        ae_restrict_of_ae (U.bounded.mono fun _ hp => hp.1))
      (graphon_integrable U).integrableOn (cost_integrable U).integrableOn
    rw [setAverage_eq, setAverage_eq] at hj
    simp only [smul_eq_mul] at hj
    have hm := mul_le_mul_of_nonneg_left hj hw.le
    unfold rectangleEntropy rectangleMean rectangleIntegral
    simpa only [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul] using hm

/-- Every fixed block contribution is continuous along cut-convergent graphons. -/
theorem CutConverges.rectangle_entropy {U : ℕ → Graphon} {W : Graphon}
    (h : CutConverges U W) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Tendsto (fun n => rectangleEntropy (U n) S T) atTop (𝓝 (rectangleEntropy W S T)) := by
  have hmean := (h.rectangle_integral hS hT).const_mul (squareMeasure.real (S ×ˢ T))⁻¹
  have hent := continuous_entropy.continuousAt.tendsto.comp hmean
  exact hent.const_mul _

/-- A finite collection of disjoint measurable rectangles. It need not cover the square. -/
structure RectangleFamily (ι : Type*) [Fintype ι] where
  left : ι → Set ℝ
  right : ι → Set ℝ
  measurable_left : ∀ i, MeasurableSet (left i)
  measurable_right : ∀ i, MeasurableSet (right i)
  disjoint : Pairwise (fun i j => Disjoint (left i ×ˢ right i) (left j ×ˢ right j))

def blockEntropy {ι : Type*} [Fintype ι] (P : RectangleFamily ι) (U : Graphon) : ℝ :=
  ∑ i, rectangleEntropy U (P.left i) (P.right i)

/-- Finite-block Jensen: averaging on disjoint rectangles never increases total entropy. -/
theorem blockEntropy_le_cost {ι : Type*} [Fintype ι] (P : RectangleFamily ι) (U : Graphon) :
    blockEntropy P U ≤ cost U := by
  classical
  calc
    _ ≤ ∑ i, ∫ p in P.left i ×ˢ P.right i, entropy (U p) ∂squareMeasure :=
      Finset.sum_le_sum (fun i _ => rectangleEntropy_le U (P.left i) (P.right i))
    _ = ∫ p in ⋃ i, P.left i ×ˢ P.right i, entropy (U p) ∂squareMeasure := by
      symm
      exact integral_iUnion_fintype (fun i => (P.measurable_left i).prod (P.measurable_right i))
        P.disjoint (fun _ => (cost_integrable U).integrableOn)
    _ ≤ cost U := setIntegral_le_integral (cost_integrable U)
      (U.bounded.mono fun _ hp => entropy_nonneg hp.1)

/-- Fixed finite-block entropy is continuous for the actual cut norm. -/
theorem CutConverges.block_entropy {U : ℕ → Graphon} {W : Graphon}
    (h : CutConverges U W) {ι : Type*} [Fintype ι] (P : RectangleFamily ι) :
    Tendsto (fun n => blockEntropy P (U n)) atTop (𝓝 (blockEntropy P W)) := by
  exact tendsto_finset_sum _ fun i _ => h.rectangle_entropy (P.measurable_left i) (P.measurable_right i)

end SparseLowerTail.Section02

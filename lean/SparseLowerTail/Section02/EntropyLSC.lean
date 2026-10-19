import SparseLowerTail.Section02.EntropyContinuity
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Entropy lower semicontinuity for the actual cut norm

This proves the entropy conclusions of manuscript lem:lsc. The only explicit
classical input is L¹ convergence of dyadic cell averages for integrable real
kernels. Graphon validity, Jensen, finite-block continuity, entropy convergence,
and the lower-semicontinuity argument are all proved here or in the imported
modules; none of these own-paper conclusions are included in that input.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- Full content of lem:lsc(a), with the classical approximation theorem explicit. -/
theorem dyadic_averaging (hclass : ClassicalDyadicL1Approximation) (U : Graphon) :
    (∀ k, cost (averagedGraphon (dyadicPartition k) U) ≤ cost U) ∧
    Tendsto (fun k => l1Distance (averagedGraphon (dyadicPartition k) U) U) atTop (𝓝 0) :=
  ⟨fun k => cost_averagedGraphon_le (dyadicPartition k) U,
    hclass U.toFun (graphon_integrable U)⟩

/-- Every fixed partition entropy is bounded by the liminf along a cut-convergent sequence. -/
theorem CutConverges.averaged_cost_le_liminf {U : ℕ → Graphon} {W : Graphon}
    (h : CutConverges U W) {n : ℕ} (P : VertexPartition n) :
    cost (averagedGraphon P W) ≤ liminf (fun k => cost (U k)) atTop := by
  have hconv : Tendsto (fun k => cost (averagedGraphon P (U k))) atTop
      (𝓝 (cost (averagedGraphon P W))) := by
    simpa only [cost_averagedGraphon] using h.block_entropy P.rectangles
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun k => cost (averagedGraphon P (U k))) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun k => cost_nonneg _)
  have hc : IsCoboundedUnder (· ≥ ·) atTop (fun k => cost (U k)) :=
    isCoboundedUnder_ge_of_le atTop (fun k => cost_le_one (U k))
  have hlim := liminf_le_liminf
    (Eventually.of_forall fun k => cost_averagedGraphon_le P (U k)) hb hc
  rwa [hconv.liminf_eq] at hlim

/-- Manuscript lem:lsc(b): the entropy is lower semicontinuous under genuine cut convergence. -/
theorem cost_lowerSemicontinuous_cut (hclass : ClassicalDyadicL1Approximation)
    {U : ℕ → Graphon} {W : Graphon} (h : CutConverges U W) :
    cost W ≤ liminf (fun k => cost (U k)) atTop := by
  apply le_of_tendsto (cost_dyadic_tendsto hclass W)
  exact Eventually.of_forall fun k => h.averaged_cost_le_liminf (dyadicPartition k)

/-- Frequently used limit-value version of lower semicontinuity. -/
theorem cost_le_limit_of_cut (hclass : ClassicalDyadicL1Approximation)
    {U : ℕ → Graphon} {W : Graphon} {c : ℝ} (h : CutConverges U W)
    (hc : Tendsto (fun k => cost (U k)) atTop (𝓝 c)) : cost W ≤ c := by
  simpa only [hc.liminf_eq] using cost_lowerSemicontinuous_cut hclass h

end SparseLowerTail.Section02

import SparseLowerTail.Section02.Existence
import SparseLowerTail.Section02.CutDistance
import SparseLowerTail.Section02.ValueContinuity
import SparseLowerTail.Section02.Isolation
import SparseLowerTail.Section05.ThresholdReduction

/-!
# Limits of minimizers and the limit from below the threshold

Manuscript lem:limits and lem:leftlimits for actual representatives converging
in cut norm and for the infimum cut distance over genuine measurable
measure-preserving bijections. The threshold identification is conditional on the
explicit internal proposition CriticalClassification.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section05
open Section02 Section04

/-- Edge density is continuous under the actual cut norm. -/
theorem edgeDensity_tendsto_of_cut {U : ℕ → Graphon} {W : Graphon} (h : CutConverges U W) :
    Tendsto (fun n => edgeDensity (U n)) atTop (𝓝 (edgeDensity W)) := by
  simpa only [rectangleIntegral, univ_prod_univ, setIntegral_univ, edgeDensity] using
    h.rectangle_integral MeasurableSet.univ MeasurableSet.univ

/-- The minimizer conclusion of lem:limits for cut-convergent representatives. -/
theorem minimizer_of_cut_limit (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) {r : ℝ} {rn : ℕ → ℝ}
    (hr : r ∈ Ioo (0:ℝ) 1) (hrn : ∀ n, rn n ∈ Ioo (0:ℝ) 1)
    (hrt : Tendsto rn atTop (𝓝 r)) {U : ℕ → Graphon} {W : Graphon}
    (hm : ∀ n, IsMinimizer (rn n) (U n)) (hcut : CutConverges U W) : IsMinimizer r W := by
  have htri : Tendsto (fun n => triangle (U n)) atTop (𝓝 (r^3)) := by
    simpa only [fun n => minimizer_triangle_eq (hrn n) (hm n)] using hrt.pow 3
  have ht : triangle W=r^3 := tendsto_nhds_unique (hcut.triangle hcount) htri
  have hV := (continuousOn_value.continuousAt (isOpen_Ioo.mem_nhds hr)).tendsto.comp hrt
  have hcost : Tendsto (fun n => cost (U n)) atTop (𝓝 (value r)) := by
    simpa only [fun n => (isMinimizer_iff.mp (hm n)).2] using hV
  have hlo := cost_le_limit_of_cut hdyadic hcut hcost
  exact isMinimizer_iff.mpr ⟨ht.le,le_antisymm hlo (value_le_cost ht.le)⟩

/-- Complete four conclusions of lem:limits, with explicit representatives. -/
theorem minimizer_limits (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) {r : ℝ} {rn : ℕ → ℝ}
    (hr : r ∈ Ioo (0:ℝ) 1) (hrn : ∀ n, rn n ∈ Ioo (0:ℝ) 1)
    (hrt : Tendsto rn atTop (𝓝 r)) {U : ℕ → Graphon} {W : Graphon}
    (hm : ∀ n, IsMinimizer (rn n) (U n)) (hcut : CutConverges U W) :
    IsMinimizer r W ∧
    Tendsto (fun n => edgeDensity (U n)) atTop (𝓝 (edgeDensity W)) ∧
    Tendsto (fun n => cost (U n)) atTop (𝓝 (cost W)) ∧
    Tendsto (fun n => graphonMultiplier (U n) (rn n)) atTop (𝓝 (graphonMultiplier W r)) := by
  have hW := minimizer_of_cut_limit hdyadic hcount hr hrn hrt hm hcut
  have he := edgeDensity_tendsto_of_cut hcut
  have hV := (continuousOn_value.continuousAt (isOpen_Ioo.mem_nhds hr)).tendsto.comp hrt
  have hc : Tendsto (fun n => cost (U n)) atTop (𝓝 (cost W)) := by
    simpa only [fun n => (isMinimizer_iff.mp (hm n)).2, (isMinimizer_iff.mp hW).2] using hV
  refine ⟨hW,he,hc,?_⟩
  exact ((tendsto_const_nhds.sub hc).sub he).div (hrt.pow 3) (pow_ne_zero _ hr.1.ne')

/-- Relabeling preserves the minimizer property without requiring inverse maps. -/
theorem minimizer_relabel {r : ℝ} {U : Graphon} (hU : IsMinimizer r U) (φ : Relabeling) :
    IsMinimizer r (relabel U φ) := by
  rw [isMinimizer_iff, Feasible, triangle_relabel, cost_relabel]
  exact isMinimizer_iff.mp hU

/-- The limits conclusion when cut convergence is realized after genuine relabelings. -/
theorem minimizer_limits_relabel (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) {r : ℝ} {rn : ℕ → ℝ}
    (hr : r ∈ Ioo (0:ℝ) 1) (hrn : ∀ n, rn n ∈ Ioo (0:ℝ) 1)
    (hrt : Tendsto rn atTop (𝓝 r)) {U : ℕ → Graphon} {W : Graphon}
    (hm : ∀ n, IsMinimizer (rn n) (U n)) (φ : ℕ → Relabeling)
    (hcut : CutConverges (fun n => relabel (U n) (φ n)) W) :
    IsMinimizer r W ∧
    Tendsto (fun n => edgeDensity (U n)) atTop (𝓝 (edgeDensity W)) ∧
    Tendsto (fun n => cost (U n)) atTop (𝓝 (cost W)) ∧
    Tendsto (fun n => graphonMultiplier (U n) (rn n)) atTop (𝓝 (graphonMultiplier W r)) := by
  have h := minimizer_limits hdyadic hcount hr hrn hrt
    (fun n => minimizer_relabel (hm n) (φ n)) hcut
  simpa only [edgeDensity_relabel,cost_relabel,graphonMultiplier] using h

/-- lem:leftlimits for cut-convergent representatives; nonconstant critical phase is forced. -/
theorem balanced_left_limit (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) (hcrit : CriticalClassification)
    {rn : ℕ → ℝ} (hrn : ∀ n, rn n ∈ Ioo (0:ℝ) threshold)
    (hrt : Tendsto rn atTop (𝓝 threshold)) {U : ℕ → Graphon} {W : Graphon}
    (hm : ∀ n, IsMinimizer (rn n) (U n)) (hcut : CutConverges U W) :
    IsBalanced W criticalA criticalB := by
  have hrn1 : ∀ n, rn n ∈ Ioo (0:ℝ) 1 :=
    fun n => ⟨(hrn n).1,(hrn n).2.trans threshold_mem_Ioo.2⟩
  obtain ⟨hW,he,_,_⟩ := minimizer_limits hdyadic hcount threshold_mem_Ioo hrn1 hrt hm hcut
  have hM := (continuousOn_isolatedMean.continuousAt (isOpen_Ioo.mem_nhds threshold_mem_Ioo)).tendsto.comp hrt
  have hmean : isolatedMean threshold ≤ edgeDensity W := by
    apply le_of_tendsto_of_tendsto' hM he
    intro n
    have hcost := (isMinimizer_iff.mp (hm n)).2.trans_le (value_le_entropy ⟨(hrn1 n).1.le,(hrn1 n).2.le⟩)
    have hnon : ¬IsConstant (U n) (rn n) :=
      fun hc => minimizer_nonconstant_below (hrn n) (hm n) ⟨rn n,hc⟩
    exact (isolation (hrn1 n) (hm n).1 hcost hnon).2
  rcases (minimizer_at_iff hcrit W).mp hW with hc | hb
  · have hed : edgeDensity W=threshold := by
      have h := integral_congr_ae hc
      simpa only [integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul,edgeDensity] using h
    have hg := isolatedMean_gt threshold_mem_Ioo
    exfalso
    linarith
  · exact hb

/-- The same left-limit conclusion for an explicit subsequence and relabelings. -/
theorem balanced_left_subsequence_limit (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) (hcrit : CriticalClassification)
    {rn : ℕ → ℝ} (hrn : ∀ n, rn n ∈ Ioo (0:ℝ) threshold)
    (hrt : Tendsto rn atTop (𝓝 threshold)) {U : ℕ → Graphon} {W : Graphon}
    (hm : ∀ n, IsMinimizer (rn n) (U n)) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (φ : ℕ → Relabeling) (hcut : CutConverges (fun n => relabel (U (σ n)) (φ n)) W) :
    IsBalanced W criticalA criticalB := by
  exact balanced_left_limit hdyadic hcount hcrit (fun n => hrn (σ n))
    (hrt.comp hσ.tendsto_atTop) (fun n => minimizer_relabel (hm (σ n)) (φ n)) hcut

/-- Manuscript lem:limits with the actual infimum cut-distance hypothesis. -/
theorem minimizer_limits_cutDistance (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) {r : ℝ} {rn : ℕ → ℝ}
    (hr : r ∈ Ioo (0:ℝ) 1) (hrn : ∀ n, rn n ∈ Ioo (0:ℝ) 1)
    (hrt : Tendsto rn atTop (𝓝 r)) {U : ℕ → Graphon} {W : Graphon}
    (hm : ∀ n, IsMinimizer (rn n) (U n))
    (hcut : Tendsto (fun n => cutDistance (U n) W) atTop (𝓝 0)) :
    IsMinimizer r W ∧
    Tendsto (fun n => edgeDensity (U n)) atTop (𝓝 (edgeDensity W)) ∧
    Tendsto (fun n => cost (U n)) atTop (𝓝 (cost W)) ∧
    Tendsto (fun n => graphonMultiplier (U n) (rn n)) atTop (𝓝 (graphonMultiplier W r)) := by
  obtain ⟨φ,hφ⟩ := exists_relabel_cutConverges hcut
  exact minimizer_limits_relabel hdyadic hcount hr hrn hrt hm (fun n => (φ n).toRelabeling) hφ

/-- Manuscript lem:leftlimits with its original cut-distance subsequence hypothesis. -/
theorem balanced_left_limit_cutDistance (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) (hcrit : CriticalClassification)
    {rn : ℕ → ℝ} (hrn : ∀ n, rn n ∈ Ioo (0:ℝ) threshold)
    (hrt : Tendsto rn atTop (𝓝 threshold)) {U : ℕ → Graphon} {W : Graphon}
    (hm : ∀ n, IsMinimizer (rn n) (U n)) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hcut : Tendsto (fun n => cutDistance (U (σ n)) W) atTop (𝓝 0)) :
    IsBalanced W criticalA criticalB := by
  obtain ⟨φ,hφ⟩ := exists_relabel_cutConverges hcut
  exact balanced_left_subsequence_limit hdyadic hcount hcrit hrn hrt hm hσ
    (fun n => (φ n).toRelabeling) hφ

end SparseLowerTail.Section05

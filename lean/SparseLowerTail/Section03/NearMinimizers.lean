import SparseLowerTail.Section02.Existence
import SparseLowerTail.Section02.CutDistanceIdentities

/-! Near minimizers of the graphon variational problem (manuscript `lem:stability`). -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02

/-- A cut limit of asymptotically feasible, asymptotically optimal graphons is a minimizer. -/
theorem minimizer_of_approximate_cut_limit
    (hdyadic : ClassicalDyadicL1Approximation) (hcount : ClassicalTriangleCounting)
    {r : ℝ} {U : ℕ → Graphon} {W : Graphon} {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hcut : CutConverges U W)
    (ht : ∀ n, triangle (U n) ≤ r^3 + δ n)
    (hc : ∀ n, cost (U n) ≤ value r + δ n) : IsMinimizer r W := by
  have htri : Tendsto (fun n => r^3 + δ n) atTop (𝓝 (r^3)) := by
    simpa using hδ.const_add (r^3)
  have hcost : Tendsto (fun n => value r + δ n) atTop (𝓝 (value r)) := by
    simpa using hδ.const_add (value r)
  have hf : Feasible r W :=
    le_of_tendsto_of_tendsto (hcut.triangle hcount) htri (Eventually.of_forall ht)
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun n => cost (U n)) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => cost_nonneg (U n))
  have hlim := liminf_le_liminf (Eventually.of_forall hc) hlo hcost.isCoboundedUnder_ge
  rw [hcost.liminf_eq] at hlim
  exact isMinimizer_iff.mpr ⟨hf, le_antisymm
    ((cost_lowerSemicontinuous_cut hdyadic hcut).trans hlim) (value_le_cost hf)⟩

/-- Approximate feasibility and optimality force proximity to an actual minimizer,
with a genuine measure-preserving bijection. The external inputs are the same
classical approximation, compactness, and counting results used in Section 2. -/
theorem near_minimizer_stability
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ U : Graphon, triangle U ≤ r^3 + δ → cost U ≤ value r + δ →
      ∃ W : Graphon, IsMinimizer r W ∧ ∃ φ : BijectiveRelabeling,
        cutNorm (fun p => relabel U φ.toRelabeling p - W p) ≤ ε := by
  classical
  by_contra h
  push_neg at h
  have hex : ∀ n : ℕ, ∃ U : Graphon,
      triangle U ≤ r^3 + 1/((n:ℝ)+1) ∧ cost U ≤ value r + 1/((n:ℝ)+1) ∧
      ∀ W : Graphon, IsMinimizer r W → ∀ φ : BijectiveRelabeling,
        ε < cutNorm (fun p => relabel U φ.toRelabeling p - W p) :=
    fun n => h (1/((n:ℝ)+1)) (by positivity)
  choose U ht hc hbad using hex
  obtain ⟨W, σ, φ, hσ, hcut⟩ := hcompact U
  have hδ : Tendsto (fun n => 1/((σ n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop
  have hW : IsMinimizer r W := minimizer_of_approximate_cut_limit hdyadic hcount hδ hcut
    (fun n => by simpa only [triangle_relabel] using ht (σ n))
    (fun n => by simpa only [cost_relabel] using hc (σ n))
  have hdist : Tendsto (fun n => cutDistance (U (σ n)) W) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => cutDistance_nonneg _ _) _ hcut
    intro n
    have htriangle := cutDistance_triangle (U (σ n)) (relabel (U (σ n)) (φ n)) W
    rw [cutDistance_relabel_zero hpull, zero_add] at htriangle
    exact htriangle.trans
      (cutDistance_le_relabel (relabel (U (σ n)) (φ n)) W BijectiveRelabeling.identity)
  obtain ⟨n, hn⟩ := (hdist.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨ψ, hψ⟩ := exists_relabel_cutNorm_lt (U (σ n)) W (half_pos hε)
  have hfail := hbad (σ n) W hW ψ
  linarith

end SparseLowerTail.Section03

import SparseLowerTail.Section03.RecoveryVectors
import SparseLowerTail.Section02.ValueContinuity

/-! Strictly feasible uniform step competitors with entropy arbitrarily near the graphon value. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace SparseLowerTail.Section03
open Section02

theorem VertexPartition.eq_of_color_eq {n : ℕ} {P Q : VertexPartition n} (h : P.color=Q.color) : P=Q := by
  cases P
  cases Q
  cases h
  rfl

theorem dyadicPartition_eq_uniform (k : ℕ) :
    dyadicPartition k=uniformVertexPartition (2^k) (by positivity) := by
  apply VertexPartition.eq_of_color_eq
  funext x
  apply Fin.ext
  simp [dyadicPartition,uniformVertexPartition]

theorem averagedGraphon_eq_matrix {n : ℕ} (P : VertexPartition n) (U : Graphon) :
    averagedGraphon P U=matrixStepGraphon P
      (fun i j => rectangleMean U (P.fiber i) (P.fiber j))
      (fun _ _ => rectangleMean_swap U _ _) (fun _ _ => rectangleMean_mem_Icc U _ _) := rfl

/-- The dyadic triangle densities converge, using only the named classical L1 and counting inputs. -/
theorem triangle_dyadic_tendsto (hdyadic : ClassicalDyadicL1Approximation)
    (hcount : ClassicalTriangleCounting) (U : Graphon) :
    Tendsto (fun k => triangle (averagedGraphon (dyadicPartition k) U)) atTop (𝓝 (triangle U)) := by
  have hc : CutConverges (fun k => averagedGraphon (dyadicPartition k) U) U := by
    have hi : ∀ k, Integrable (fun p => averagedGraphon (dyadicPartition k) U p-U p) squareMeasure :=
      fun _ => (graphon_integrable _).sub (graphon_integrable U)
    exact squeeze_zero (fun k => cutNorm_nonneg (hi k))
      (fun k => cutNorm_le_l1 (hi k)) (dyadic_averaging hdyadic U).2
  exact hc.triangle hcount

/-- The actual uniform block graphons suffice for the strict-slack upper-bound construction. -/
theorem exists_uniform_step_competitor (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) {δ : ℝ} (hδ : 0<δ) :
    ∃ K : ℕ, ∃ hK : 0<K, ∃ Z : Fin K → Fin K → ℝ,
      ∃ hsym : ∀ a b, Z a b=Z b a, ∃ hb : ∀ a b, Z a b∈Icc (0:ℝ) 1,
        triangle (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb)<r^3 ∧
        cost (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb)≤value r+δ := by
  let ε : ℝ := min (δ/2) (1/2)
  have hε : 0<ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε≤1/2 := min_le_right _ _
  have hεδ : ε≤δ/2 := min_le_left _ _
  let s := (1-ε)*r
  have hs : 0<s := mul_pos (by linarith) hr.1
  have hsr : s<r := by dsimp [s]; nlinarith [mul_pos hε hr.1]
  have hs1 : s≤1 := hsr.le.trans hr.2.le
  obtain ⟨U,hU⟩ := exists_minimizer hdyadic hcompact hcount ⟨hs.le,hs1⟩
  have hcost : cost U≤value r+δ := by
    have hv := value_sub_le_scale_loss hs hsr.le hr.2.le
    have he : 1-s/r=ε := by dsimp [s]; field_simp [hr.1.ne']; ring
    rw [he] at hv
    rw [(isMinimizer_iff.mp hU).2]
    linarith
  have ht : triangle U<r^3 := by
    have hc : s^3<r^3 := pow_lt_pow_left₀ hsr hs.le (by decide : (3:ℕ)≠0)
    exact hU.1.trans_lt hc
  obtain ⟨k,hk⟩ := ((triangle_dyadic_tendsto hdyadic hcount U).eventually_lt_const ht).exists
  have hcostk := (cost_averagedGraphon_le (dyadicPartition k) U).trans hcost
  let P := uniformVertexPartition (2^k) (by positivity)
  let Z : Fin (2^k) → Fin (2^k) → ℝ := fun a b => rectangleMean U (P.fiber a) (P.fiber b)
  refine ⟨2^k,by positivity,Z,(fun _ _ => rectangleMean_swap U _ _),
    (fun _ _ => rectangleMean_mem_Icc U _ _),?_,?_⟩
  · simpa only [dyadicPartition_eq_uniform,averagedGraphon_eq_matrix] using hk
  · simpa only [dyadicPartition_eq_uniform,averagedGraphon_eq_matrix] using hcostk

end SparseLowerTail.Section03

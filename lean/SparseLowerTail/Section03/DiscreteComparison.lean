import SparseLowerTail.Section03.DiscreteUpperLimit

/-! Combined convergence of the actual finite entropy minimum, strengthening lem:discrete. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02

/-- The discrete variational values converge along every n_j→∞ and p_j→0. -/
theorem finiteTrianglePhi_tendsto_cube (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hp : ∀ j, p j∈Ioo (0:ℝ) 1)
    (hpzero : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun j => finiteTrianglePhi (n j) (p j) (r^3)/((n j:ℝ)^2*p j/2))
      atTop (𝓝 (value r)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hzero : Tendsto (fun j => 1/(n j:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
    have hlo : Tendsto (fun j => value r-1/(n j:ℝ)) atTop (𝓝 (value r)) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => value r) atTop (𝓝 (value r))).sub hzero
    filter_upwards [hn.eventually (eventually_ge_atTop 3),hlo.eventually_const_lt hb] with j hj hbj
    have hlower := finiteTrianglePhi_lower (n j) hj (hp j) (pow_nonneg hr.1.le 3) rfl
    have hnorm : 0<(n j:ℝ)^2*p j/2 :=
      div_pos (mul_pos (sq_pos_of_pos (by exact_mod_cast (show 0<n j by omega))) (hp j).1) (by norm_num)
    apply hbj.trans_le
    apply (le_div_iff₀ hnorm).mpr
    nlinarith
  · intro a ha
    obtain ⟨K,hK,Z,hsym,hb,ht,hcost⟩ :=
      exists_uniform_step_competitor hdyadic hcompact hcount hr
        (show 0<(a-value r)/2 by linarith)
    have hf := hn.eventually (recoveryWeight_eventually_feasible K hK Z hsym hb ht)
    have hpos := hn.eventually (eventually_gt_atTop 0)
    have hlim : Tendsto (fun j => recoveryCostBound K hK Z (n j)+p j/(2*(1-p j))) atTop
        (𝓝 (cost (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb))) := by
      simpa only [add_zero] using ((recoveryCostBound_tendsto K hK Z hsym hb).comp hn).add
        (sparse_entropy_correction_tendsto hpzero)
    have hsmall := hlim.eventually_lt_const
      (show cost (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb)<a by linarith)
    filter_upwards [hf,hpos,hsmall] with j hj hjpos hja
    exact (finiteTrianglePhi_recovery_bound K hK Z hsym hb (n j) hjpos (hp j)
      (hj (p j) (hp j))).trans_lt hja

/-- Combined comparison in the manuscript's η^(1/3) notation. -/
theorem finiteTrianglePhi_tendsto (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1) (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hp : ∀ j, p j∈Ioo (0:ℝ) 1)
    (hpzero : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun j => finiteTrianglePhi (n j) (p j) η/((n j:ℝ)^2*p j/2)) atTop
      (𝓝 (value (η^(1/3:ℝ)))) := by
  have hr : η^(1/3:ℝ)∈Ioo (0:ℝ) 1 := ⟨Real.rpow_pos_of_pos hη.1 _,
    Real.rpow_lt_one hη.1.le hη.2 (by norm_num)⟩
  have hcube : (η^(1/3:ℝ))^3=η := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hη.1.le (by norm_num : (3:ℕ)≠0)
  simpa only [hcube] using finiteTrianglePhi_tendsto_cube hdyadic hcompact hcount hr n p hn hp hpzero

end SparseLowerTail.Section03

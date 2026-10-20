import SparseLowerTail.Section03.UniformStepCompetitors

/-! The full sequence-wise upper bound in lem:discrete(b). -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02

theorem finiteTrianglePhi_nonneg (n : ℕ) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) :
    0≤finiteTrianglePhi n p η := by
  obtain ⟨q,hq,hcost⟩ := finiteTrianglePhi_attained n hp hη
  rw [← hcost]
  exact Finset.sum_nonneg (fun e he => bernoulliEntropy_nonneg hp (hq.1 e he))

/-- The Bernoulli correction vanishes along every sparse probability sequence. -/
theorem sparse_entropy_correction_tendsto {p : ℕ → ℝ}
    (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun j => p j/(2*(1-p j))) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hd : Tendsto (fun j => 2*(1-p j)) atTop (𝓝 (2:ℝ)) := by
    simpa only [sub_zero,mul_one] using (hc.sub hp).const_mul 2
  simpa only [zero_div] using hp.div hd (by norm_num : (2:ℝ)≠0)

/-- Lemma discrete(b), written first with target η=r^3. No relation between the speeds of n and p is needed. -/
theorem finiteTrianglePhi_limsup_cube (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hp : ∀ j, p j∈Ioo (0:ℝ) 1)
    (hpzero : Tendsto p atTop (𝓝 0)) :
    limsup (fun j => finiteTrianglePhi (n j) (p j) (r^3)/((n j:ℝ)^2*p j/2)) atTop≤value r := by
  have hnonneg : ∀ j, 0≤finiteTrianglePhi (n j) (p j) (r^3)/((n j:ℝ)^2*p j/2) := by
    intro j
    exact div_nonneg (finiteTrianglePhi_nonneg _ (hp j) (pow_nonneg hr.1.le 3))
      (div_nonneg (mul_nonneg (sq_nonneg _) (hp j).1.le) (by norm_num))
  have hcob := isCoboundedUnder_le_of_le atTop hnonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨K,hK,Z,hsym,hb,ht,hcost⟩ :=
    exists_uniform_step_competitor hdyadic hcompact hcount hr (half_pos hε)
  have hf := hn.eventually (recoveryWeight_eventually_feasible K hK Z hsym hb ht)
  have hpos := hn.eventually (eventually_gt_atTop 0)
  have hbound : ∀ᶠ j in atTop,
      finiteTrianglePhi (n j) (p j) (r^3)/((n j:ℝ)^2*p j/2)≤
        recoveryCostBound K hK Z (n j)+p j/(2*(1-p j)) := by
    filter_upwards [hf,hpos] with j hj hjpos
    exact finiteTrianglePhi_recovery_bound K hK Z hsym hb (n j) hjpos (hp j) (hj (p j) (hp j))
  have hlim : Tendsto (fun j => recoveryCostBound K hK Z (n j)+p j/(2*(1-p j))) atTop
      (𝓝 (cost (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb))) := by
    simpa only [add_zero] using ((recoveryCostBound_tendsto K hK Z hsym hb).comp hn).add
      (sparse_entropy_correction_tendsto hpzero)
  have hsmall := hlim.eventually_lt_const (show
      cost (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb)<value r+ε by linarith)
  apply limsup_le_of_le hcob
  filter_upwards [hbound,hsmall] with j hj hj'
  exact hj.trans hj'.le

/-- Lemma discrete(b), with the manuscript's actual target η and its real cube root. -/
theorem finiteTrianglePhi_limsup (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1) (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hp : ∀ j, p j∈Ioo (0:ℝ) 1)
    (hpzero : Tendsto p atTop (𝓝 0)) :
    limsup (fun j => finiteTrianglePhi (n j) (p j) η/((n j:ℝ)^2*p j/2)) atTop≤
      value (η^(1/3:ℝ)) := by
  have hr : η^(1/3:ℝ)∈Ioo (0:ℝ) 1 := ⟨Real.rpow_pos_of_pos hη.1 _,
    Real.rpow_lt_one hη.1.le hη.2 (by norm_num)⟩
  have hcube : (η^(1/3:ℝ))^3=η := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hη.1.le (by norm_num : (3:ℕ)≠0)
  simpa only [hcube] using finiteTrianglePhi_limsup_cube hdyadic hcompact hcount hr n p hn hp hpzero

end SparseLowerTail.Section03

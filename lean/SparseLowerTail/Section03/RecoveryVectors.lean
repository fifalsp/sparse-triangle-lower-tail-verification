import SparseLowerTail.Section03.MatrixRecoveryBounds

/-! Genuine finite-edge recovery vectors for uniform block graphons, for every large n. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SparseLowerTail.Section03
open Section02

def recoveryMatrix (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ) (n : ℕ)
    (i j : Fin n) : ℝ := Z (balancedVertexColor K hK n i) (balancedVertexColor K hK n j)

def recoveryWeight (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ) (n : ℕ) :
    Finset (Fin n) → ℝ := edgeWeightFromMatrix (recoveryMatrix K hK Z n)

def recoveryCostBound (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ) (n : ℕ) : ℝ :=
  (∑ i, ∑ j, entropy (recoveryMatrix K hK Z n i j))/(n:ℝ)^2+1/(n:ℝ)

def recoveryTriangleBound (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ) (n : ℕ) : ℝ :=
  (∑ i, ∑ j, ∑ k, recoveryMatrix K hK Z n i j*recoveryMatrix K hK Z n j k*
    recoveryMatrix K hK Z n i k)/(n:ℝ)^3

theorem recoveryWeight_bounds (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ)
    (hb : ∀ a b, Z a b∈Icc (0:ℝ) 1) (n : ℕ) (e : Finset (Fin n)) :
    recoveryWeight K hK Z n e∈Icc (0:ℝ) 1 :=
  edgeWeightFromMatrix_bounds _ (fun _ _ => hb _ _) e

theorem recoveryCostBound_tendsto (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ)
    (hsym : ∀ a b, Z a b=Z b a) (hb : ∀ a b, Z a b∈Icc (0:ℝ) 1) :
    Tendsto (recoveryCostBound K hK Z) atTop
      (𝓝 (cost (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb))) := by
  rw [uniformStepGraphon_cost]
  have hzero : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [add_zero] using (balanced_pair_average_tendsto K hK (fun a b => entropy (Z a b))).add hzero

theorem recoveryTriangleBound_tendsto (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ)
    (hsym : ∀ a b, Z a b=Z b a) (hb : ∀ a b, Z a b∈Icc (0:ℝ) 1) :
    Tendsto (recoveryTriangleBound K hK Z) atTop
      (𝓝 (triangle (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb))) := by
  rw [uniformStepGraphon_triangle]
  exact balanced_triple_average_tendsto K hK (fun a b d => Z a b*Z b d*Z a d)

/-- The exact finite triangle-sampling normalization tends to one. -/
theorem triangleSamplingRatio_tendsto :
    Tendsto (fun n : ℕ => 6*(n.choose 3:ℝ)/(n:ℝ)^3) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub h1).mul
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub h2)
  norm_num only [sub_zero,mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hc := triangle_counts_relation n (by omega)
  rw [triangleVertexCount_formula] at hc
  unfold triangleEdgeCount at hc
  field_simp [hn0]
  nlinarith

/-- Homogeneity is exact because every triangle has three distinct edges. -/
theorem weightedTriangleCount_const_mul {n : ℕ} (q : Finset (Fin n) → ℝ) (p : ℝ) :
    weightedTriangleCount (fun e => p*q e)=p^3*weightedTriangleCount q := by
  unfold weightedTriangleCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.prod_mul_distrib]
  have hc : (triangleEdgeSet T).card=3 := by
    simp [triangleEdgeSet,Finset.card_powersetCard,Finset.mem_powersetCard_univ.mp hT]
  simp [hc]

/-- Strict triangle slack makes the genuine scaled edge vector feasible eventually, uniformly in p. -/
theorem recoveryWeight_eventually_feasible (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ)
    (hsym : ∀ a b, Z a b=Z b a) (hb : ∀ a b, Z a b∈Icc (0:ℝ) 1) {η : ℝ}
    (ht : triangle (matrixStepGraphon (uniformVertexPartition K hK) Z hsym hb)<η) :
    ∀ᶠ n : ℕ in atTop, ∀ p∈Ioo (0:ℝ) 1,
      FiniteTriangleFeasible n p η (fun e => p*recoveryWeight K hK Z n e) := by
  have hsmall := (recoveryTriangleBound_tendsto K hK Z hsym hb).eventually_lt
    (triangleSamplingRatio_tendsto.const_mul η) (by simpa using ht)
  filter_upwards [hsmall,eventually_gt_atTop 0] with n hn hn0 p hp
  have hq := recoveryWeight_bounds K hK Z hb n
  constructor
  · intro e _
    exact ⟨mul_nonneg hp.1.le (hq e).1,
      (mul_le_mul_of_nonneg_left (hq e).2 hp.1.le).trans (by linarith [hp.2])⟩
  · rw [weightedTriangleCount_const_mul]
    have hbound := edgeStepGraphon_fromMatrix_triangle_le n (recoveryMatrix K hK Z n)
      (fun _ _ => hsym _ _) (fun _ _ => hb _ _)
    have hh : 6*weightedTriangleCount (recoveryWeight K hK Z n)/(n:ℝ)^3≤
        (6*(η*(n.choose 3:ℝ)))/(n:ℝ)^3 := by
      calc
        _ ≤ recoveryTriangleBound K hK Z n := hbound
        _ ≤ η*(6*(n.choose 3:ℝ)/(n:ℝ)^3) := hn.le
        _ = _ := by ring
    have hpos : 0<(n:ℝ)^3 := pow_pos (by exact_mod_cast hn0) 3
    have hN : weightedTriangleCount (recoveryWeight K hK Z n)≤η*(n.choose 3:ℝ) := by
      have hh' := (div_le_div_iff_of_pos_right hpos).mp hh
      linarith
    have hh' := mul_le_mul_of_nonneg_left hN (pow_nonneg hp.1.le 3)
    nlinarith

/-- Candidate entropy bound with the actual finite step graphon and the explicit 1/n loss. -/
theorem finiteTrianglePhi_recovery_bound (K : ℕ) (hK : 0<K) (Z : Fin K → Fin K → ℝ)
    (hsym : ∀ a b, Z a b=Z b a) (hb : ∀ a b, Z a b∈Icc (0:ℝ) 1)
    (n : ℕ) (hn : 0<n) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1)
    (hf : FiniteTriangleFeasible n p η (fun e => p*recoveryWeight K hK Z n e)) :
    finiteTrianglePhi n p η/((n:ℝ)^2*p/2)≤recoveryCostBound K hK Z n+p/(2*(1-p)) := by
  have hq := recoveryWeight_bounds K hK Z hb n
  have hqp : ∀ e∈completeGraphEdges n, p*recoveryWeight K hK Z n e∈Icc (0:ℝ) p := by
    intro e _
    exact ⟨mul_nonneg hp.1.le (hq e).1,by simpa using mul_le_mul_of_nonneg_left (hq e).2 hp.1.le⟩
  have hu := finiteEdgeEntropy_upper n hn hp (fun e => p*recoveryWeight K hK Z n e) hqp
  have hlo := finiteTrianglePhi_le n hp _ hf
  have hcancel : (fun e => p*recoveryWeight K hK Z n e/p)=recoveryWeight K hK Z n := by
    funext e
    field_simp [hp.1.ne']
  let hw : ∀ e∈completeGraphEdges n, p*recoveryWeight K hK Z n e/p∈Icc (0:ℝ) 1 :=
    fun e he => ⟨div_nonneg (hqp e he).1 hp.1.le,(div_le_one hp.1).mpr (hqp e he).2⟩
  have hcost : cost (edgeStepGraphon n hn (fun e => p*recoveryWeight K hK Z n e/p) hw)
      ≤recoveryCostBound K hK Z n := by
    simpa only [hcancel] using edgeStepGraphon_fromMatrix_cost_le n hn (recoveryMatrix K hK Z n)
      (fun _ _ => hsym _ _) (fun _ _ => hb _ _)
  have hnorm : 0<(n:ℝ)^2*p/2 := div_pos (mul_pos (sq_pos_of_pos (by exact_mod_cast hn)) hp.1) (by norm_num)
  apply (div_le_iff₀ hnorm).mpr
  have hh := mul_le_mul_of_nonneg_left (add_le_add_right hcost (p/(2*(1-p)))) hnorm.le
  nlinarith

end SparseLowerTail.Section03

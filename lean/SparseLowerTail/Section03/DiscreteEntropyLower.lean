import SparseLowerTail.Section03.FiniteWeightedGraph

/-! The finite-n lower bound in lem:discrete(a), with the actual edge entropy infimum. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

/-- Gibbs' inequality applied to the actual two-point Bernoulli laws. -/
theorem bernoulliEntropy_nonneg {p q : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hq : q∈Icc (0:ℝ) 1) :
    0≤bernoulliEntropy p q := by
  have hh := finiteRelativeEntropy_nonneg (bernoulliMass q) (bernoulliMass p)
    (bernoulliMass_nonneg hq) (bernoulliMass_nonneg ⟨hp.1.le,hp.2.le⟩)
    (bernoulliMass_sum q) (bernoulliMass_sum p)
    (fun b hb => False.elim ((bernoulliMass_pos hp b).ne' hb))
  simpa only [finiteRelativeEntropy,Fintype.sum_bool,bernoulliMass,bernoulliEntropy] using hh

theorem bernoulliEntropy_self {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) :
    bernoulliEntropy p p=0 := by
  simp [bernoulliEntropy,hp.1.ne',(sub_pos.mpr hp.2).ne']

/-- Clipping an edge mean at p cannot increase its entropy cost. -/
theorem bernoulliEntropy_clip {p q : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hq : q∈Icc (0:ℝ) 1) :
    bernoulliEntropy p (min q p)≤bernoulliEntropy p q := by
  by_cases hqp : q≤p
  · simp [min_eq_left hqp]
  · rw [min_eq_right (le_of_not_ge hqp),bernoulliEntropy_self hp]
    exact bernoulliEntropy_nonneg hp hq

theorem triangleEdgeSet_edge {n : ℕ} {T e : Finset (Fin n)}
    (he : e∈triangleEdgeSet T) : e∈completeGraphEdges n :=
  Finset.mem_powersetCard_univ.mpr (Finset.mem_powersetCard.mp he).2

/-- Triangle counts have nonnegative coefficients and hence are monotone in the edge means. -/
theorem weightedTriangleCount_mono {n : ℕ} (q q' : Finset (Fin n) → ℝ)
    (hq : ∀ e∈completeGraphEdges n, 0≤q e)
    (hle : ∀ e∈completeGraphEdges n, q e≤q' e) :
    weightedTriangleCount q≤weightedTriangleCount q' := by
  apply Finset.sum_le_sum
  intro T _
  exact Finset.prod_le_prod (fun e he => hq e (triangleEdgeSet_edge he))
    (fun e he => hle e (triangleEdgeSet_edge he))

/-- The finite normalization 6 choose(n,3) is at most n cubed. -/
theorem six_choose_three_le_cube (n : ℕ) (hn : 3≤n) :
    6*(n.choose 3:ℝ)≤(n:ℝ)^3 := by
  have hh := triangle_counts_relation n (by omega)
  rw [triangleVertexCount_formula] at hh
  unfold triangleEdgeCount at hh
  have hn' : (3:ℝ)≤n := by exact_mod_cast hn
  have hm : 0≤(n:ℝ)*(3*(n:ℝ)-2) := mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- Feasible vectors are actual edge probabilities with the manuscript's triangle bound. -/
def FiniteTriangleFeasible (n : ℕ) (p η : ℝ) (q : Finset (Fin n) → ℝ) : Prop :=
  (∀ e∈completeGraphEdges n, q e∈Icc (0:ℝ) 1) ∧
    weightedTriangleCount q≤η*(n.choose 3:ℝ)*p^3

def finiteEdgeEntropy (n : ℕ) (p : ℝ) (q : Finset (Fin n) → ℝ) : ℝ :=
  ∑ e∈completeGraphEdges n, bernoulliEntropy p (q e)

/-- The discrete variational value, over the actual finite collection of graph edges. -/
def finiteTrianglePhi (n : ℕ) (p η : ℝ) : ℝ :=
  sInf {v | ∃ q : Finset (Fin n) → ℝ, FiniteTriangleFeasible n p η q ∧ finiteEdgeEntropy n p q=v}

/-- Every feasible vector obeys the sharp finite-n lower bound, after clipping at p. -/
theorem finiteEdgeEntropy_lower (n : ℕ) (hn : 3≤n) {p η r : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) (hr : r^3=η)
    (q : Finset (Fin n) → ℝ) (hq : FiniteTriangleFeasible n p η q) :
    (n:ℝ)^2*p/2*(value r-1/(n:ℝ))≤finiteEdgeEntropy n p q := by
  classical
  let q' : Finset (Fin n) → ℝ := fun e => min (q e) p
  have hq' : ∀ e∈completeGraphEdges n, q' e∈Icc (0:ℝ) p := by
    intro e he
    exact ⟨le_min (hq.1 e he).1 hp.1.le,min_le_right _ _⟩
  have hw : ∀ e∈completeGraphEdges n, q' e/p∈Icc (0:ℝ) 1 := by
    intro e he
    exact ⟨div_nonneg (hq' e he).1 hp.1.le,(div_le_one hp.1).mpr (hq' e he).2⟩
  let W := edgeStepGraphon n (by omega) (fun e => q' e/p) hw
  have ht : weightedTriangleCount q'≤η*(n.choose 3:ℝ)*p^3 :=
    (weightedTriangleCount_mono q' q (fun e he => (hq' e he).1)
      (fun _ _ => min_le_left _ _)).trans hq.2
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hW : Feasible r W := by
    change triangle W≤r^3
    rw [hr]
    dsimp [W]
    rw [edgeStepGraphon_triangle,weightedTriangleCount_div]
    have hc := six_choose_three_le_cube n hn
    have htc := (div_le_iff₀ (pow_pos hp.1 3)).mpr ht
    apply (div_le_iff₀ (pow_pos hn0 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc hη]
  have hv := value_le_cost hW
  have hc : cost W=2/(n:ℝ)^2*(∑ e∈completeGraphEdges n, entropy (q' e/p))+1/(n:ℝ) :=
    edgeStepGraphon_cost n (by omega) _ hw
  have hcost : p*(∑ e∈completeGraphEdges n, entropy (q' e/p))≤finiteEdgeEntropy n p q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have hb := (sparse_entropy_bounds hp (hw e he)).1
    have hcancel : p*(q' e/p)=q' e := by field_simp [hp.1.ne']
    rw [hcancel] at hb
    have hpoint : p*entropy (q' e/p)≤bernoulliEntropy p (q' e) := by
      rw [mul_comm]
      apply (le_div_iff₀ hp.1).mp
      linarith
    exact hpoint.trans (bernoulliEntropy_clip hp (hq.1 e he))
  rw [hc] at hv
  have hv' := mul_le_mul_of_nonneg_left hv (show 0≤(n:ℝ)^2*p/2 from
    div_nonneg (mul_nonneg (sq_nonneg _) hp.1.le) (by norm_num))
  have he : (n:ℝ)^2*p/2*(2/(n:ℝ)^2*(∑ e∈completeGraphEdges n, entropy (q' e/p))+1/(n:ℝ))=
      p*(∑ e∈completeGraphEdges n, entropy (q' e/p))+(n:ℝ)^2*p/2*(1/(n:ℝ)) := by
    field_simp
  rw [he] at hv'
  nlinarith

/-- The zero edge vector is feasible for every nonnegative target. -/
theorem zero_finiteTriangleFeasible (n : ℕ) {p η : ℝ} (hp : 0≤p) (hη : 0≤η) :
    FiniteTriangleFeasible n p η (fun _ => 0) := by
  constructor
  · intro e he; exact ⟨le_rfl,zero_le_one⟩
  · have hz : weightedTriangleCount (fun _ : Finset (Fin n) => (0:ℝ))=0 := by
      apply Finset.sum_eq_zero
      intro T hT
      have hc : (triangleEdgeSet T).card=3 := by
        simp [triangleEdgeSet,Finset.card_powersetCard,Finset.mem_powersetCard_univ.mp hT]
      simp [Finset.prod_const,hc]
    rw [hz]
    positivity

/-- The finite entropy costs are bounded below, so the infimum has its usual meaning. -/
theorem finiteTriangle_costs_bddBelow (n : ℕ) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1) :
    BddBelow {v | ∃ q, FiniteTriangleFeasible n p η q ∧ finiteEdgeEntropy n p q=v} := by
  refine ⟨0,?_⟩
  rintro v ⟨q,hq,rfl⟩
  exact Finset.sum_nonneg (fun e he => bernoulliEntropy_nonneg hp (hq.1 e he))

/-- A feasible vector bounds the discrete infimum from above. -/
theorem finiteTrianglePhi_le (n : ℕ) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1)
    (q : Finset (Fin n) → ℝ) (hq : FiniteTriangleFeasible n p η q) :
    finiteTrianglePhi n p η≤finiteEdgeEntropy n p q :=
  csInf_le (finiteTriangle_costs_bddBelow n hp) ⟨q,hq,rfl⟩

/-- Lemma discrete(a), for any real cube root r of the target η. -/
theorem finiteTrianglePhi_lower (n : ℕ) (hn : 3≤n) {p η r : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) (hr : r^3=η) :
    (n:ℝ)^2*p/2*(value r-1/(n:ℝ))≤finiteTrianglePhi n p η := by
  apply le_csInf
    (show {v | ∃ q, FiniteTriangleFeasible n p η q ∧ finiteEdgeEntropy n p q=v}.Nonempty from
      ⟨_,(fun _ => 0),zero_finiteTriangleFeasible n hp.1.le hη,rfl⟩)
  rintro v ⟨q,hq,rfl⟩
  exact finiteEdgeEntropy_lower n hn hp hη hr q hq

/-- Lemma discrete(a) in the manuscript's η^(1/3) notation. -/
theorem finiteTrianglePhi_lower_cuberoot (n : ℕ) (hn : 3≤n) {p η : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : η∈Ioo (0:ℝ) 1) :
    (n:ℝ)^2*p/2*(value (η ^ (1/3:ℝ))-1/(n:ℝ))≤finiteTrianglePhi n p η := by
  apply finiteTrianglePhi_lower n hn hp hη.1.le
  simpa only [one_div] using Real.rpow_inv_natCast_pow hη.1.le (by norm_num : (3:ℕ)≠0)

end SparseLowerTail.Section03

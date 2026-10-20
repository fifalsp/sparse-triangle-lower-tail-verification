import SparseLowerTail.Section03.RevealedHarris
import SparseLowerTail.Section03.ConditionalCostBounds

/-! Entropy cost of the actual conditional means after deleting the revealed edges. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unrevealedEntropyCost (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool) (p : ℝ) : ℝ :=
  ∑ i : ↑Wᶜ, bernoulliEntropy p (finiteMarginal (unrevealedConditionalLaw q W y) (fun z => z i) true)

/-- The actual unrevealed entropy cost is nonnegative on all patterns. -/
theorem unrevealedEntropyCost_nonneg (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z)
    (W : Finset ι) (y : W → Bool) {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) :
    0≤unrevealedEntropyCost q W y p :=
  Finset.sum_nonneg (fun i _ => bernoulliEntropy_nonneg hp
    (unrevealedConditionalLaw_marginal_mem_unitInterval q hq W y i))

/-- The exact cost identity, with the deleted coordinates charged at their zero-edge entropy. -/
theorem erasedConditionalMeans_entropy (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool) (p : ℝ) :
    (∑ i, bernoulliEntropy p (erasedConditionalMeans q W y i)) =
      (W.card:ℝ)*bernoulliEntropy p 0+unrevealedEntropyCost q W y p := by
  classical
  let f := fun i => bernoulliEntropy p (erasedConditionalMeans q W y i)
  have hsplit := Finset.sum_add_sum_compl W f
  have hW : (∑ i∈W, f i)=(W.card:ℝ)*bernoulliEntropy p 0 := by
    have hh : ∀ i∈W, f i=bernoulliEntropy p 0 := by
      intro i hi
      simp [f,erasedConditionalMeans,hi]
    rw [Finset.sum_congr rfl hh]
    simp
  have hC : (∑ i∈Wᶜ, f i)=unrevealedEntropyCost q W y p := by
    rw [Finset.sum_subtype Wᶜ (fun _ => Iff.rfl) f]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    rw [erasedConditionalMeans,if_neg (Finset.mem_compl.mp i.property),← unrevealedConditionalLaw_marginal_true q W y i]
  rw [hW,hC] at hsplit
  exact hsplit.symm

omit [Fintype ι] [DecidableEq ι] in
/-- Zeroing a revealed edge costs at most 2p when p≤1/2. -/
theorem bernoulliEntropy_zero_le_two_mul {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hpmax : p≤1/2) :
    bernoulliEntropy p 0≤2*p := by
  have hb := (sparse_entropy_bounds hp (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)).2.1
  simp only [mul_zero,entropy_zero,sub_zero,one_pow,mul_one] at hb
  have hd : 0<2*(1-p) := mul_pos (by norm_num) (sub_pos.mpr hp.2)
  have hratio : p/(2*(1-p))≤1 := (div_le_one hd).mpr (by linarith)
  have hh : bernoulliEntropy p 0/p≤2 := by linarith
  have hmul := (div_le_iff₀ hp.1).mp hh
  exact hmul

/-- The actual erased vector's entropy is bounded by unrevealed cost plus 2p per revealed edge. -/
theorem erasedConditionalMeans_entropy_le (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool)
    {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hpmax : p≤1/2) :
    (∑ i, bernoulliEntropy p (erasedConditionalMeans q W y i))≤
      unrevealedEntropyCost q W y p+2*p*W.card := by
  rw [erasedConditionalMeans_entropy]
  have hh := mul_le_mul_of_nonneg_left (bernoulliEntropy_zero_le_two_mul hp hpmax)
    (show (0:ℝ)≤W.card by positivity)
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- On the actual relaxed triangle event, the unrevealed cost has the manuscript's baseline lower bound. -/
theorem triangle_unrevealed_cost_lower (n : ℕ) (hn : 3≤n) {p η τ r α : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hpmax : p≤1/2) (hη : 0≤η) (hτ : 0≤τ) (hr : r^3=τ) (hα : 0≤α)
    (W : Finset (GraphEdgeCoordinate n)) (hW : (W.card:ℝ)≤α*(n.choose 2:ℝ))
    (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ)) (y : W → Bool)
    (hfeas : hypergraphWeightedCount (coordinateTriangleHypergraph n)
      (erasedConditionalMeans (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)≤τ*p^3*(n.choose 3:ℝ)) :
    triangleRateScale n p*(value r-1/(n:ℝ)-2*α)≤
      unrevealedEntropyCost (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y p := by
  let q := hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η
  let qc := erasedConditionalMeans q W y
  have hb : ∀ i, qc i∈Icc (0:ℝ) p := erasedConditionalMeans_bounds_all (coordinateTriangleHypergraph n) 3
    (by norm_num) (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη W hHarris y
  have hf : FiniteTriangleFeasible n p τ (extendGraphEdges qc) := by
    constructor
    · intro e he
      have hh := hb ⟨e,he⟩
      rw [extendGraphEdges_coe qc ⟨e,he⟩]
      exact ⟨hh.1,hh.2.trans hp.2.le⟩
    · rw [← coordinateTriangle_weightedCount n qc]
      dsimp [qc,q] at hfeas ⊢
      nlinarith
  have hlower := finiteEdgeEntropy_lower n hn hp hτ hr (extendGraphEdges qc) hf
  have he : finiteEdgeEntropy n p (extendGraphEdges qc)=(∑ i, bernoulliEntropy p (qc i)) := by
    rw [finiteEdgeEntropy_eq_coordinate_sum]
    simp only [extendGraphEdges_coe]
  rw [he] at hlower
  have hupper := erasedConditionalMeans_entropy_le q W y hp hpmax
  have hW' : (W.card:ℝ)≤α*((n:ℝ)^2/2) :=
    hW.trans (mul_le_mul_of_nonneg_left (graph_edge_count_le_half_square n) hα)
  have hcharge : 2*p*(W.card:ℝ)≤α*(n:ℝ)^2*p := by
    have hh := mul_le_mul_of_nonneg_left hW' (show 0≤2*p from mul_nonneg (by norm_num) hp.1.le)
    nlinarith
  change (n:ℝ)^2*p/2*(value r-1/(n:ℝ)-2*α)≤unrevealedEntropyCost q W y p
  dsimp only [qc] at hlower
  nlinarith

end SparseLowerTail.Section03

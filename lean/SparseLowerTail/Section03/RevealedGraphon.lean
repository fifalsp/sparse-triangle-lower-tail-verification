import SparseLowerTail.Section03.RevealedCutMatrices
import SparseLowerTail.Section03.StepMatrixCut
import SparseLowerTail.Section03.NearMinimizers

/-! The actual graphon of the erased conditional edge means. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

theorem normalizedEdgeWeight_bounds {n : ℕ} {p : ℝ} (hp : 0<p)
    (q : GraphEdgeCoordinate n → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) p)
    (e : Finset (Fin n)) (he : e∈completeGraphEdges n) :
    extendGraphEdges q e/p∈Icc (0:ℝ) 1 := by
  rw [extendGraphEdges_coe q ⟨e,he⟩]
  exact ⟨div_nonneg (hq ⟨e,he⟩).1 hp.le,(div_le_one hp).mpr (hq ⟨e,he⟩).2⟩

def normalizedEdgeStepGraphon (n : ℕ) (hn : 0<n) {p : ℝ} (hp : 0<p)
    (q : GraphEdgeCoordinate n → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) p) : Graphon :=
  edgeStepGraphon n hn (fun e => extendGraphEdges q e/p) (normalizedEdgeWeight_bounds hp q hq)

/-- The normalized finite entropy bounds the actual graphon's cost, with its exact diagonal error. -/
theorem normalizedEdgeStepGraphon_cost_le (n : ℕ) (hn : 0<n) {p : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (q : GraphEdgeCoordinate n → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) p) :
    cost (normalizedEdgeStepGraphon n hn hp.1 q hq)≤
      (∑ i, bernoulliEntropy p (q i))/triangleRateScale n p+1/(n:ℝ) := by
  rw [normalizedEdgeStepGraphon,edgeStepGraphon_cost]
  have hpoint : ∀ e∈completeGraphEdges n,
      entropy (extendGraphEdges q e/p)≤bernoulliEntropy p (extendGraphEdges q e)/p := by
    intro e he
    have hb := (sparse_entropy_bounds hp (normalizedEdgeWeight_bounds hp.1 q hq e he)).1
    have hc : p*(extendGraphEdges q e/p)=extendGraphEdges q e := mul_div_cancel₀ _ hp.1.ne'
    rw [hc] at hb
    linarith
  have hh := Finset.sum_le_sum hpoint
  rw [← Finset.sum_div] at hh
  have he : (∑ e∈completeGraphEdges n, bernoulliEntropy p (extendGraphEdges q e))=
      ∑ i, bernoulliEntropy p (q i) := by
    rw [← finiteEdgeEntropy,finiteEdgeEntropy_eq_coordinate_sum]
    simp only [extendGraphEdges_coe]
  rw [he] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤2/(n:ℝ)^2 by positivity)
  have hfactor : (2/(n:ℝ)^2)*((∑ i, bernoulliEntropy p (q i))/p)=
      (∑ i, bernoulliEntropy p (q i))/triangleRateScale n p := by
    unfold triangleRateScale
    field_simp
  rw [hfactor] at hmul
  exact add_le_add_right hmul _

/-- The actual graphon's triangle density obeys the same relaxed target as the finite vector. -/
theorem normalizedEdgeStepGraphon_triangle_le (n : ℕ) (hn : 3≤n) {p τ : ℝ} (hp : 0<p)
    (hτ : 0≤τ) (q : GraphEdgeCoordinate n → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) p)
    (hcount : hypergraphWeightedCount (coordinateTriangleHypergraph n) q≤τ*p^3*(n.choose 3:ℝ)) :
    triangle (normalizedEdgeStepGraphon n (by omega) hp q hq)≤τ := by
  rw [normalizedEdgeStepGraphon,edgeStepGraphon_triangle,weightedTriangleCount_div,
    ← coordinateTriangle_weightedCount n q]
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  apply (div_le_iff₀ (pow_pos hnpos 3)).mpr
  have hfinite : hypergraphWeightedCount (coordinateTriangleHypergraph n) q/p^3≤τ*(n.choose 3:ℝ) :=
    (div_le_iff₀ (pow_pos hp 3)).mpr (by nlinarith [hcount])
  have hchoose := mul_le_mul_of_nonneg_left (six_choose_three_le_cube n hn) hτ
  nlinarith

/-- The graphon U^y built from the actual conditioned edge means, with revealed edges erased. -/
def triangleConditionalGraphon (n : ℕ) (hn : 0<n) {p η : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η)
    (W : Finset (GraphEdgeCoordinate n)) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ)) (y : W → Bool) : Graphon :=
  normalizedEdgeStepGraphon n hn hp.1 (erasedConditionalMeans (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)
    (erasedConditionalMeans_bounds_all (coordinateTriangleHypergraph n) 3 (by norm_num)
      (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη W hHarris y)

/-- The actual conditional graphon has the cost bound used on G₁∩G₂. -/
theorem triangleConditionalGraphon_cost_le (n : ℕ) (hn : 0<n) {p η α : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hpmax : p≤1/2) (hη : 0≤η) (hα : 0≤α)
    (W : Finset (GraphEdgeCoordinate n)) (hW : (W.card:ℝ)≤α*(n.choose 2:ℝ))
    (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ)) (y : W → Bool) :
    cost (triangleConditionalGraphon n hn hp hη W hHarris y)≤
      unrevealedEntropyCost (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y p/triangleRateScale n p+
        2*α+1/(n:ℝ) := by
  let q := hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η
  have hc := normalizedEdgeStepGraphon_cost_le n hn hp (erasedConditionalMeans q W y)
    (erasedConditionalMeans_bounds_all _ 3 (by norm_num) (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη W hHarris y)
  have he := erasedConditionalMeans_entropy_le q W y hp hpmax
  have hscale : 0<triangleRateScale n p := div_pos (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hn)) hp.1) (by norm_num)
  have hW' := hW.trans (mul_le_mul_of_nonneg_left (graph_edge_count_le_half_square n) hα)
  have hcharge : 2*p*(W.card:ℝ)≤triangleRateScale n p*(2*α) := by
    unfold triangleRateScale
    have hh := mul_le_mul_of_nonneg_left hW' hp.1.le
    nlinarith
  have hupper := div_le_div_of_nonneg_right he hscale.le
  have hcharge' : 2*p*(W.card:ℝ)/triangleRateScale n p≤2*α :=
    (div_le_iff₀ hscale).mpr (by simpa only [mul_comm] using hcharge)
  change cost (normalizedEdgeStepGraphon n hn hp.1 _ _)≤_
  rw [add_div] at hupper
  linarith

/-- On the four actual good events the normalized graph is close to an actual minimizer
under a genuine measure-preserving bijection. All finite tolerances are explicit. -/
theorem triangle_good_events_stability (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hpull : ClassicalPullbackApproximation)
    (hcount : ClassicalTriangleCounting) (r : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ δ>0, ∀ (n : ℕ) (hn : 3≤n), ∀ p η α γ ζ : ℝ, p∈Ioo (0:ℝ) 1 → p≤1/2 →
      0≤η → r^3=η → 0≤α → α≤ε/16 → 0≤ζ → ζ≤δ → γ+2*α+1/(n:ℝ)≤δ →
      ∀ (W : Finset (GraphEdgeCoordinate n)), ClassicalHarrisPositiveAssociation (↑Wᶜ) →
      (W.card:ℝ)≤α*(n.choose 2:ℝ) → ∀ (y : W → Bool) (z : GraphEdgeCoordinate n → Bool),
      hypergraphWeightedCount (coordinateTriangleHypergraph n)
        (erasedConditionalMeans (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)≤(η+ζ)*p^3*(n.choose 3:ℝ) →
      unrevealedEntropyCost (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y p/triangleRateScale n p≤value r+γ →
      revealedEdgeCount W z≤2*α*p*(n:ℝ)^2 →
      finiteMatrixCutNorm (fun u v => graphEdgeMatrix (extendGraphEdges (erasedBooleanCoordinates W z)) u v-
        graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)) u v)≤(ε/4)*p →
      ∃ U₀ : Graphon, IsMinimizer r U₀ ∧ ∃ φ : BijectiveRelabeling,
        cutNorm (fun x => matrixStepKernel (uniformVertexPartition n (by omega))
          (fun u v => graphEdgeMatrix (extendGraphEdges (fun i => ((z i).toNat:ℝ))) u v/p)
          (φ.equiv x.1,φ.equiv x.2)-U₀ x)<ε := by
  obtain ⟨δ,hδ,hstable⟩ := near_minimizer_stability hdyadic hcompact hpull hcount r (show 0<ε/4 by positivity)
  refine ⟨δ,hδ,?_⟩
  intro n hn p η α γ ζ hp hpmax hη hr hα hαsmall hζ hζsmall hcost W hHarris hW y z hG₁ hG₂ hNW hcut
  have hnpos : 0<n := by omega
  let q := hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η
  let U := triangleConditionalGraphon n hnpos hp hη W hHarris y
  have ht : triangle U≤r^3+δ := by
    have hh := normalizedEdgeStepGraphon_triangle_le n hn hp.1 (add_nonneg hη hζ)
      (erasedConditionalMeans q W y)
      (erasedConditionalMeans_bounds_all _ 3 (by norm_num) (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη W hHarris y) hG₁
    change triangle U≤η+ζ at hh
    rw [hr]
    linarith
  have hc : cost U≤value r+δ := by
    have hh := triangleConditionalGraphon_cost_le n hnpos hp hpmax hη hα W hW hHarris y
    change cost U≤_ at hh
    linarith
  obtain ⟨U₀,hU₀,φ,hφ⟩ := hstable U ht hc
  let A := graphEdgeMatrix (extendGraphEdges (fun i => ((z i).toNat:ℝ)))
  let B := graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans q W y))
  have hmat : finiteMatrixCutNorm (fun u v => A u v/p-B u v/p)≤ε/2 := by
    have he : (fun u v => A u v/p-B u v/p)=(fun u v => (A u v-B u v)/p) := by funext u v; ring
    rw [he]
    exact normalized_graph_matrix_close n hnpos q W y z hp.1 hαsmall hNW hcut
  have hU : ∀ x, U x=matrixStepKernel (uniformVertexPartition n hnpos) (fun u v => B u v/p) x := by
    intro x
    change matrixStepKernel _ (graphEdgeMatrix (fun e => extendGraphEdges (erasedConditionalMeans q W y) e/p)) x=_
    rw [graphEdgeMatrix_div]
  have hh := stepKernel_close_of_matrix_and_graphon n hnpos (fun u v => A u v/p) (fun u v => B u v/p)
    U U₀ hU φ hmat hφ
  refine ⟨U₀,hU₀,φ,?_⟩
  exact hh.trans_lt (by linarith)

end SparseLowerTail.Section03

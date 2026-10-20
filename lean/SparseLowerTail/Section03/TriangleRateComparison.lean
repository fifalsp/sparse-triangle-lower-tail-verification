import SparseLowerTail.Section03.KS23RateInputs

/-! Apply the generic KS23 bounds to the actual triangle hypergraph. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SparseLowerTail.Section03

def triangleLowerTailRate (n : ℕ) (p η : ℝ) : ℝ :=
  hypergraphLowerTailRate (coordinateTriangleHypergraph n) 3 p η

def triangleRateScale (n : ℕ) (p : ℝ) : ℝ := (n:ℝ)^2*p/2

theorem triangle_count_eq_unordered_count (n : ℕ) (z : GraphEdgeCoordinate n → Bool) :
    hypergraphRealCount (coordinateTriangleHypergraph n) z=
      weightedTriangleCount (extendGraphEdges (fun e => ((z e).toNat:ℝ))) :=
  coordinateTriangle_weightedCount n (fun e => ((z e).toNat:ℝ))

theorem triangle_count_expectation (n : ℕ) (p : ℝ) :
    (∑ z, productBernoulliMass (fun _ : GraphEdgeCoordinate n => p) z*
      hypergraphRealCount (coordinateTriangleHypergraph n) z)=p^3*(n.choose 3:ℝ) := by
  simpa only [coordinateTriangleHypergraph_card] using
    hypergraphRealCount_expectation (coordinateTriangleHypergraph n) 3
      (fun _ hA => coordinateTriangleHypergraph_uniform hA) p

theorem triangleLowerTailRate_nonneg (n : ℕ) {p : ℝ} (hp : p∈Icc (0:ℝ) 1) (η : ℝ) :
    0≤triangleLowerTailRate n p η := hypergraphLowerTailRate_nonneg _ _ hp η

theorem coordinateTriangleHypergraph_nonempty (n : ℕ) (hn : 3≤n) :
    (coordinateTriangleHypergraph n).Nonempty := by
  apply Finset.card_pos.mp
  rw [coordinateTriangleHypergraph_card]
  exact Nat.choose_pos hn

/-- Every paper-specific count, codegree and variational identification is discharged. -/
theorem triangle_KS_comparison (hlower : KS23HypergraphLowerBound)
    (hupper : KS23HypergraphUpperBound) {ε : ℝ} (hε : ε∈Ioo (0:ℝ) 1) :
    ∃ L : ℝ, 0<L ∧ ∃ C₁ : ℝ, 0≤C₁ ∧ ∃ C₂ : ℝ, 0≤C₂ ∧
    ∀ n : ℕ, 4≤n → ∀ p η : ℝ, p∈Ioo (0:ℝ) 1 → p≤1/2 →
      L/Real.sqrt n≤p → 0≤η →
      (1-ε)*finiteTrianglePhi n p (η+ε)-C₁≤triangleLowerTailRate n p η ∧
      triangleLowerTailRate n p η≤(1+ε)*finiteTrianglePhi n p ((1-ε)*η)+C₂ := by
  obtain ⟨ell,hell,C₁,hC₁,hlo⟩ := hlower 3 (by decide) (1/2) ε 3
    (by norm_num) hε.1 (by norm_num)
  obtain ⟨C₂,hC₂,hhi⟩ := hupper (1/2) ε (by norm_num) hε
  refine ⟨2/ell,div_pos (by norm_num) hell,C₁,hC₁,C₂,hC₂,?_⟩
  intro n hn p η hp hp0 hpL hη
  have hH : ∀ A∈coordinateTriangleHypergraph n, A.card=3 :=
    fun _ hA => coordinateTriangleHypergraph_uniform hA
  have hlo' := hlo (GraphEdgeCoordinate n) (coordinateTriangleHypergraph n)
    (coordinateTriangleHypergraph_nonempty n (by omega)) hH p η hp hp0 hη
    (coordinateTriangleHypergraph_codegree_condition n hn hell hpL)
  have hhi' := hhi (GraphEdgeCoordinate n) (coordinateTriangleHypergraph n) 3 (by decide) hH p η hp hp0 hη
  simpa only [coordinateTrianglePhi_eq,triangleLowerTailRate] using And.intro hlo' hhi'

/-- The asymptotic sparse regime eventually satisfies every fixed KS threshold. -/
theorem eventually_sparse_threshold (n : ℕ → ℕ) (p : ℕ → ℝ) {L : ℝ}
    (hn : Tendsto n atTop atTop)
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    ∀ᶠ j in atTop, 4≤n j ∧ L/Real.sqrt (n j:ℝ)≤p j := by
  filter_upwards [hn.eventually (eventually_ge_atTop 4),hsparse.eventually_ge_atTop L] with j hj hjL
  refine ⟨hj,(div_le_iff₀ ?_).mpr ?_⟩
  · exact Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n j by omega))
  · nlinarith

/-- The normalization n^2 p / 2 tends to infinity, so additive KS errors disappear. -/
theorem triangleRateScale_tendsto_atTop (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hp : ∀ j, 0≤p j)
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleRateScale (n j) (p j)) atTop atTop := by
  have hh : Tendsto (fun j => (Real.sqrt (n j:ℝ)*p j)/2) atTop atTop :=
    hsparse.atTop_div_const (by norm_num)
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hj
  have hj' : (1:ℝ)≤n j := by exact_mod_cast hj
  have hroot : Real.sqrt (n j:ℝ)≤(n j:ℝ)^2 := by
    have hsq := Real.sq_sqrt (show (0:ℝ)≤n j by positivity)
    have hnonneg := Real.sqrt_nonneg (n j:ℝ)
    have hn2 : (n j:ℝ)≤(n j:ℝ)^2 := by nlinarith
    have hrn : Real.sqrt (n j:ℝ)≤(n j:ℝ) := by nlinarith
    exact hrn.trans hn2
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hroot (hp j)) (by norm_num)

end SparseLowerTail.Section03

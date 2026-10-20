import SparseLowerTail.Section03.RevealedGraphon

/-! The four-good-event deduction in the original triangle edge probability space. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

def patternLift {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Finset ι)
    (E : Finset (W → Bool)) : Finset (ι → Bool) :=
  Finset.univ.filter (fun z => (splitCoordinates W z).1∈E)

theorem patternLift_mass {ι : Type*} [Fintype ι] [DecidableEq ι] (q : (ι → Bool) → ℝ)
    (W : Finset ι) (E : Finset (W → Bool)) :
    finiteEventMass q (patternLift W E)=finiteEventMass (revealedPatternMass q W) E := by
  classical
  have hh := finiteMarginal_expect q (fun z => fun i : W => z i) (fun y => if y∈E then (1:ℝ) else 0)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_mem,Finset.univ_inter] at hh
  unfold finiteEventMass patternLift
  rw [Finset.sum_filter]
  simp_rw [revealedPatternMass_eq_marginal]
  exact hh.symm

def relaxedTriangleBadPatterns (n : ℕ) (p η ζ : ℝ) (W : Finset (GraphEdgeCoordinate n)) : Finset (W → Bool) :=
  Finset.univ.filter (fun y => (η+ζ)*p^3*(n.choose 3:ℝ)<hypergraphWeightedCount
    (coordinateTriangleHypergraph n) (erasedConditionalMeans (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y))

def excessCostBadPatterns (n : ℕ) (p η v₀ γ : ℝ) (W : Finset (GraphEdgeCoordinate n)) : Finset (W → Bool) :=
  Finset.univ.filter (fun y => v₀+γ<unrevealedEntropyCost (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y p/triangleRateScale n p)

def triangleScaledKernel (n : ℕ) (hn : 0<n) (p : ℝ) (z : GraphEdgeCoordinate n → Bool) : ℝ×ℝ → ℝ :=
  matrixStepKernel (uniformVertexPartition n hn)
    (fun u v => graphEdgeMatrix (extendGraphEdges (fun i => ((z i).toNat:ℝ))) u v/p)

def TriangleClose (n : ℕ) (hn : 0<n) (p r ε : ℝ) (z : GraphEdgeCoordinate n → Bool) : Prop :=
  ∃ U : Graphon, IsMinimizer r U ∧ ∃ φ : BijectiveRelabeling,
    cutNorm (fun x => triangleScaledKernel n hn p z (φ.equiv x.1,φ.equiv x.2)-U x)<ε

def triangleFarEvent (n : ℕ) (hn : 0<n) (p r ε : ℝ) : Finset (GraphEdgeCoordinate n → Bool) := by
  classical
  exact Finset.univ.filter (fun z => ¬TriangleClose n hn p r ε z)

/-- The original conditioned probability of being far from every minimizer is bounded
by the four actual bad-event probabilities. Their estimates are proved separately. -/
theorem triangle_far_probability_le (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hpull : ClassicalPullbackApproximation)
    (hcount : ClassicalTriangleCounting) (r : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ δ>0, ∀ (n : ℕ) (hn : 3≤n) (p η α γ ζ v₀ b₁ b₂ b₃ b₄ : ℝ),
      p∈Ioo (0:ℝ) 1 → p≤1/2 → 0≤η → r^3=η → 0≤α → α≤ε/16 → 0≤ζ → ζ≤δ →
      γ+2*α+1/(n:ℝ)≤δ → v₀≤value r →
      ∀ W : Finset (GraphEdgeCoordinate n), ClassicalHarrisPositiveAssociation (↑Wᶜ) →
      (W.card:ℝ)≤α*(n.choose 2:ℝ) →
      finiteEventMass (revealedPatternMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W)
        (relaxedTriangleBadPatterns n p η ζ W)≤b₁ →
      finiteEventMass (revealedPatternMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W)
        (excessCostBadPatterns n p η v₀ γ W)≤b₂ →
      finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η)
        (revealedFamilyEvent W (fun y => unrevealedCutEvent (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y ε p))≤b₃ →
      finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η)
        (Finset.univ.filter (fun z => 2*α*p*(n:ℝ)^2<revealedEdgeCount W z))≤b₄ →
      finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η)
        (triangleFarEvent n (by omega) p r ε)≤b₁+b₂+b₃+b₄ := by
  classical
  obtain ⟨δ,hδ,hstable⟩ := triangle_good_events_stability hdyadic hcompact hpull hcount r hε
  refine ⟨δ,hδ,?_⟩
  intro n hn p η α γ ζ v₀ b₁ b₂ b₃ b₄ hp hpmax hη hr hα hαsmall hζ hζsmall hcost hv₀ W hHarris hW h₁ h₂ h₃ h₄
  let q := hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η
  let A := patternLift W (relaxedTriangleBadPatterns n p η ζ W)
  let B := patternLift W (excessCostBadPatterns n p η v₀ γ W)
  let C := revealedFamilyEvent W (fun y => unrevealedCutEvent q W y ε p)
  let D := Finset.univ.filter (fun z => 2*α*p*(n:ℝ)^2<revealedEdgeCount W z)
  have hsub : triangleFarEvent n (by omega) p r ε⊆A∪B∪C∪D := by
    intro z hz
    by_contra hnot
    have hnone : ((z∉A ∧ z∉B) ∧ z∉C) ∧ z∉D := by simpa only [Finset.mem_union,not_or] using hnot
    obtain ⟨⟨⟨ha,hb⟩,hc⟩,hd⟩ := hnone
    have hG₁ : hypergraphWeightedCount (coordinateTriangleHypergraph n)
        (erasedConditionalMeans q W (splitCoordinates W z).1)≤(η+ζ)*p^3*(n.choose 3:ℝ) := by
      simpa only [A,patternLift,relaxedTriangleBadPatterns,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using ha
    have hG₂ : unrevealedEntropyCost q W (splitCoordinates W z).1 p/triangleRateScale n p≤value r+γ := by
      have hh : unrevealedEntropyCost q W (splitCoordinates W z).1 p/triangleRateScale n p≤v₀+γ := by
        simpa only [B,patternLift,excessCostBadPatterns,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hb
      linarith
    have hcut : finiteMatrixCutNorm (fun u v => graphEdgeMatrix (extendGraphEdges (erasedBooleanCoordinates W z)) u v-
        graphEdgeMatrix (extendGraphEdges (erasedConditionalMeans q W (splitCoordinates W z).1)) u v)≤(ε/4)*p := by
      dsimp only [C] at hc
      rw [revealedFamilyEvent_cut_eq] at hc
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hc
    have hNW : revealedEdgeCount W z≤2*α*p*(n:ℝ)^2 := by
      simpa only [D,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hd
    have hclose := hstable n hn p η α γ ζ hp hpmax hη hr hα hαsmall hζ hζsmall hcost W hHarris hW
      (splitCoordinates W z).1 z hG₁ hG₂ hNW hcut
    exact (Finset.mem_filter.mp hz).2 hclose
  have hq : ∀ z, 0≤q z := hypergraphLowerLaw_nonneg _ 3 ⟨hp.1.le,hp.2.le⟩ η
  have hmass : finiteEventMass q (triangleFarEvent n (by omega) p r ε)≤finiteEventMass q (A∪B∪C∪D) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hq z)
  have hA : finiteEventMass q A≤b₁ := by rw [patternLift_mass]; exact h₁
  have hB : finiteEventMass q B≤b₂ := by rw [patternLift_mass]; exact h₂
  exact (hmass.trans (finite_four_bad_events_le q hq A B C D)).trans
    (add_le_add (add_le_add (add_le_add hA hB) h₃) h₄)

/-- Combined finite probability bound, discharging all four bad-event probabilities
with the actual triangle-law estimates. Only the displayed finite parameter conditions remain. -/
theorem triangle_far_probability_estimate (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hpull : ClassicalPullbackApproximation)
    (hcount : ClassicalTriangleCounting) (r : ℝ) {ε : ℝ} (hε : ε∈Ioo (0:ℝ) 1) :
    ∃ δ>0, ∀ (n : ℕ) (hn : 3≤n) (p η α γ ζ s β ω : ℝ),
      p∈Ioo (0:ℝ) 1 → p≤1/2 → 0≤η → r^3=η → 0≤α → α≤ε/16 → 0<γ → 0<ζ → ζ≤δ →
      γ+2*α+1/(n:ℝ)≤δ → s^3=η+ζ → value s-1/(n:ℝ)-2*α≤1 →
      0≤value r-(value s-1/(n:ℝ)-2*α) → value r-(value s-1/(n:ℝ)-2*α)≤ω/2 →
      ζ≤ω/8 → β/ζ≤ω/8 → triangleLowerTailRate n p η/triangleRateScale n p≤value r+ζ →
      2*4^n*Real.exp (-ε^2*p*(n:ℝ)^2/128)≤Real.exp (-ε^2*p*(n:ℝ)^2/256) →
      Real.log 2≤ω*(p*(n:ℝ)^2) →
      ClassicalHarrisPositiveAssociation (GraphEdgeCoordinate n) →
      ∀ W : Finset (GraphEdgeCoordinate n), ClassicalHarrisPositiveAssociation (↑Wᶜ) →
      (W.card:ℝ)≤α*(n.choose 2:ℝ) →
      hypergraphConditionalError (coordinateTriangleHypergraph n)
        (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W≤β*p^3*(n.choose 3:ℝ) →
      finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η)
        (triangleFarEvent n (by omega) p r ε)≤β/ζ+ω/γ+384*ω/ε^2+Real.exp (-α*p*(n:ℝ)^2) := by
  obtain ⟨δ,hδ,hfar⟩ := triangle_far_probability_le hdyadic hcompact hpull hcount r hε.1
  refine ⟨δ,hδ,?_⟩
  intro n hn p η α γ ζ s β ω hp hpmax hη hr hα hαsmall hγ hζ hζsmall hcost hs hbase hgap0 hgap hζω hβω hrate hlarge hlog hHarris W hHarrisW hW hdecor
  obtain ⟨hcostprob,hdepend⟩ := triangle_revealed_cost_and_dependence n hn hp hpmax hη hζ hs hα hγ W hW hHarrisW
    hdecor hrate hbase hgap hζω hβω
  have hnpos : 0<n := by omega
  have hscale : 0<triangleRateScale n p := div_pos (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hnpos)) hp.1) (by norm_num)
  have hD : (∑ y : W → Bool, revealedPatternMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y*
      finiteRelativeEntropy (unrevealedConditionalLaw (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)
      (productMarginals (unrevealedConditionalLaw (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)))≤ω*(p*(n:ℝ)^2)/2 := by
    rw [← Finset.sum_div] at hdepend
    have hh := (div_le_iff₀ hscale).mp hdepend
    convert hh using 1; unfold triangleRateScale; ring
  have hcutprob := triangle_conditioned_cut_error_probability n hnpos hp hη hε W hHarrisW hlarge hD hlog
  have hWtail : (W.card:ℝ)≤α*(n:ℝ)^2/2 := by
    have hh := hW.trans (mul_le_mul_of_nonneg_left (graph_edge_count_le_half_square n) hα)
    nlinarith
  have htail := revealedEdgeCount_conditioned_tail (coordinateTriangleHypergraph n) 3 (by norm_num)
    (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη hHarris W hWtail
  exact hfar n hn p η α γ ζ (value s-1/(n:ℝ)-2*α) (β/ζ) (ω/γ) (384*ω/ε^2)
    (Real.exp (-α*p*(n:ℝ)^2)) hp hpmax hη hr hα hαsmall hζ.le hζsmall hcost (by linarith)
    W hHarrisW hW (triangle_relaxed_constraint_probability n hn hp hζ W hdecor) hcostprob hcutprob htail

end SparseLowerTail.Section03

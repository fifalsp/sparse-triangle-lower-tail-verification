import SparseLowerTail.Section03.RevealedCost

/-! The cost and dependence-entropy estimates for the actual triangle revealed-pattern law. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- The actual cost exceeds its baseline only with small probability, and the remaining
conditional dependence entropy is small in mean. These are the G₂ and entropy estimates
in the conditioned-structure proof. -/
theorem triangle_revealed_cost_and_dependence (n : ℕ) (hn : 3≤n) {p η ζ s r α β γ ω : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hpmax : p≤1/2) (hη : 0≤η) (hζ : 0<ζ) (hs : s^3=η+ζ)
    (hα : 0≤α) (hγ : 0<γ) (W : Finset (GraphEdgeCoordinate n))
    (hW : (W.card:ℝ)≤α*(n.choose 2:ℝ)) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ))
    (hdecor : hypergraphConditionalError (coordinateTriangleHypergraph n)
      (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W≤β*p^3*(n.choose 3:ℝ))
    (hrate : triangleLowerTailRate n p η/triangleRateScale n p≤value r+ζ)
    (hbase : value s-1/(n:ℝ)-2*α≤1)
    (hgap : value r-(value s-1/(n:ℝ)-2*α)≤ω/2)
    (hζsmall : ζ≤ω/8) (hbad : β/ζ≤ω/8) :
    let q := hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η
    let μ := revealedPatternMass q W
    let v₀ := value s-1/(n:ℝ)-2*α
    finiteEventMass μ (Finset.univ.filter (fun y => v₀+γ<unrevealedEntropyCost q W y p/triangleRateScale n p))≤ω/γ ∧
    (∑ y : W → Bool, μ y*finiteRelativeEntropy (unrevealedConditionalLaw q W y)
      (productMarginals (unrevealedConditionalLaw q W y))/triangleRateScale n p)≤ω := by
  let q := hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η
  let μ := revealedPatternMass q W
  let v₀ := value s-1/(n:ℝ)-2*α
  let X := fun y : W → Bool => unrevealedEntropyCost q W y p/triangleRateScale n p
  let D := fun y : W → Bool => finiteRelativeEntropy (unrevealedConditionalLaw q W y)
    (productMarginals (unrevealedConditionalLaw q W y))/triangleRateScale n p
  let G := Finset.univ.filter (fun y : W → Bool => hypergraphWeightedCount (coordinateTriangleHypergraph n)
    (erasedConditionalMeans q W y)≤(η+ζ)*p^3*(n.choose 3:ℝ))
  have hnpos : 0<n := lt_of_lt_of_le (by norm_num : 0<3) hn
  have hscale : 0<triangleRateScale n p := div_pos (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hnpos)) hp.1) (by norm_num)
  have hq : ∀ z, 0≤q z := hypergraphLowerLaw_nonneg _ 3 ⟨hp.1.le,hp.2.le⟩ η
  have hμ : ∀ y, 0≤μ y := fun y => Finset.sum_nonneg (fun z _ => hq z)
  have hμsum : ∑ y, μ y=1 := by
    rw [revealedPatternMass_sum]
    exact hypergraphLowerLaw_sum _ 3 (by norm_num) (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη
  have hX : ∀ y, 0≤X y := fun y => div_nonneg (unrevealedEntropyCost_nonneg q hq W y hp) hscale.le
  have hD : ∀ y, 0≤D y := fun y => div_nonneg (unrevealedConditionalLaw_dependence_nonneg q hq W y) hscale.le
  have hG : ∀ y∈G, v₀≤X y := by
    intro y hy
    have hbound := triangle_unrevealed_cost_lower n hn hp hpmax hη (by linarith : 0≤η+ζ) hs hα
      W hW hHarris y (Finset.mem_filter.mp hy).2
    exact (le_div_iff₀ hscale).mpr (by simpa only [v₀,q,mul_comm] using hbound)
  have hbudget : (∑ y, μ y*D y)+(∑ y, μ y*X y)≤value r+ζ := by
    have hb := hypergraph_revealed_entropy_budget (coordinateTriangleHypergraph n) 3 (by norm_num)
      (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη W
    have hh := div_le_div_of_nonneg_right hb hscale.le
    have hh' : (∑ y, μ y*D y)+(∑ y, μ y*X y)≤triangleLowerTailRate n p η/triangleRateScale n p := by
      simpa only [D,X,unrevealedEntropyCost,← mul_div_assoc,← Finset.sum_div,← add_div] using hh
    exact hh'.trans hrate
  have hGbad : finiteEventMass μ Gᶜ≤ω/8 := by
    have hfail := triangle_relaxed_constraint_probability n hn hp hζ W hdecor
    have hevent : Gᶜ=Finset.univ.filter (fun y => (η+ζ)*p^3*(n.choose 3:ℝ)<
        hypergraphWeightedCount (coordinateTriangleHypergraph n) (erasedConditionalMeans q W y)) := by
      ext y
      simp [G,not_le]
    rw [hevent]
    exact hfail.trans hbad
  obtain ⟨hexcess,hdepend⟩ := conditional_excess_and_dependence_means μ X D hμ hμsum hX hD G hbase hG
    hbudget hgap hζsmall hGbad
  constructor
  · exact conditional_excess_cost_probability μ X hμ hγ hexcess
  · simpa only [D,mul_div_assoc] using hdepend

end SparseLowerTail.Section03

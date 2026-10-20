import SparseLowerTail.Section03.GraphEdgeEndpoints
import SparseLowerTail.Section03.RevealedEntropyTransfer

/-! Matrix cut concentration and entropy transfer for the actual unrevealed triangle edge law. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

def unrevealedConditionalMeans {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool) (i : ↑Wᶜ) : ℝ :=
  finiteMarginal (unrevealedConditionalLaw q W y) (fun z => z i) true

/-- The actual cut-error event after the revealed entries have been set to zero. -/
def unrevealedCutEvent {n : ℕ} (q : (GraphEdgeCoordinate n → Bool) → ℝ)
    (W : Finset (GraphEdgeCoordinate n)) (y : W → Bool) (ε p : ℝ) : Finset (↑Wᶜ → Bool) :=
  Finset.univ.filter (fun z => (ε/4)*p<finiteMatrixCutNorm
    (symmetricEdgeMatrix (unrevealedEdgeEndpoints W) (fun i => (z i).toNat-unrevealedConditionalMeans q W y i)))

/-- The proved matrix concentration theorem applies to the actual product marginals at every positive-mass pattern. -/
theorem triangle_unrevealed_product_cut_bound (n : ℕ) (hn : 0<n) {p η ε : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) (hε : ε∈Ioo (0:ℝ) 1)
    (W : Finset (GraphEdgeCoordinate n)) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ))
    (y : W → Bool) (hy : 0<revealedPatternMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y) :
    finiteEventMass (productMarginals (unrevealedConditionalLaw
      (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y))
      (unrevealedCutEvent (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y ε p)≤
      2*4^n*Real.exp (-ε^2*p*(n:ℝ)^2/128) := by
  let q := hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η
  have hmean : ∀ i : ↑Wᶜ, unrevealedConditionalMeans q W y i∈Icc (0:ℝ) p :=
    hypergraph_unrevealed_marginal_bounds_all (coordinateTriangleHypergraph n) 3 (by norm_num)
      (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη W hHarris y
  rw [productMarginals_eq_productBernoulliMass _ (unrevealedConditionalLaw_sum q W y hy)]
  have hh := bernoulli_matrix_cut_concentration hn (unrevealedEdgeEndpoints W)
    (unrevealedEdgeEndpoints_injective W) (unrevealedEdgeEndpoints_ordered W)
    (unrevealedConditionalMeans q W y) (fun i => ⟨(hmean i).1,(hmean i).2.trans hp.2.le⟩)
    (show ε/4∈Icc (0:ℝ) 1 from ⟨by linarith [hε.1],by linarith [hε.2]⟩)
    hp.1.le (fun i => (hmean i).2)
  have hexp : -(ε/4)^2*p*(n:ℝ)^2/8 = -ε^2*p*(n:ℝ)^2/128 := by ring
  rw [hexp] at hh
  exact hh

/-- The actual conditioned cut-error probability satisfies the manuscript's 384ω/ε² bound. -/
theorem triangle_conditioned_cut_error_probability (n : ℕ) (hn : 0<n) {p η ε ω : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) (hε : ε∈Ioo (0:ℝ) 1)
    (W : Finset (GraphEdgeCoordinate n)) (hHarris : ClassicalHarrisPositiveAssociation (↑Wᶜ))
    (hlarge : 2*4^n*Real.exp (-ε^2*p*(n:ℝ)^2/128)≤Real.exp (-ε^2*p*(n:ℝ)^2/256))
    (hD : (∑ y : W → Bool, revealedPatternMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y*
      finiteRelativeEntropy (unrevealedConditionalLaw (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)
      (productMarginals (unrevealedConditionalLaw (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)))≤
      ω*(p*(n:ℝ)^2)/2)
    (hlog : Real.log 2≤ω*(p*(n:ℝ)^2)) :
    finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η)
      (revealedFamilyEvent W (fun y => unrevealedCutEvent
        (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y ε p))≤384*ω/ε^2 := by
  have hv : 0<p*(n:ℝ)^2 := mul_pos hp.1 (sq_pos_of_pos (Nat.cast_pos.mpr hn))
  apply revealedFamilyEvent_cut_transfer _ (hypergraphLowerLaw_nonneg _ 3 ⟨hp.1.le,hp.2.le⟩ η)
    (hypergraphLowerLaw_sum _ 3 (by norm_num) (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hη)
    W _ hε.1 hv _ hD hlog
  intro y hy
  have hh := (triangle_unrevealed_product_cut_bound n hn hp hη hε W hHarris y hy).trans hlarge
  convert hh using 1
  congr 1
  ring

end SparseLowerTail.Section03

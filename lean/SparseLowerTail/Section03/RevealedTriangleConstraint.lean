import SparseLowerTail.Section03.Decorrelation
import SparseLowerTail.Section03.HypergraphVariational
import SparseLowerTail.Section03.FiniteProbabilityBounds

/-! The actual near-feasibility event obtained from triangle decorrelation. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conditional edge means with every revealed edge deleted. -/
def erasedConditionalMeans (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool) (i : ι) : ℝ :=
  if i∈W then 0 else revealedConditionalMoment q W y {i}

def patternHypergraphError (H : Finset (Finset ι)) (q : (ι → Bool) → ℝ)
    (W : Finset ι) (y : W → Bool) : ℝ :=
  ∑ A∈unrevealedHyperedges H W,
    |revealedConditionalMoment q W y A-∏ i∈A, revealedConditionalMoment q W y {i}|

/-- Deleting revealed means removes precisely the hyperedges meeting the revealed set. -/
theorem erasedConditionalMeans_count (H : Finset (Finset ι)) (q : (ι → Bool) → ℝ)
    (W : Finset ι) (y : W → Bool) :
    hypergraphWeightedCount H (erasedConditionalMeans q W y) =
      ∑ A∈unrevealedHyperedges H W, ∏ i∈A, revealedConditionalMoment q W y {i} := by
  unfold hypergraphWeightedCount unrevealedHyperedges
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hAW : Disjoint A W
  · rw [if_pos hAW]
    apply Finset.prod_congr rfl
    intro i hi
    have hiW : i∉W := fun h => (Finset.disjoint_left.mp hAW hi h).elim
    simp [erasedConditionalMeans,hiW]
  · rw [if_neg hAW]
    obtain ⟨i,hiA,hiW⟩ := Finset.not_disjoint_iff.mp hAW
    exact Finset.prod_eq_zero hiA (by simp [erasedConditionalMeans,hiW])

/-- The sum of genuine conditional hyperedge moments is the conditional count expectation. -/
theorem revealedConditionalMoment_sum (H : Finset (Finset ι)) (q : (ι → Bool) → ℝ)
    (W : Finset ι) (y : W → Bool) :
    (∑ A∈H, revealedConditionalMoment q W y A) =
      ∑ z, finiteConditionedMass q (revealedPatternEvent W y) z*hypergraphRealCount H z := by
  unfold hypergraphRealCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  simp_rw [booleanProduct_eq_allTrue,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter,revealedConditionalMoment,finiteEventMass]

/-- Lower-tail conditioning continues to enforce the count bound after revealing any positive-mass pattern. -/
theorem hypergraph_conditional_count_le (H : Finset (Finset ι)) (r : ℕ) {p η : ℝ}
    (hp : p∈Icc (0:ℝ) 1) (W : Finset ι) (y : W → Bool)
    (hy : 0<revealedPatternMass (hypergraphLowerLaw H r p η) W y) :
    (∑ A∈H, revealedConditionalMoment (hypergraphLowerLaw H r p η) W y A)≤η*p^r*H.card := by
  let q := hypergraphLowerLaw H r p η
  let qc := finiteConditionedMass q (revealedPatternEvent W y)
  have hq : ∀ z, 0≤q z := hypergraphLowerLaw_nonneg H r hp η
  have hqc : ∀ z, 0≤qc z := finiteConditionedMass_nonneg q hq _
  have hsum : ∑ z, qc z=1 := finiteConditionedMass_sum q _ hy
  rw [revealedConditionalMoment_sum]
  have hpoint : ∀ z, qc z*hypergraphRealCount H z≤qc z*(η*p^r*H.card) := by
    intro z
    by_cases hz : z∈hypergraphLowerEvent H r p η
    · exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hz).2 (hqc z)
    · have hzero : q z=0 := by simp [q,hypergraphLowerLaw,finiteConditionedMass,hz]
      have hczero : qc z=0 := by
        unfold qc finiteConditionedMass
        split_ifs <;> simp [hzero]
      rw [hczero,zero_mul,zero_mul]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun z _ => hpoint z)
  simpa only [← Finset.sum_mul,hsum,one_mul] using hh

/-- The prediction can exceed the true conditional count only by its decorrelation error. -/
theorem erasedConditionalMeans_count_le (H : Finset (Finset ι)) (r : ℕ) {p η : ℝ}
    (hp : p∈Icc (0:ℝ) 1) (W : Finset ι) (y : W → Bool)
    (hy : 0<revealedPatternMass (hypergraphLowerLaw H r p η) W y) :
    hypergraphWeightedCount H (erasedConditionalMeans (hypergraphLowerLaw H r p η) W y)≤
      η*p^r*H.card+patternHypergraphError H (hypergraphLowerLaw H r p η) W y := by
  let q := hypergraphLowerLaw H r p η
  have hnonneg : ∀ A, 0≤revealedConditionalMoment q W y A := fun A =>
    Finset.sum_nonneg (fun z _ => finiteConditionedMass_nonneg q (hypergraphLowerLaw_nonneg H r hp η) _ z)
  have hsubset : (∑ A∈unrevealedHyperedges H W, revealedConditionalMoment q W y A)≤
      ∑ A∈H, revealedConditionalMoment q W y A := by
    unfold unrevealedHyperedges
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro A _
    split_ifs
    · exact le_rfl
    · exact hnonneg A
  have hpred : (∑ A∈unrevealedHyperedges H W, ∏ i∈A, revealedConditionalMoment q W y {i})≤
      (∑ A∈unrevealedHyperedges H W, revealedConditionalMoment q W y A)+patternHypergraphError H q W y := by
    rw [patternHypergraphError,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro A _
    have hh := neg_le_abs (revealedConditionalMoment q W y A-∏ i∈A, revealedConditionalMoment q W y {i})
    linarith
  rw [erasedConditionalMeans_count]
  exact hpred.trans (add_le_add_right (hsubset.trans (hypergraph_conditional_count_le H r hp W y hy)) _)

/-- The actual probability of failing the relaxed triangle constraint is at most β/ζ. -/
theorem hypergraph_relaxed_constraint_probability (H : Finset (Finset ι)) (r : ℕ) {p η β ζ : ℝ}
    (hp : p∈Icc (0:ℝ) 1) (hζ : 0<ζ) (hM : 0<p^r*(H.card:ℝ)) (W : Finset ι)
    (hbudget : hypergraphConditionalError H (hypergraphLowerLaw H r p η) W≤β*p^r*H.card) :
    finiteEventMass (revealedPatternMass (hypergraphLowerLaw H r p η) W)
      (Finset.univ.filter (fun y => (η+ζ)*p^r*H.card<
        hypergraphWeightedCount H (erasedConditionalMeans (hypergraphLowerLaw H r p η) W y)))≤β/ζ := by
  let q := hypergraphLowerLaw H r p η
  let μ := revealedPatternMass q W
  let E := Finset.univ.filter (fun y => (η+ζ)*p^r*H.card<
    hypergraphWeightedCount H (erasedConditionalMeans q W y))
  have hμ : ∀ y, 0≤μ y := fun y =>
    Finset.sum_nonneg (fun z _ => hypergraphLowerLaw_nonneg H r hp η z)
  have herr : ∀ y, 0≤patternHypergraphError H q W y := fun y =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpoint : ∀ y∈E, μ y*(ζ*(p^r*H.card))≤μ y*patternHypergraphError H q W y := by
    intro y hy
    by_cases hyzero : μ y=0
    · simp [hyzero]
    · have hypos : 0<μ y := lt_of_le_of_ne (hμ y) (Ne.symm hyzero)
      have hpredict := erasedConditionalMeans_count_le H r hp W y hypos
      have hbad := (Finset.mem_filter.mp hy).2
      apply mul_le_mul_of_nonneg_left _ (hμ y)
      dsimp [q] at hbad ⊢
      nlinarith
  have hmarkov : finiteEventMass μ E*(ζ*(p^r*H.card))≤hypergraphConditionalError H q W := by
    unfold finiteEventMass
    rw [Finset.sum_mul]
    calc
      _≤∑ y∈E, μ y*patternHypergraphError H q W y := Finset.sum_le_sum hpoint
      _≤∑ y, μ y*patternHypergraphError H q W y :=
        Finset.sum_le_univ_sum_of_nonneg (fun y => mul_nonneg (hμ y) (herr y))
  apply (le_div_iff₀ hζ).mpr
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    (p^r*H.card)*(finiteEventMass μ E*ζ)=finiteEventMass μ E*(ζ*(p^r*H.card)) := by ring
    _≤hypergraphConditionalError H q W := hmarkov
    _≤(p^r*H.card)*β := by simpa only [mul_assoc,mul_comm,mul_left_comm] using hbudget

/-- Specialization of the relaxed-constraint estimate to the actual triangle law. -/
theorem triangle_relaxed_constraint_probability (n : ℕ) (hn : 3≤n) {p η β ζ : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hζ : 0<ζ) (W : Finset (GraphEdgeCoordinate n))
    (hbudget : hypergraphConditionalError (coordinateTriangleHypergraph n)
      (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W≤β*p^3*(n.choose 3:ℝ)) :
    finiteEventMass (revealedPatternMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W)
      (Finset.univ.filter (fun y => (η+ζ)*p^3*(n.choose 3:ℝ)<hypergraphWeightedCount
        (coordinateTriangleHypergraph n)
        (erasedConditionalMeans (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)))≤β/ζ := by
  have hM : 0<p^3*((coordinateTriangleHypergraph n).card:ℝ) := by
    rw [coordinateTriangleHypergraph_card]
    exact mul_pos (pow_pos hp.1 _) (by exact_mod_cast Nat.choose_pos hn)
  simpa only [coordinateTriangleHypergraph_card] using
    hypergraph_relaxed_constraint_probability (coordinateTriangleHypergraph n) 3 ⟨hp.1.le,hp.2.le⟩ hζ hM W
      (by simpa only [coordinateTriangleHypergraph_card] using hbudget)

/-- A revealed set of the prescribed size makes the actual relaxed triangle constraint hold
outside a set of conditional probability at most β/ζ. -/
theorem triangle_revealed_feasibility (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    {α β ζ : ℝ} (hα : α∈Ioo (0:ℝ) 1) (hβ : β∈Ioo (0:ℝ) 1) (hζ : 0<ζ) :
    ∃ L : ℝ, 4≤L ∧ ∀ n : ℕ, L≤(n:ℝ) → ∀ p : ℝ, p∈Ioo (0:ℝ) 1 →
      L*(n:ℝ)^(-(1/(2:ℝ)))≤p → p≤1/2 → ∀ η : ℝ, η∈Ioo (0:ℝ) 1 →
      ∃ W : Finset (GraphEdgeCoordinate n), (W.card:ℝ)≤α*(n.choose 2:ℝ) ∧
        finiteEventMass (revealedPatternMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W)
          (Finset.univ.filter (fun y => (η+ζ)*p^3*(n.choose 3:ℝ)<hypergraphWeightedCount
            (coordinateTriangleHypergraph n)
            (erasedConditionalMeans (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W y)))≤β/ζ := by
  obtain ⟨L,hL,hdec⟩ := triangle_decorrelation hSelection hCS hα hβ
  refine ⟨L,hL,?_⟩
  intro n hn p hp hpL hpmax η hη
  obtain ⟨W,hW,hbudget⟩ := hdec n hn p hpL hpmax η hη
  have hn3 : 3≤n := by exact_mod_cast (show (3:ℝ)≤n by linarith)
  exact ⟨W,hW,triangle_relaxed_constraint_probability n hn3 hp hζ W hbudget⟩

end SparseLowerTail.Section03

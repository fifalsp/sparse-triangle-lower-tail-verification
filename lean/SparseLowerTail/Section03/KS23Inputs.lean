import SparseLowerTail.Section03.TriangleHypergraphCoordinates

/-! Explicit finite-law versions of KS23 Lemma 18 and equation (33).
Both are generic hypergraph inputs, not triangle-specific conclusions. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hypergraphRealCount (H : Finset (Finset ι)) (z : ι → Bool) : ℝ :=
  ∑ A∈H, ∏ i∈A, ((z i).toNat:ℝ)

def hypergraphLowerEvent (H : Finset (Finset ι)) (r : ℕ) (p η : ℝ) : Finset (ι → Bool) :=
  Finset.univ.filter (fun z => hypergraphRealCount H z≤η*p^r*H.card)

def hypergraphLowerLaw (H : Finset (Finset ι)) (r : ℕ) (p η : ℝ) : (ι → Bool) → ℝ :=
  finiteConditionedMass (productBernoulliMass (fun _ : ι => p)) (hypergraphLowerEvent H r p η)

def revealedPatternEvent (W : Finset ι) (y : W → Bool) : Finset (ι → Bool) :=
  Finset.univ.filter (fun z => ∀ i : W, z i=y i)

def revealedPatternMass (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool) : ℝ :=
  finiteEventMass q (revealedPatternEvent W y)

def revealedConditionalMoment (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool)
    (A : Finset ι) : ℝ :=
  finiteEventMass (finiteConditionedMass q (revealedPatternEvent W y)) (allTrueEvent A)

def unrevealedHyperedges (H : Finset (Finset ι)) (W : Finset ι) : Finset (Finset ι) :=
  H.filter (fun A => Disjoint A W)

/-- The expected absolute difference between a joint conditional moment and its product marginals. -/
def hypergraphConditionalError (H : Finset (Finset ι)) (q : (ι → Bool) → ℝ)
    (W : Finset ι) : ℝ :=
  ∑ y : W → Bool, revealedPatternMass q W y *
    ∑ A∈unrevealedHyperedges H W,
      |revealedConditionalMoment q W y A - ∏ i∈A, revealedConditionalMoment q W y {i}|

/-- KS23 D_W(B,b), with the conditional law defined by actual revealed-coordinate fibers. -/
def ksConditionalCovariance (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool)
    (B : Finset ι) (b : ι) : ℝ :=
  revealedConditionalMoment q W y B -
    revealedConditionalMoment q W y (B.erase b)*revealedConditionalMoment q W y {b}

/-- KS23 equation (32), specialized only to unit hyperedge weights. -/
def ksConditionalEnergy (H : Finset (Finset ι)) (q : (ι → Bool) → ℝ)
    (W : Finset ι) (r : ℕ) (p : ℝ) : ℝ :=
  ∑ y : W → Bool, revealedPatternMass q W y *
    ∑ A∈unrevealedHyperedges H W, ∑ B∈A.powerset.filter (fun B => 2≤B.card),
      ∑ b∈B, (ksConditionalCovariance q W y B b)^2 /
        ((r.choose B.card:ℝ)*B.card*p^(2*B.card))

/-- Generic unweighted uniform-hypergraph energy selection in KS23 Lemma 18. -/
def KS23EnergySelection : Prop :=
  ∀ r : ℕ, 2≤r → ∀ p₀ : ℝ, p₀∈Ioo (0:ℝ) 1 →
  ∀ α β K : ℝ, 0<α → 0<β → 0<K →
  ∃ ell : ℝ, 0<ell ∧ ∃ V₀ : ℕ,
  ∀ (ν : Type) [Fintype ν] [DecidableEq ν] (H : Finset (Finset ν)),
    (∀ A∈H, A.card=r) → V₀≤Fintype.card ν →
  ∀ p η : ℝ, p∈Ioo (0:ℝ) 1 → p≤p₀ → η∈Icc (0:ℝ) 1 →
    (∀ S : Finset ν, 1≤S.card ∧ S.card≤r →
      (((H.filter (fun A => S⊆A)).card):ℝ)≤K*(ell*p)^(S.card-1)*H.card/Fintype.card ν) →
    ∃ W : Finset ν, (W.card:ℝ)≤α*Fintype.card ν ∧
      ksConditionalEnergy H (hypergraphLowerLaw H r p η) W r p≤β*H.card

/-- Generic conditional-error estimate in KS23 equation (33), including its r-1 factor. -/
def KS23ConditionalErrorBound : Prop :=
  ∀ (ν : Type) [Fintype ν] [DecidableEq ν] (H : Finset (Finset ν)) (r : ℕ),
    2≤r → (∀ A∈H, A.card=r) →
  ∀ p η : ℝ, p∈Ioo (0:ℝ) 1 → η∈Icc (0:ℝ) 1 → ∀ W : Finset ν,
    hypergraphConditionalError H (hypergraphLowerLaw H r p η) W ≤
      p^r*(Real.sqrt ((r-1:ℕ)*(unrevealedHyperedges H W).card)*
        Real.sqrt (ksConditionalEnergy H (hypergraphLowerLaw H r p η) W r p))

theorem hypergraphLowerLaw_nonneg (H : Finset (Finset ι)) (r : ℕ) {p : ℝ}
    (hp : p∈Icc (0:ℝ) 1) (η : ℝ) (z : ι → Bool) :
    0≤hypergraphLowerLaw H r p η z :=
  finiteConditionedMass_nonneg _ (fun z => finiteProductMass_nonneg _
    (fun _ b => bernoulliMass_nonneg hp b) z) _ z

theorem ksConditionalEnergy_nonneg (H : Finset (Finset ι)) (q : (ι → Bool) → ℝ)
    (hq : ∀ z, 0≤q z) (W : Finset ι) (r : ℕ) {p : ℝ} (hp : 0≤p) :
    0≤ksConditionalEnergy H q W r p := by
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (Finset.sum_nonneg (fun z _ => hq z))
  apply Finset.sum_nonneg; intro A _
  apply Finset.sum_nonneg; intro B _
  apply Finset.sum_nonneg; intro b _
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem hypergraphLowerEvent_probability_pos (H : Finset (Finset ι)) (r : ℕ)
    (hr : 1≤r) (hH : ∀ A∈H, A.card=r) {p η : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) :
    0<finiteEventMass (productBernoulliMass (fun _ : ι => p)) (hypergraphLowerEvent H r p η) := by
  have hz : hypergraphRealCount H (fun _ => false)=0 := by
    apply Finset.sum_eq_zero
    intro A hA
    have hAc : A.card≠0 := by have := hH A hA; omega
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hAc)
    exact Finset.prod_eq_zero ha (by simp)
  have hmem : (fun _ : ι => false)∈hypergraphLowerEvent H r p η := by
    simp only [hypergraphLowerEvent,Finset.mem_filter,Finset.mem_univ,true_and,hz]
    exact mul_nonneg (mul_nonneg hη (pow_nonneg hp.1.le _)) (Nat.cast_nonneg _)
  have hh := Finset.single_le_sum (s:=hypergraphLowerEvent H r p η)
    (f:=productBernoulliMass (fun _ : ι => p))
    (fun z _ => finiteProductMass_nonneg _ (fun _ b => bernoulliMass_nonneg ⟨hp.1.le,hp.2.le⟩ b) z) hmem
  exact (finiteProductMass_pos _ (fun _ b => bernoulliMass_pos hp b) (fun _ => false)).trans_le hh

theorem hypergraphLowerLaw_sum (H : Finset (Finset ι)) (r : ℕ)
    (hr : 1≤r) (hH : ∀ A∈H, A.card=r) {p η : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η) : ∑ z, hypergraphLowerLaw H r p η z=1 :=
  finiteConditionedMass_sum _ _ (hypergraphLowerEvent_probability_pos H r hr hH hp hη)

theorem revealedPatternMass_eq_marginal (q : (ι → Bool) → ℝ) (W : Finset ι) (y : W → Bool) :
    revealedPatternMass q W y=finiteMarginal q (fun z => fun i : W => z i) y := by
  classical
  simp only [revealedPatternMass,finiteEventMass,revealedPatternEvent,Finset.sum_filter,
    finiteMarginal,funext_iff]

theorem revealedPatternMass_sum (q : (ι → Bool) → ℝ) (W : Finset ι) :
    (∑ y : W → Bool, revealedPatternMass q W y)=∑ z, q z := by
  simp_rw [revealedPatternMass_eq_marginal]
  exact finiteMarginal_sum _ _

/-- A product of Boolean indicators is the indicator of the pinned-coordinate event. -/
theorem booleanProduct_eq_allTrue {A : Finset ι} (z : ι → Bool) :
    (∏ i∈A, ((z i).toNat:ℝ))=if z∈allTrueEvent A then 1 else 0 := by
  classical
  have hm : z∈allTrueEvent A ↔ ∀ i∈A, z i=true := by
    rw [allTrueEvent,Fintype.mem_piFinset]
    constructor
    · intro h i hi; simpa [hi] using h i
    · intro h i
      by_cases hi : i∈A
      · simpa [hi] using h i hi
      · simp [hi]
  by_cases h : ∀ i∈A, z i=true
  · rw [if_pos (hm.mpr h)]
    apply Finset.prod_eq_one
    intro i hi; simp [h i hi]
  · rw [if_neg (mt hm.mp h)]
    push_neg at h
    obtain ⟨i,hi,hzi⟩ := h
    apply Finset.prod_eq_zero hi
    cases hb : z i <;> simp_all

/-- The independent product law has exactly p^r times the hyperedge count as its mean. -/
theorem hypergraphRealCount_expectation (H : Finset (Finset ι)) (r : ℕ)
    (hH : ∀ A∈H, A.card=r) (p : ℝ) :
    (∑ z, productBernoulliMass (fun _ : ι => p) z*hypergraphRealCount H z)=p^r*H.card := by
  classical
  unfold hypergraphRealCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he : ∀ A∈H, (∑ z, productBernoulliMass (fun _ : ι => p) z*
      ∏ i∈A, ((z i).toNat:ℝ))=p^r := by
    intro A hA
    simp_rw [booleanProduct_eq_allTrue,mul_ite,mul_one,mul_zero]
    simp only [Finset.sum_ite_mem,Finset.univ_inter]
    change finiteEventMass (productBernoulliMass (fun _ : ι => p)) (allTrueEvent A)=p^r
    rw [productBernoulliMass_allTrueEvent]
    simp [hH A hA]
  calc
    _ = ∑ _A∈H, p^r := Finset.sum_congr rfl he
    _ = _ := by simp; ring

/-- The lower-tail event is normalized by the actual independent expectation. -/
theorem hypergraphLowerEvent_eq_expected (H : Finset (Finset ι)) (r : ℕ)
    (hH : ∀ A∈H, A.card=r) (p η : ℝ) :
    hypergraphLowerEvent H r p η=Finset.univ.filter (fun z => hypergraphRealCount H z≤
      η*(∑ z', productBernoulliMass (fun _ : ι => p) z'*hypergraphRealCount H z')) := by
  rw [hypergraphRealCount_expectation H r hH p]
  unfold hypergraphLowerEvent
  congr 1; funext z; ring_nf

end SparseLowerTail.Section03

import SparseLowerTail.Section03.HypergraphVariational

/-! Generic, unit-weight hypergraph instances of KS23 Theorems 5 and 6.
No triangle specialization, graphon value, or asymptotic conclusion is included in these inputs. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hypergraphLowerTailRate (H : Finset (Finset ι)) (r : ℕ) (p η : ℝ) : ℝ :=
  -Real.log (finiteEventMass (productBernoulliMass (fun _ : ι => p)) (hypergraphLowerEvent H r p η))

theorem hypergraphWeightedCount_expectation (H : Finset (Finset ι)) (q : ι → ℝ) :
    (∑ z, productBernoulliMass q z*hypergraphRealCount H z)=hypergraphWeightedCount H q := by
  classical
  unfold hypergraphRealCount hypergraphWeightedCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  simp_rw [booleanProduct_eq_allTrue,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  exact productBernoulliMass_allTrueEvent q A

omit [Fintype ι] [DecidableEq ι] in
theorem hypergraphWeightedCount_constant (H : Finset (Finset ι)) (r : ℕ)
    (hH : ∀ A∈H, A.card=r) (p : ℝ) :
    hypergraphWeightedCount H (fun _ => p)=p^r*H.card := by
  unfold hypergraphWeightedCount
  have he : ∀ A∈H, (∏ _i∈A, p)=p^r := by intro A hA; simp [hH A hA]
  rw [Finset.sum_congr rfl he]
  simp; ring

theorem hypergraphLowerTailRate_nonneg (H : Finset (Finset ι)) (r : ℕ) {p : ℝ}
    (hp : p∈Icc (0:ℝ) 1) (η : ℝ) : 0≤hypergraphLowerTailRate H r p η := by
  have hmass : ∀ z : ι → Bool, 0≤productBernoulliMass (fun _ => p) z :=
    fun z => finiteProductMass_nonneg _ (fun _ b => bernoulliMass_nonneg hp b) z
  have hlo : 0≤finiteEventMass (productBernoulliMass (fun _ : ι => p)) (hypergraphLowerEvent H r p η) :=
    Finset.sum_nonneg (fun z _ => hmass z)
  have hhi : finiteEventMass (productBernoulliMass (fun _ : ι => p)) (hypergraphLowerEvent H r p η)≤1 := by
    rw [← productBernoulliMass_sum (fun _ : ι => p)]
    exact Finset.sum_le_univ_sum_of_nonneg (fun z => hmass z)
  exact neg_nonneg.mpr (Real.log_nonpos hlo hhi)

/-- KS23 Theorem 5, restricted only to unit-weight uniform hypergraphs. -/
def KS23HypergraphLowerBound : Prop :=
  ∀ r : ℕ, 2≤r → ∀ p₀ ε K : ℝ, p₀∈Ioo (0:ℝ) 1 → 0<ε → 0<K →
  ∃ ell : ℝ, 0<ell ∧ ∃ C : ℝ, 0≤C ∧
  ∀ (ν : Type) [Fintype ν] [DecidableEq ν] (H : Finset (Finset ν)),
    H.Nonempty → (∀ A∈H, A.card=r) →
  ∀ p η : ℝ, p∈Ioo (0:ℝ) 1 → p≤p₀ → 0≤η →
    (∀ S : Finset ν, 1≤S.card ∧ S.card≤r →
      (((H.filter (fun A => S⊆A)).card):ℝ)≤K*(ell*p)^(S.card-1)*H.card/Fintype.card ν) →
    (1-ε)*hypergraphPhi H r p (η+ε)-C≤hypergraphLowerTailRate H r p η

/-- KS23 Theorem 6 applied to arbitrary uniform hypergraph counts, which are increasing. -/
def KS23HypergraphUpperBound : Prop :=
  ∀ p₀ ε : ℝ, p₀∈Ioo (0:ℝ) 1 → ε∈Ioo (0:ℝ) 1 → ∃ C : ℝ, 0≤C ∧
  ∀ (ν : Type) [Fintype ν] [DecidableEq ν] (H : Finset (Finset ν)) (r : ℕ),
    1≤r → (∀ A∈H, A.card=r) →
  ∀ p η : ℝ, p∈Ioo (0:ℝ) 1 → p≤p₀ → 0≤η →
    hypergraphLowerTailRate H r p η≤(1+ε)*hypergraphPhi H r p ((1-ε)*η)+C

end SparseLowerTail.Section03

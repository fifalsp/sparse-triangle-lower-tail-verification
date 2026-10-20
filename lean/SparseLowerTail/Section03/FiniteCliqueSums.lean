import SparseLowerTail.Section03.FiniteStepGraphon

/-! Exact multiplicities for unordered edges and triangles in finite matrix sums. -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- An unordered pair has exactly its two orientations. -/
theorem ordered_pair_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (x y : α) (hxy : x≠y) :
    (Finset.univ.filter (fun ij : α×α => ({ij.1,ij.2} : Finset α)={x,y}))=
      {(x,y),(y,x)} := by
  ext ij
  rcases ij with ⟨i,j⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_singleton,Prod.mk.injEq]
  constructor
  · intro h
    have hi : i=x ∨ i=y := by
      have : i∈({x,y}:Finset α) := h ▸ (by simp)
      simpa using this
    have hj : j=x ∨ j=y := by
      have : j∈({x,y}:Finset α) := h ▸ (by simp)
      simpa using this
    have hx : x∈({i,j}:Finset α) := by rw [h]; simp
    have hy : y∈({i,j}:Finset α) := by rw [h]; simp
    clear h
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> simp_all
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> simp [Finset.pair_comm]

/-- A three-element set has exactly six ordered listings. -/
theorem ordered_triple_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (x y z : α) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    (Finset.univ.filter (fun ijk : α×(α×α) => ({ijk.1,ijk.2.1,ijk.2.2}:Finset α)={x,y,z}))=
      {(x,y,z),(x,z,y),(y,x,z),(y,z,x),(z,x,y),(z,y,x)} := by
  ext ijk
  rcases ijk with ⟨i,j,k⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_singleton,Prod.mk.injEq]
  constructor
  · intro h
    have hi : i=x ∨ i=y ∨ i=z := by
      have : i∈({x,y,z}:Finset α) := h ▸ (by simp)
      simpa using this
    have hj : j=x ∨ j=y ∨ j=z := by
      have : j∈({x,y,z}:Finset α) := h ▸ (by simp)
      simpa using this
    have hk : k=x ∨ k=y ∨ k=z := by
      have : k∈({x,y,z}:Finset α) := h ▸ (by simp)
      simpa using this
    have hx : x∈({i,j,k}:Finset α) := by rw [h]; simp
    have hy : y∈({i,j,k}:Finset α) := by rw [h]; simp
    have hz : z∈({i,j,k}:Finset α) := by rw [h]; simp
    clear h
    rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl <;>
      rcases hk with rfl|rfl|rfl <;> simp_all <;> aesop
  · rintro (⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
      ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩) <;>
      ext a <;> simp <;> tauto

/-- Summing any unordered-pair weight over all ordered distinct pairs doubles it. -/
theorem sum_ordered_pairs {α : Type*} [Fintype α] [DecidableEq α] (f : Finset α → ℝ) :
    (∑ i, ∑ j, if i=j then 0 else f {i,j})=
      2*∑ e∈Finset.univ.powersetCard 2, f e := by
  classical
  have hh := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (α×α))
    (Finset.univ.powersetCard 2) (fun ij => ({ij.1,ij.2}:Finset α))
    (fun ij => f {ij.1,ij.2})
  have hleft : (∑ e∈Finset.univ.powersetCard 2,
      ∑ ij∈Finset.univ.filter (fun ij : α×α => {ij.1,ij.2}=e), f {ij.1,ij.2})=
      2*∑ e∈Finset.univ.powersetCard 2, f e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hf : (∑ ij∈Finset.univ.filter (fun ij : α×α => {ij.1,ij.2}=e), f {ij.1,ij.2})=
        ((Finset.univ.filter (fun ij : α×α => {ij.1,ij.2}=e)).card:ℝ)*f e := by
      calc
        _ = ∑ _ij∈Finset.univ.filter (fun ij : α×α => {ij.1,ij.2}=e), f e := by
          apply Finset.sum_congr rfl
          intro ij hij; rw [(Finset.mem_filter.mp hij).2]
        _ = _ := by simp
    rw [hf]
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard_univ.mp he)
    rw [ordered_pair_fiber x y hxy]
    simp [hxy]
  rw [hleft] at hh
  rw [hh,Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases hij : i=j <;> simp [hij]

/-- Summing any unordered-triangle weight over distinct ordered triples multiplies it by six. -/
theorem sum_ordered_triples {α : Type*} [Fintype α] [DecidableEq α] (f : Finset α → ℝ) :
    (∑ i, ∑ j, ∑ k, if i=j ∨ i=k ∨ j=k then 0 else f {i,j,k})=
      6*∑ T∈Finset.univ.powersetCard 3, f T := by
  classical
  have hh := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (α×(α×α)))
    (Finset.univ.powersetCard 3) (fun ijk => ({ijk.1,ijk.2.1,ijk.2.2}:Finset α))
    (fun ijk => f {ijk.1,ijk.2.1,ijk.2.2})
  have hleft : (∑ T∈Finset.univ.powersetCard 3,
      ∑ ijk∈Finset.univ.filter (fun ijk : α×(α×α) => {ijk.1,ijk.2.1,ijk.2.2}=T),
        f {ijk.1,ijk.2.1,ijk.2.2})=6*∑ T∈Finset.univ.powersetCard 3, f T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hf : (∑ ijk∈Finset.univ.filter (fun ijk : α×(α×α) => {ijk.1,ijk.2.1,ijk.2.2}=T),
        f {ijk.1,ijk.2.1,ijk.2.2})=
        ((Finset.univ.filter (fun ijk : α×(α×α) => {ijk.1,ijk.2.1,ijk.2.2}=T)).card:ℝ)*f T := by
      calc
        _ = ∑ _ijk∈Finset.univ.filter (fun ijk : α×(α×α) => {ijk.1,ijk.2.1,ijk.2.2}=T), f T := by
          apply Finset.sum_congr rfl
          intro ijk hijk; rw [(Finset.mem_filter.mp hijk).2]
        _ = _ := by simp
    rw [hf]
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ :=
      Finset.card_eq_three.mp (Finset.mem_powersetCard_univ.mp hT)
    rw [ordered_triple_fiber x y z hxy hxz hyz]
    simp [hxy,hxz,hyz,Ne.symm hxy,Ne.symm hxz,Ne.symm hyz]
  rw [hleft] at hh
  rw [hh,Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  by_cases hij : i=j
  · subst j; by_cases hik : i=k <;> simp [hik]
  by_cases hik : i=k
  · subst k; simp [hij,Ne.symm hij]
  by_cases hjk : j=k
  · subst k; simp [hij]
  simp [hij,hik,hjk]

end SparseLowerTail.Section03

import SparseLowerTail.Section03.BalancedFiniteColoring

/-! Exact finite color-frequency formulas for entropy and triangle recovery sums. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SparseLowerTail.Section03

/-- A finite sum grouped by its actual colors. -/
theorem sum_finite_colors {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (f : κ → ℝ) :
    (∑ i, f (c i))=∑ a, (∑ i, if c i=a then (1:ℝ) else 0)*f a := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

def finiteColorMass {n K : ℕ} (c : Fin n → Fin K) (a : Fin K) : ℝ :=
  (∑ i, if c i=a then (1:ℝ) else 0)/(n:ℝ)

theorem sum_finite_colors_pair {n K : ℕ} (c : Fin n → Fin K) (g : Fin K → Fin K → ℝ) :
    (∑ i, ∑ j, g (c i) (c j))/(n:ℝ)^2=
      ∑ a, ∑ b, finiteColorMass c a*finiteColorMass c b*g a b := by
  rw [sum_finite_colors c (fun a => ∑ j, g a (c j))]
  have hj : ∀ a, (∑ j, g a (c j))=∑ b, (∑ j, if c j=b then (1:ℝ) else 0)*g a b :=
    fun a => sum_finite_colors c (g a)
  simp_rw [hj,Finset.mul_sum]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  unfold finiteColorMass
  ring

theorem sum_finite_colors_triple {n K : ℕ} (c : Fin n → Fin K)
    (g : Fin K → Fin K → Fin K → ℝ) :
    (∑ i, ∑ j, ∑ k, g (c i) (c j) (c k))/(n:ℝ)^3=
      ∑ a, ∑ b, ∑ d, finiteColorMass c a*finiteColorMass c b*finiteColorMass c d*g a b d := by
  rw [sum_finite_colors c (fun a => ∑ j, ∑ k, g a (c j) (c k))]
  have hj : ∀ a, (∑ j, ∑ k, g a (c j) (c k))=
      ∑ b, (∑ j, if c j=b then (1:ℝ) else 0)*(∑ k, g a b (c k)) :=
    fun a => sum_finite_colors c (fun b => ∑ k, g a b (c k))
  have hk : ∀ a b, (∑ k, g a b (c k))=
      ∑ d, (∑ k, if c k=d then (1:ℝ) else 0)*g a b d :=
    fun a b => sum_finite_colors c (g a b)
  simp_rw [hj,hk,Finset.mul_sum]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro d _
  unfold finiteColorMass
  ring

/-- Pair observables of the balanced finite copies converge to their uniform block sum. -/
theorem balanced_pair_average_tendsto (K : ℕ) (hK : 0<K) (g : Fin K → Fin K → ℝ) :
    Tendsto (fun n => (∑ i, ∑ j,
      g (balancedVertexColor K hK n i) (balancedVertexColor K hK n j))/(n:ℝ)^2)
      atTop (𝓝 ((∑ a, ∑ b, g a b)/(K:ℝ)^2)) := by
  have hterm : ∀ a b, Tendsto (fun n =>
      finiteColorMass (balancedVertexColor K hK n) a*
        finiteColorMass (balancedVertexColor K hK n) b*g a b)
      atTop (𝓝 ((1/(K:ℝ))*(1/(K:ℝ))*g a b)) := by
    intro a b
    exact ((balancedColorMass_tendsto K hK a).mul (balancedColorMass_tendsto K hK b)).mul_const _
  have hh := tendsto_finset_sum Finset.univ (fun a _ =>
    tendsto_finset_sum Finset.univ (fun b _ => hterm a b))
  have he : (∑ a, ∑ b, (1/(K:ℝ))*(1/(K:ℝ))*g a b)=
      (∑ a, ∑ b, g a b)/(K:ℝ)^2 := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _; ring
  rw [he] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n => (sum_finite_colors_pair (balancedVertexColor K hK n) g).symm)

/-- Triple observables converge for every vertex count, including incomplete batches. -/
theorem balanced_triple_average_tendsto (K : ℕ) (hK : 0<K)
    (g : Fin K → Fin K → Fin K → ℝ) :
    Tendsto (fun n => (∑ i, ∑ j, ∑ k,
      g (balancedVertexColor K hK n i) (balancedVertexColor K hK n j)
        (balancedVertexColor K hK n k))/(n:ℝ)^3)
      atTop (𝓝 ((∑ a, ∑ b, ∑ d, g a b d)/(K:ℝ)^3)) := by
  have hterm : ∀ a b d, Tendsto (fun n =>
      finiteColorMass (balancedVertexColor K hK n) a*
        finiteColorMass (balancedVertexColor K hK n) b*
        finiteColorMass (balancedVertexColor K hK n) d*g a b d)
      atTop (𝓝 ((1/(K:ℝ))*(1/(K:ℝ))*(1/(K:ℝ))*g a b d)) := by
    intro a b d
    exact (((balancedColorMass_tendsto K hK a).mul
      (balancedColorMass_tendsto K hK b)).mul (balancedColorMass_tendsto K hK d)).mul_const _
  have hh := tendsto_finset_sum Finset.univ (fun a _ =>
    tendsto_finset_sum Finset.univ (fun b _ =>
      tendsto_finset_sum Finset.univ (fun d _ => hterm a b d)))
  have he : (∑ a, ∑ b, ∑ d, (1/(K:ℝ))*(1/(K:ℝ))*(1/(K:ℝ))*g a b d)=
      (∑ a, ∑ b, ∑ d, g a b d)/(K:ℝ)^3 := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro d _; ring
  rw [he] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n => (sum_finite_colors_triple (balancedVertexColor K hK n) g).symm)

end SparseLowerTail.Section03

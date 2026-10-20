import SparseLowerTail.Section03.FiniteColorSums

/-! Turn finite matrix samples into genuine unordered edge weights and bound diagonal deletion. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SparseLowerTail.Section03
open Section02

/-- Read an unordered pair using its least and greatest vertices. -/
def edgeWeightFromMatrix {n : ℕ} (Z : Fin n → Fin n → ℝ) (e : Finset (Fin n)) : ℝ :=
  if he : e.Nonempty then Z (e.min' he) (e.max' he) else 0

theorem edgeWeightFromMatrix_pair {n : ℕ} (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (i j : Fin n) :
    edgeWeightFromMatrix Z {i,j}=Z i j := by
  simp only [edgeWeightFromMatrix,Finset.insert_nonempty,dif_pos,Finset.min'_pair,Finset.max'_pair]
  rcases le_total i j with h|h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,hsym]

theorem edgeWeightFromMatrix_bounds {n : ℕ} (Z : Fin n → Fin n → ℝ)
    (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) (e : Finset (Fin n)) :
    edgeWeightFromMatrix Z e∈Icc (0:ℝ) 1 := by
  unfold edgeWeightFromMatrix
  split_ifs
  · exact hb _ _
  · exact ⟨le_rfl,zero_le_one⟩

theorem graphEdgeMatrix_fromMatrix {n : ℕ} (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (i j : Fin n) :
    graphEdgeMatrix (edgeWeightFromMatrix Z) i j=if i=j then 0 else Z i j := by
  classical
  simp only [graphEdgeMatrix,edgeWeightFromMatrix_pair Z hsym]

/-- Deleting the diagonal costs at most 1/n in normalized entropy. -/
theorem edgeStepGraphon_fromMatrix_cost_le (n : ℕ) (hn : 0<n)
    (Z : Fin n → Fin n → ℝ) (hsym : ∀ i j, Z i j=Z j i)
    (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) :
    cost (edgeStepGraphon n hn (edgeWeightFromMatrix Z)
      (fun e _ => edgeWeightFromMatrix_bounds Z hb e))≤
      (∑ i, ∑ j, entropy (Z i j))/(n:ℝ)^2+1/(n:ℝ) := by
  classical
  rw [edgeStepGraphon,uniformStepGraphon_cost]
  have hs : (∑ i, ∑ j, entropy (graphEdgeMatrix (edgeWeightFromMatrix Z) i j))≤
      (∑ i, ∑ j, entropy (Z i j))+(n:ℝ) := by
    have hh : (∑ i, ∑ j, entropy (graphEdgeMatrix (edgeWeightFromMatrix Z) i j))≤
        ∑ i, ∑ j, (entropy (Z i j)+(if i=j then 1 else 0)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [graphEdgeMatrix_fromMatrix Z hsym]
      by_cases hij : i=j
      · subst j
        simp only [ite_true,entropy_zero]
        linarith [entropy_nonneg (hb i i).1]
      · simp [hij]
    simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hh := div_le_div_of_nonneg_right hs (sq_nonneg (n:ℝ))
  convert hh using 1
  field_simp [hn0]

/-- Deleting the diagonal cannot increase any nonnegative triangle product. -/
theorem edgeStepGraphon_fromMatrix_triangle_le (n : ℕ)
    (Z : Fin n → Fin n → ℝ) (hsym : ∀ i j, Z i j=Z j i)
    (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) :
    6*weightedTriangleCount (edgeWeightFromMatrix Z)/(n:ℝ)^3≤
      (∑ i, ∑ j, ∑ k, Z i j*Z j k*Z i k)/(n:ℝ)^3 := by
  classical
  rw [← graphEdgeMatrix_triangle_sum]
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg n) 3)
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  apply Finset.sum_le_sum; intro k _
  have hg : ∀ a b, 0≤graphEdgeMatrix (edgeWeightFromMatrix Z) a b ∧
      graphEdgeMatrix (edgeWeightFromMatrix Z) a b≤Z a b := by
    intro a b
    rw [graphEdgeMatrix_fromMatrix Z hsym]
    by_cases hab : a=b
    · subst b
      simp only [ite_true]
      exact ⟨le_rfl,(hb a a).1⟩
    · simp [hab,(hb a b).1]
  exact mul_le_mul (mul_le_mul (hg i j).2 (hg j k).2 (hg j k).1 (hb i j).1)
    (hg i k).2 (hg i k).1 (mul_nonneg (hb i j).1 (hb j k).1)

end SparseLowerTail.Section03

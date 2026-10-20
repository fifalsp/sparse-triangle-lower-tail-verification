import SparseLowerTail.Section03.DiscreteEntropyLower

/-! The uniform entropy upper estimate for a finite step-graphon recovery vector. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

/-- The number of graph edges is bounded by n squared over two. -/
theorem graph_edge_count_le_half_square (n : ℕ) :
    (n.choose 2:ℝ)≤(n:ℝ)^2/2 := by
  rw [Nat.cast_choose_two]
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

/-- The exact finite-graph entropy upper estimate used in discrete(b).
The candidate's feasibility and approximation properties are separate obligations. -/
theorem finiteEdgeEntropy_upper (n : ℕ) (hn : 0<n) {p : ℝ} (hp : p∈Ioo (0:ℝ) 1)
    (q : Finset (Fin n) → ℝ) (hq : ∀ e∈completeGraphEdges n, q e∈Icc (0:ℝ) p) :
    let hw : ∀ e∈completeGraphEdges n, q e/p∈Icc (0:ℝ) 1 :=
      fun e he => ⟨div_nonneg (hq e he).1 hp.1.le,(div_le_one hp.1).mpr (hq e he).2⟩
    finiteEdgeEntropy n p q≤(n:ℝ)^2*p/2*
      (cost (edgeStepGraphon n hn (fun e => q e/p) hw)+p/(2*(1-p))) := by
  classical
  dsimp only
  let hw : ∀ e∈completeGraphEdges n, q e/p∈Icc (0:ℝ) 1 :=
    fun e he => ⟨div_nonneg (hq e he).1 hp.1.le,(div_le_one hp.1).mpr (hq e he).2⟩
  have hc := edgeStepGraphon_cost n hn (fun e => q e/p) hw
  have hs : finiteEdgeEntropy n p q≤
      p*(∑ e∈completeGraphEdges n, entropy (q e/p))+(n.choose 2:ℝ)*p*(p/(2*(1-p))) := by
    have hsum : finiteEdgeEntropy n p q≤
        ∑ e∈completeGraphEdges n, (p*entropy (q e/p)+p*(p/(2*(1-p)))) := by
      apply Finset.sum_le_sum
      intro e he
      have hb := (sparse_entropy_bounds hp (hw e he)).2.1.trans (sparse_entropy_bounds hp (hw e he)).2.2
      have hcancel : p*(q e/p)=q e := by field_simp [hp.1.ne']
      rw [hcancel] at hb
      have hm := mul_le_mul_of_nonneg_left hb hp.1.le
      have hc' : p*(bernoulliEntropy p (q e)/p-entropy (q e/p))=
          bernoulliEntropy p (q e)-p*entropy (q e/p) := by field_simp [hp.1.ne']
      rw [hc'] at hm
      linarith
    simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
      nsmul_eq_mul,completeGraphEdges_card,mul_assoc,mul_left_comm,mul_comm] using hsum
  have herr : 0≤p/(2*(1-p)) := div_nonneg hp.1.le (by linarith [hp.2])
  have hcount := mul_le_mul_of_nonneg_right (graph_edge_count_le_half_square n)
    (mul_nonneg hp.1.le herr)
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [hc]
  have he : (n:ℝ)^2*p/2*(2/(n:ℝ)^2*(∑ e∈completeGraphEdges n, entropy (q e/p))+1/(n:ℝ)+p/(2*(1-p)))=
      p*(∑ e∈completeGraphEdges n, entropy (q e/p))+(n:ℝ)^2*p/2*(p/(2*(1-p)))+(n:ℝ)*p/2 := by
    field_simp [hn0,(sub_pos.mpr hp.2).ne']
    ring
  rw [he]
  have hnp : 0≤(n:ℝ)*p/2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) hp.1.le) (by norm_num)
  nlinarith

end SparseLowerTail.Section03

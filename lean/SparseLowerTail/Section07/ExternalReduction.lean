import SparseLowerTail.BalancedExistence

/-!
# External penalized reduction and its constrained consequence

Paper anchors: `eq:KP`, and the transfer argument used in `prop:smalldata`.
KP26, Theorem 1.6, is an explicitly assumed external theorem. It is represented
by a proposition passed as a theorem parameter, not by a global Lean axiom.
The transfer from penalized to constrained optimality below is proved here.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section07

def balancedPenalty (γ a b : ℝ) : ℝ := balancedCost a b + γ * balancedTriangle a b

def IsBalancedPenalizedMinimizer (γ a b : ℝ) : Prop :=
  a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧
    ∀ c d : ℝ, c ∈ Icc 0 1 → d ∈ Icc 0 1 →
      balancedPenalty γ a b ≤ balancedPenalty γ c d

/-- External input KP26, Theorem 1.6, specialized exactly as `eq:KP` in the
paper. Every balanced penalized minimizer attains a lower bound valid for all
graphons. This proposition is NOT asserted or proved in this development. -/
def KP26PenalizedReduction : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ a b : ℝ, IsBalancedPenalizedMinimizer γ a b →
    ∀ U : Graphon, balancedPenalty γ a b ≤ cost U + γ * triangle U

/-- The scalar penalized problem does attain its minimum; this is elementary
compactness and is independent of the external KP26 input. -/
theorem exists_balancedPenalizedMinimizer (γ : ℝ) :
    ∃ a b : ℝ, IsBalancedPenalizedMinimizer γ a b := by
  have hc : Continuous (fun p : ℝ × ℝ => balancedPenalty γ p.1 p.2) :=
    continuous_balancedCost.add (continuous_const.mul continuous_balancedTriangle)
  obtain ⟨p, hp, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (show ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1)).Nonempty from
      ⟨(0,0), by norm_num⟩) hc.continuousOn
  refine ⟨p.1, p.2, hp.1, hp.2, ?_⟩
  intro c d hc hd
  exact hmin (show (c,d) ∈ (Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1) from ⟨hc, hd⟩)

/-- The external reduction implies that a scalar penalized minimizer is also
an unrestricted penalized minimizer after realizing it as a graphon. -/
theorem penalized_global_of_KP26 (external : KP26PenalizedReduction)
    {γ a b : ℝ} (hγ : 0 < γ) (hpair : IsBalancedPenalizedMinimizer γ a b) :
    ∀ U : Graphon,
      cost (balancedGraphon a b hpair.1 hpair.2.1) +
        γ * triangle (balancedGraphon a b hpair.1 hpair.2.1) ≤
      cost U + γ * triangle U := by
  intro U
  simpa [balancedPenalty] using external γ hγ a b hpair U

/-- A supporting positive penalty gives the constrained lower bound at its
own triangle density. This is the transfer argument used in `prop:smalldata`;
identifying which r admit such a pair remains the paper's scalar analysis. -/
theorem constrained_lower_bound_of_KP26 (external : KP26PenalizedReduction)
    {γ r a b : ℝ} (hγ : 0 < γ) (hpair : IsBalancedPenalizedMinimizer γ a b)
    (ht : balancedTriangle a b = r^3) {U : Graphon} (hU : Feasible r U) :
    balancedCost a b ≤ cost U := by
  have hp := external γ hγ a b hpair U
  have hm := mul_le_mul_of_nonneg_left hU (le_of_lt hγ)
  unfold balancedPenalty at hp
  rw [ht] at hp
  linarith

theorem constrained_minimizer_of_KP26 (external : KP26PenalizedReduction)
    {γ r a b : ℝ} (hγ : 0 < γ) (hpair : IsBalancedPenalizedMinimizer γ a b)
    (ht : balancedTriangle a b = r^3) :
    IsMinimizer r (balancedGraphon a b hpair.1 hpair.2.1) := by
  refine ⟨?_, ?_⟩
  · simp [Feasible, ht]
  · intro U hU
    rw [cost_balancedGraphon]
    exact constrained_lower_bound_of_KP26 external hγ hpair ht hU

theorem value_eq_of_KP26 (external : KP26PenalizedReduction)
    {γ r a b : ℝ} (hγ : 0 < γ) (hpair : IsBalancedPenalizedMinimizer γ a b)
    (ht : balancedTriangle a b = r^3) : value r = balancedCost a b := by
  have h := (isMinimizer_iff.mp (constrained_minimizer_of_KP26 external hγ hpair ht)).2
  simpa using h.symm

/-- Every constrained minimizer at a supported target also minimizes the
penalized objective, and its triangle constraint is active. No general
Euler--Lagrange or active-constraint theorem is assumed in this implication. -/
theorem any_minimizer_penalized_of_KP26 (external : KP26PenalizedReduction)
    {γ r a b : ℝ} (hγ : 0 < γ) (hpair : IsBalancedPenalizedMinimizer γ a b)
    (ht : balancedTriangle a b = r^3) {U : Graphon} (hU : IsMinimizer r U) :
    triangle U = r^3 ∧
      ∀ W : Graphon, cost U + γ * triangle U ≤ cost W + γ * triangle W := by
  have hc : cost U = balancedCost a b := by
    rw [(isMinimizer_iff.mp hU).2, value_eq_of_KP26 external hγ hpair ht]
  have hp := external γ hγ a b hpair U
  unfold balancedPenalty at hp
  rw [ht, hc] at hp
  have hactive : triangle U = r^3 := by
    apply le_antisymm hU.1
    nlinarith
  refine ⟨hactive, ?_⟩
  intro W
  have hw := external γ hγ a b hpair W
  simpa [balancedPenalty, ht, hc, hactive] using hw

end SparseLowerTail.Section07

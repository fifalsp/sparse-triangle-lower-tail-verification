import SparseLowerTail.Foundations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Scalar entropy geometry for the balanced problem

Stable manuscript anchors: `s4:eq:cube`, `cor:Vbal`, and `lem:ray`.
This file proves the entropy and polynomial steps in the proof of `cor:Vbal`;
it does not assume the classification conclusion or its numerical certificates.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section04

/-- The entropy is strictly convex, including at the endpoint zero. -/
theorem strictConvexOn_entropy : StrictConvexOn ℝ (Ici 0) entropy := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy u v hu hv huv
  have h := Real.strictConvexOn_mul_log.2 hx hy hxy hu hv huv
  simp only [smul_eq_mul] at h ⊢
  unfold entropy
  nlinarith

/-- The usual derivative formula is only asserted away from zero. -/
theorem hasDerivAt_entropy {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt entropy (Real.log x) x := by
  convert ((Real.hasDerivAt_mul_log hx).sub (hasDerivAt_id x)).add_const 1 using 1
  simp

/-- Strict decrease holds on the closed unit interval. -/
theorem strictAntiOn_entropy : StrictAntiOn entropy (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) continuous_entropy.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(hasDerivAt_entropy (ne_of_gt hx.1)).deriv]
  exact Real.log_neg hx.1 hx.2

/-- Stable manuscript anchor `s4:eq:cube`. -/
theorem mean_cube_sub_balancedTriangle (a b : ℝ) :
    ((a + b) / 2) ^ 3 - balancedTriangle a b = (b - a) ^ 3 / 8 := by
  unfold balancedTriangle
  ring

/-- Jensen's inequality in the normalization used by the balanced SBM. -/
theorem entropy_mean_le_balancedCost {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    entropy ((a + b) / 2) ≤ balancedCost a b := by
  have h := strictConvexOn_entropy.convexOn.2 ha hb
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simpa only [smul_eq_mul, balancedCost, show (1 / 2 : ℝ) * a + 1 / 2 * b =
      (a + b) / 2 by ring,
    show (1 / 2 : ℝ) * entropy a + 1 / 2 * entropy b =
      (entropy a + entropy b) / 2 by ring] using h

/-- Strict Jensen inequality, including when one entry vanishes. -/
theorem entropy_mean_lt_balancedCost {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) : entropy ((a + b) / 2) < balancedCost a b := by
  have h := strictConvexOn_entropy.2 ha hb hab
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simpa only [smul_eq_mul, balancedCost, show (1 / 2 : ℝ) * a + 1 / 2 * b =
      (a + b) / 2 by ring,
    show (1 / 2 : ℝ) * entropy a + 1 / 2 * entropy b =
      (entropy a + entropy b) / 2 by ring] using h

/-- The `a ≥ b` part of the feasible region lies below the target in mean. -/
theorem mean_le_target {r a b : ℝ} (hr : 0 ≤ r) (hf : BalancedFeasible r a b)
    (hab : b ≤ a) : (a + b) / 2 ≤ r := by
  have hid := mean_cube_sub_balancedTriangle a b
  have hn : (b - a) ^ 3 ≤ 0 := (show Odd (3 : ℕ) by decide).pow_nonpos_iff.mpr (by linarith)
  have hc : ((a + b) / 2) ^ 3 ≤ r ^ 3 := by linarith [hf.2.2]
  exact (pow_le_pow_iff_left₀ (by linarith [hf.1.1, hf.2.1.1]) hr (by decide : 3 ≠ 0)).mp hc

/-- First case in the proof of `cor:Vbal`: a feasible pair with `a ≥ b`
cannot improve upon the constant graphon. -/
theorem entropy_target_le_balancedCost {r a b : ℝ} (hr : r ∈ Icc 0 1)
    (hf : BalancedFeasible r a b) (hab : b ≤ a) : entropy r ≤ balancedCost a b := by
  have hm : (a + b) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hf.1.1, hf.1.2, hf.2.1.1, hf.2.1.2]
  exact (strictAntiOn_entropy.antitoneOn hm hr (mean_le_target hr.1 hf hab)).trans
    (entropy_mean_le_balancedCost hf.1.1 hf.2.1.1)

/-- Equality in the preceding bound forces the diagonal pair `(r,r)`. -/
theorem balancedCost_eq_entropy_iff {r a b : ℝ} (hr : r ∈ Icc 0 1)
    (hf : BalancedFeasible r a b) (hab : b ≤ a) :
    balancedCost a b = entropy r ↔ a = r ∧ b = r := by
  constructor
  · intro heq
    have hm : (a + b) / 2 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hf.1.1, hf.1.2, hf.2.1.1, hf.2.1.2]
    have hl := strictAntiOn_entropy.antitoneOn hm hr (mean_le_target hr.1 hf hab)
    have he : a = b := by
      by_contra hne
      have hs := entropy_mean_lt_balancedCost hf.1.1 hf.2.1.1 hne
      linarith
    subst b
    have har : a = r := by
      apply strictAntiOn_entropy.injOn hf.1 hr
      simpa using heq
    exact ⟨har, har⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- Every other feasible pair in the `a ≥ b` region has strictly larger cost. -/
theorem entropy_target_lt_balancedCost {r a b : ℝ} (hr : r ∈ Icc 0 1)
    (hf : BalancedFeasible r a b) (hab : b ≤ a) (hne : ¬ (a = r ∧ b = r)) :
    entropy r < balancedCost a b := by
  refine lt_of_le_of_ne (entropy_target_le_balancedCost hr hf hab) ?_
  intro heq
  exact hne ((balancedCost_eq_entropy_iff hr hf hab).mp heq.symm)

/-- Scaling entropy, with the zero endpoint handled explicitly (`lem:ray`). -/
theorem entropy_mul {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    entropy (c * x) = c * entropy x + c * x * Real.log c + 1 - c := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    simp
  · rw [entropy, Real.log_mul (ne_of_gt hc) (ne_of_gt hpos), entropy]
    ring

/-- Balanced cost version of the scalar entropy scaling identity. -/
theorem balancedCost_scale {c a b : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    balancedCost (c * a) (c * b) =
      c * balancedCost a b + c * ((a + b) / 2) * Real.log c + 1 - c := by
  unfold balancedCost
  rw [entropy_mul hc ha, entropy_mul hc hb]
  ring

/-- Triangle density is cubic under scalar multiplication. -/
theorem balancedTriangle_scale (c a b : ℝ) :
    balancedTriangle (c * a) (c * b) = c ^ 3 * balancedTriangle a b := by
  unfold balancedTriangle
  ring

/-- Interpolation from an entry to one, used to saturate the triangle constraint. -/
def towardOne (s x : ℝ) : ℝ := (1 - s) * x + s

theorem towardOne_mem {s x : ℝ} (hs : s ∈ Icc 0 1) (hx : x ∈ Icc 0 1) :
    towardOne s x ∈ Icc (0 : ℝ) 1 := by
  unfold towardOne
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) hx.1) hs.1
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hx.2)]

theorem le_towardOne {s x : ℝ} (hs : 0 ≤ s) (hx : x ≤ 1) : x ≤ towardOne s x := by
  unfold towardOne
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hx)]

theorem towardOne_lt_towardOne {s a b : ℝ} (hs : s < 1) (hab : a < b) :
    towardOne s a < towardOne s b := by
  unfold towardOne
  nlinarith [mul_pos (sub_pos.mpr hs) (sub_pos.mpr hab)]

/-- Increasing the entries toward one weakly decreases entropy cost. -/
theorem balancedCost_towardOne_le {s a b : ℝ} (hs : s ∈ Icc 0 1)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    balancedCost (towardOne s a) (towardOne s b) ≤ balancedCost a b := by
  have h₁ := strictAntiOn_entropy.antitoneOn ha (towardOne_mem hs ha)
    (le_towardOne hs.1 ha.2)
  have h₂ := strictAntiOn_entropy.antitoneOn hb (towardOne_mem hs hb)
    (le_towardOne hs.1 hb.2)
  unfold balancedCost
  linarith

/-- For an ordered nonconstant pair, moving a positive distance strictly decreases cost. -/
theorem balancedCost_towardOne_lt {s a b : ℝ} (hs : s ∈ Ioc 0 1)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : a < b) :
    balancedCost (towardOne s a) (towardOne s b) < balancedCost a b := by
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  have hinc : a < towardOne s a := by
    unfold towardOne
    have hap : a < 1 := hab.trans_le hb.2
    nlinarith [mul_pos hs.1 (sub_pos.mpr hap)]
  have h₁ := strictAntiOn_entropy ha (towardOne_mem hs' ha) hinc
  have h₂ := strictAntiOn_entropy.antitoneOn hb (towardOne_mem hs' hb)
    (le_towardOne hs.1.le hb.2)
  unfold balancedCost
  linarith

/-- Intermediate-value step in `cor:Vbal`. Any feasible ordered pair reaches the
constraint before interpolation reaches one. No minimizer existence is assumed. -/
theorem exists_saturating_parameter {r a b : ℝ} (hr : r ∈ Ioo 0 1)
    (hf : BalancedFeasible r a b) :
    ∃ s ∈ Ico (0 : ℝ) 1,
      balancedTriangle (towardOne s a) (towardOne s b) = r ^ 3 := by
  let f : ℝ → ℝ := fun s => balancedTriangle (towardOne s a) (towardOne s b)
  have hcont : Continuous f := by
    unfold f balancedTriangle towardOne
    fun_prop
  have hzero : f 0 = balancedTriangle a b := by simp [f, towardOne]
  have hone : f 1 = 1 := by simp [f, towardOne]
  have hr3 : r ^ 3 < 1 := by
    exact pow_lt_one₀ hr.1.le hr.2 (by decide : 3 ≠ 0)
  have ht : r ^ 3 ∈ Icc (f 0) (f 1) := by
    rw [hzero, hone]
    exact ⟨hf.2.2, hr3.le⟩
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hcont.continuousOn ht
  refine ⟨s, ⟨hs.1, ?_⟩, heq⟩
  have hne : s ≠ 1 := by
    intro h
    subst s
    rw [hone] at heq
    linarith
  exact lt_of_le_of_ne hs.2 hne

/-- Second case in the proof of `cor:Vbal`: replace an ordered feasible pair
by a saturated ordered pair of no larger cost, with precise equality rigidity. -/
theorem exists_saturated_pair {r a b : ℝ} (hr : r ∈ Ioo 0 1)
    (hf : BalancedFeasible r a b) (hab : a < b) :
    ∃ a' b', BalancedFeasible r a' b' ∧ a' < b' ∧
      balancedTriangle a' b' = r ^ 3 ∧ balancedCost a' b' ≤ balancedCost a b ∧
      (balancedCost a' b' = balancedCost a b ↔ a' = a ∧ b' = b) := by
  obtain ⟨s, hs, heq⟩ := exists_saturating_parameter hr hf
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
  refine ⟨towardOne s a, towardOne s b,
    ⟨towardOne_mem hs' hf.1, towardOne_mem hs' hf.2.1, heq.le⟩,
    towardOne_lt_towardOne hs.2 hab, heq,
    balancedCost_towardOne_le hs' hf.1 hf.2.1, ?_⟩
  constructor
  · intro he
    have hs0 : s = 0 := by
      by_contra hn
      have hp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hn)
      have hlt := balancedCost_towardOne_lt ⟨hp, hs.2.le⟩ hf.1 hf.2.1 hab
      linarith
    simp [hs0, towardOne]
  · rintro ⟨ha, hb⟩
    rw [ha, hb]

/-- The geometric reduction used by `cor:Vbal`, stated directly for all minimizing
pairs: every minimizer is diagonal or ordered and saturates the constraint. -/
theorem balancedMinimizer_diagonal_or_saturated {r a b : ℝ} (hr : r ∈ Ioo 0 1)
    (hmin : IsBalancedMinimizer r a b) :
    (a = r ∧ b = r) ∨ (a < b ∧ balancedTriangle a b = r ^ 3) := by
  rcases le_or_gt b a with hab | hab
  · left
    have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    apply (balancedCost_eq_entropy_iff hr' hmin.1 hab).mp
    apply le_antisymm
    · simpa using hmin.2 r r (balanced_diagonal_feasible hr')
    · exact entropy_target_le_balancedCost hr' hmin.1 hab
  · right
    obtain ⟨a', b', hf', hab', ht', hc', heq⟩ := exists_saturated_pair hr hmin.1 hab
    have he : balancedCost a' b' = balancedCost a b :=
      le_antisymm hc' (hmin.2 a' b' hf')
    obtain ⟨rfl, rfl⟩ := heq.mp he
    exact ⟨hab, ht'⟩

end SparseLowerTail.Section04

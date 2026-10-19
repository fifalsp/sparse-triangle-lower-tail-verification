import SparseLowerTail.Triangle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The balanced SBM as an actual graphon, with its Lebesgue integral formulas. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail

/-- Kernel values of the symmetric two-block model on a measurable partition. -/
def blockValue (P : Set ℝ) (a b : ℝ) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if p.1 ∈ P then (if p.2 ∈ P then a else b)
    else (if p.2 ∈ P then b else a)

private theorem blockValue_measurable {P : Set ℝ} (hP : MeasurableSet P) (a b : ℝ) :
    Measurable (blockValue P a b) := by
  classical
  exact ((measurable_const.ite (hP.preimage measurable_snd) measurable_const).ite
    (hP.preimage measurable_fst)
    (measurable_const.ite (hP.preimage measurable_snd) measurable_const))

/-- Equal within-block values; P need not yet have mass one half. -/
def twoBlock (P : Set ℝ) (hP : MeasurableSet P) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) : Graphon where
  toFun := blockValue P a b
  measurable := (blockValue_measurable hP a b).aemeasurable
  symmetric := Filter.Eventually.of_forall (fun p => by
    classical
    simp only [blockValue, Prod.fst_swap, Prod.snd_swap]
    split_ifs <;> rfl)
  bounded := Filter.Eventually.of_forall (fun p => by
    classical
    simp only [blockValue]
    split_ifs <;> assumption)

/-- Integration of a two-valued function over a partition of probability one half. -/
theorem integral_half_partition {P : Set ℝ} [DecidablePred (· ∈ P)] (hP : MeasurableSet P)
    (hm : unitMeasure P = (1 / 2 : ENNReal)) (a b : ℝ) :
    (∫ x, (if x ∈ P then a else b) ∂unitMeasure) = (a+b)/2 := by
  classical
  have hc : unitMeasure Pᶜ = (1/2 : ENNReal) := by
    rw [measure_compl hP (measure_ne_top _ _), measure_univ, hm]
    norm_num
  have h := integral_piecewise (μ := unitMeasure) (f := fun _ => a)
    (g := fun _ => b) hP (integrable_const a).integrableOn
      (integrable_const b).integrableOn
  calc
    _ = (1/2 : ℝ)*a + (1/2 : ℝ)*b := by
      simpa [Set.piecewise, Measure.real, hm, hc, smul_eq_mul] using h
    _ = (a+b)/2 := by ring

theorem cost_twoBlock {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P = (1 / 2 : ENNReal)) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    cost (twoBlock P hP a b ha hb) = balancedCost a b := by
  classical
  rw [cost, integral_prod _ (cost_integrable _)]
  change (∫ x, ∫ y, entropy (blockValue P a b (x,y)) ∂unitMeasure ∂unitMeasure) = _
  have hi (x : ℝ) :
      (∫ y, entropy (blockValue P a b (x,y)) ∂unitMeasure) = balancedCost a b := by
    by_cases hx : x ∈ P
    · simp only [blockValue, hx, if_true, apply_ite entropy]
      exact integral_half_partition hP hm (entropy a) (entropy b)
    · simp only [blockValue, hx, if_false, apply_ite entropy]
      rw [integral_half_partition hP hm]
      simp [balancedCost, add_comm]
  simp_rw [hi]
  simp

theorem triangle_twoBlock {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P = (1 / 2 : ENNReal)) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    triangle (twoBlock P hP a b ha hb) = balancedTriangle a b := by
  classical
  let B := twoBlock P hP a b ha hb
  have hf := triangle_integrable B
  have iterated : triangle B = ∫ x, ∫ y, ∫ z,
      blockValue P a b (x,y) * blockValue P a b (y,z) * blockValue P a b (x,z)
        ∂unitMeasure ∂unitMeasure ∂unitMeasure := by
    rw [triangle, integral_prod _ hf]
    apply integral_congr_ae
    filter_upwards [hf.prod_right_ae] with x hx
    exact integral_prod _ hx
  rw [show twoBlock P hP a b ha hb = B from rfl, iterated]
  have inner (x y : ℝ) :
      (∫ z, blockValue P a b (x,y) * blockValue P a b (y,z) *
        blockValue P a b (x,z) ∂unitMeasure) =
      if (x ∈ P ↔ y ∈ P) then (a*a*a+a*b*b)/2 else a*b*b := by
    by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
    all_goals
      simp only [blockValue, hx, hy, if_true, if_false]
      simp (config := { contextual := true }) only
        [mul_ite, if_true, if_false, true_iff, false_iff, not_true_eq_false]
    all_goals
      rw [integral_half_partition hP hm] <;> ring
  simp_rw [inner]
  have middle (x : ℝ) :
      (∫ y, (if (x ∈ P ↔ y ∈ P) then (a*a*a+a*b*b)/2 else a*b*b)
        ∂unitMeasure) = balancedTriangle a b := by
    by_cases hx : x ∈ P
    · simp only [hx, true_iff]
      rw [integral_half_partition hP hm]
      unfold balancedTriangle
      ring
    · simp only [hx, false_iff, ite_not]
      rw [integral_half_partition hP hm]
      unfold balancedTriangle
      ring
  simp_rw [middle]
  simp

/-- The standard equal partition; the boundary points are irrelevant a.e. -/
def halfInterval : Set ℝ := Icc 0 (1/2)

theorem halfInterval_measurable : MeasurableSet halfInterval := measurableSet_Icc

theorem halfInterval_subset : halfInterval ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩

theorem halfInterval_mass : unitMeasure halfInterval = (1/2 : ENNReal) := by
  rw [unitMeasure, Measure.restrict_apply halfInterval_measurable,
    inter_eq_left.mpr halfInterval_subset]
  norm_num [halfInterval, Real.volume_Icc, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]

def balancedGraphon (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) : Graphon :=
  twoBlock halfInterval halfInterval_measurable a b ha hb

@[simp] theorem cost_balancedGraphon (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    cost (balancedGraphon a b ha hb) = balancedCost a b :=
  cost_twoBlock halfInterval_measurable halfInterval_mass a b ha hb

@[simp] theorem triangle_balancedGraphon (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    triangle (balancedGraphon a b ha hb) = balancedTriangle a b :=
  triangle_twoBlock halfInterval_measurable halfInterval_mass a b ha hb

theorem balancedGraphon_feasible {r a b : ℝ} (hf : BalancedFeasible r a b) :
    Feasible r (balancedGraphon a b hf.1 hf.2.1) := by
  simpa [Feasible] using hf.2.2

/-- The easy direction of Theorem 1.3(a), proved for the full graphon infimum. -/
theorem value_le_balancedValue {r : ℝ} (hr : r ∈ Icc 0 1) :
    value r ≤ balancedValue r := by
  unfold balancedValue
  refine le_csInf ?_ ?_
  · exact ⟨balancedCost r r, r, r, balanced_diagonal_feasible hr, rfl⟩
  · rintro v ⟨a, b, hf, rfl⟩
    simpa using value_le_cost (balancedGraphon_feasible hf)

/-- The bipartite graphon is an actual feasible witness for every nonnegative
triangle target; no graphon minimizer existence theorem is needed here. -/
theorem value_le_half {r : ℝ} (hr : 0 ≤ r) : value r ≤ 1/2 := by
  have hf : BalancedFeasible r 0 1 := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    simpa using pow_nonneg hr 3
  simpa using value_le_cost (balancedGraphon_feasible hf)

theorem twoBlock_isBalanced {P : Set ℝ} (hP : MeasurableSet P)
    (hsub : P ⊆ Icc (0 : ℝ) 1) (hm : unitMeasure P = (1/2 : ENNReal))
    (a b : ℝ) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    IsBalanced (twoBlock P hP a b ha hb) a b := by
  classical
  refine ⟨P, hP, hsub, hm, Filter.Eventually.of_forall ?_⟩
  intro p
  change blockValue P a b p = (if (p.1 ∈ P ↔ p.2 ∈ P) then a else b)
  by_cases h1 : p.1 ∈ P <;> by_cases h2 : p.2 ∈ P <;> simp [blockValue, h1, h2]

theorem balancedGraphon_isBalanced (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    IsBalanced (balancedGraphon a b ha hb) a b :=
  twoBlock_isBalanced halfInterval_measurable halfInterval_subset halfInterval_mass a b ha hb

/-- Partition forms in the main statement agree a.e. with constructed graphons. -/
theorem IsBalanced.exists_twoBlock {U : Graphon} {a b : ℝ}
    (hU : IsBalanced U a b) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    ∃ (P : Set ℝ) (hP : MeasurableSet P), unitMeasure P = (1/2 : ENNReal) ∧
      U.toFun =ᵐ[squareMeasure] (twoBlock P hP a b ha hb).toFun := by
  classical
  obtain ⟨P, hP, _, hm, heq⟩ := hU
  refine ⟨P, hP, hm, ?_⟩
  filter_upwards [heq] with p hp
  rw [hp]
  change (if (p.1 ∈ P ↔ p.2 ∈ P) then a else b) = blockValue P a b p
  by_cases h1 : p.1 ∈ P <;> by_cases h2 : p.2 ∈ P <;> simp [blockValue, h1, h2]

theorem IsBalanced.cost_eq {U : Graphon} {a b : ℝ}
    (hU : IsBalanced U a b) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    cost U = balancedCost a b := by
  obtain ⟨P, hP, hm, heq⟩ := hU.exists_twoBlock ha hb
  rw [cost_congr_ae heq]
  exact cost_twoBlock hP hm a b ha hb

theorem IsBalanced.triangle_eq {U : Graphon} {a b : ℝ}
    (hU : IsBalanced U a b) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    triangle U = balancedTriangle a b := by
  obtain ⟨P, hP, hm, heq⟩ := hU.exists_twoBlock ha hb
  rw [triangle_congr_ae heq]
  exact triangle_twoBlock hP hm a b ha hb

end SparseLowerTail

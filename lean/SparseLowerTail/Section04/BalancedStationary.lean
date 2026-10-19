import SparseLowerTail.Section04.Codegree
import SparseLowerTail.Section04.Branch

/-!
# Balanced stationary graphons

Stable paper anchors: `lem:branch`, `eq:branch`, and `lem:Bderivative`(a).
This file connects the scalar branch to actual measurable graphons and their
integrals. It does not assert global minimality or the crossing theorem.
-/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail

/-- The two block values inherit the graphon's a.e. bounds because both kinds
of blocks have positive measure. -/
theorem IsBalanced.values_mem_Icc {U : Graphon} {a b : ℝ}
    (hU : IsBalanced U a b) : a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 := by
  classical
  obtain ⟨P, hP, _, hm, heq⟩ := hU
  have hbounds : ∀ᵐ p ∂squareMeasure,
      (if (p.1 ∈ P ↔ p.2 ∈ P) then a else b) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [heq, U.bounded] with p hp hbp
    rw [← hp]
    exact hbp
  have hn : unitMeasure P ≠ 0 := by rw [hm]; norm_num
  have hc : unitMeasure Pᶜ = (1/2 : ENNReal) := by
    rw [measure_compl hP (measure_ne_top _ _), measure_univ, hm]
    norm_num
  have hcn : unitMeasure Pᶜ ≠ 0 := by rw [hc]; norm_num
  obtain ⟨x, hx, hex⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hbounds))
  obtain ⟨y, hy, hey⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn
    (ae_restrict_of_ae hex)
  obtain ⟨z, hz, hez⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcn
    (ae_restrict_of_ae hex)
  have hznot : z ∉ P := hz
  exact ⟨by simpa [hx, hy] using hey, by simpa [hx, hznot] using hez⟩

/-- Edge density under the same Lebesgue probability convention as `triangle`. -/
def edgeDensity (U : Graphon) : ℝ := ∫ p, U p ∂squareMeasure

theorem graphon_integrable (U : Graphon) : Integrable U.toFun squareMeasure := by
  apply Integrable.of_bound U.measurable.aestronglyMeasurable 1
  filter_upwards [U.bounded] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
  exact hp.2

theorem edgeDensity_congr_ae {U W : Graphon}
    (heq : U.toFun =ᵐ[squareMeasure] W.toFun) : edgeDensity U = edgeDensity W :=
  integral_congr_ae heq

/-- `eq:Bdens`, edge-density part, for arbitrary measurable balanced blocks. -/
theorem edgeDensity_twoBlock {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P = (1/2 : ENNReal)) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    edgeDensity (twoBlock P hP a b ha hb) = (a+b)/2 := by
  classical
  rw [edgeDensity, integral_prod _ (graphon_integrable _)]
  change (∫ x, ∫ y, blockValue P a b (x,y) ∂unitMeasure ∂unitMeasure) = _
  have hi (x : ℝ) : (∫ y, blockValue P a b (x,y) ∂unitMeasure) = (a+b)/2 := by
    by_cases hx : x ∈ P
    · simp only [blockValue, hx, if_true]
      exact integral_half_partition hP hm a b
    · simp only [blockValue, hx, if_false]
      rw [integral_half_partition hP hm]
      ring
  simp_rw [hi]
  simp

theorem IsBalanced.edgeDensity_eq {U : Graphon} {a b : ℝ}
    (hU : IsBalanced U a b) : edgeDensity U = (a+b)/2 := by
  obtain ⟨ha, hb⟩ := hU.values_mem_Icc
  obtain ⟨P, hP, hm, heq⟩ := hU.exists_twoBlock ha hb
  rw [edgeDensity_congr_ae heq]
  exact edgeDensity_twoBlock hP hm a b ha hb

namespace Section04

/-- The actual graphon belonging to the stationary scalar branch. -/
def branchGraphon (z : ℝ) (hz : 0 < z) (hz1 : z < 1) : Graphon :=
  balancedGraphon (branchA z) (branchB z)
    ⟨(branchA_pos hz).le, ((branchA_lt_branchB hz1).trans (branchB_lt_one hz hz1)).le⟩
    ⟨(branchB_pos z).le, (branchB_lt_one hz hz1).le⟩

theorem branchGraphon_isBalanced {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    IsBalanced (branchGraphon z hz hz1) (branchA z) (branchB z) :=
  balancedGraphon_isBalanced _ _ _ _

/-- `lem:branch`(a) on graphons: the branch satisfies the a.e. EL equation. -/
theorem branchGraphon_ae_log_equation {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∀ᵐ p ∂squareMeasure, Real.log (branchGraphon z hz hz1 p) =
      -branchMu z * codegree (branchGraphon z hz hz1) p.1 p.2 := by
  have hU := branchGraphon_isBalanced hz hz1
  obtain ⟨ha, hb⟩ := hU.values_mem_Icc
  apply (hU.ae_log_equation_iff ha hb (branchA_pos hz) (branchB_pos z) (branchMu z)).mpr
  simpa only [BalancedEL, mul_div_assoc] using branch_balancedEL hz hz1

/-- `lem:branch`(b) for actual graphons. Positive nonconstant balanced stationary
representatives with triangle density below one have exactly the stated branch
parameters. The bounds on a and b are consequences, not additional assumptions. -/
theorem balancedGraphon_parametrization {U : Graphon} {a b μ : ℝ}
    (hU : IsBalanced U a b) (ha_pos : 0 < a) (hb_pos : 0 < b) (hne : a ≠ b)
    (ht : triangle U < 1)
    (hel : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ * codegree U p.1 p.2) :
    a < b ∧ 0 < a/b ∧ a/b < 1 ∧
      a = branchA (a/b) ∧ b = branchB (a/b) ∧ μ = branchMu (a/b) := by
  obtain ⟨ha, hb⟩ := hU.values_mem_Icc
  have hs : BalancedEL a b μ := by
    have hh := (hU.ae_log_equation_iff ha hb ha_pos hb_pos μ).mp hel
    simpa only [BalancedEL, mul_div_assoc] using hh
  apply balancedEL_parametrization ha_pos hb_pos hne _ hs
  rwa [← hU.triangle_eq ha hb]

/-- `lem:Bderivative`(a), the multiplier identity using only the two EL equations. -/
theorem balancedEL_multiplier_triangle {a b μ : ℝ} (hel : BalancedEL a b μ) :
    μ * balancedTriangle a b = -(a * Real.log a + b * Real.log b)/2 := by
  rw [hel.1, hel.2]
  unfold balancedTriangle
  ring

/-- The entropy identity used in `lem:Bderivative`(a). This algebraic identity
also respects the continuous entropy convention at zero. -/
theorem balanced_log_entropy_identity (a b : ℝ) :
    -(a * Real.log a + b * Real.log b)/2 = 1 - balancedCost a b - (a+b)/2 := by
  unfold balancedCost entropy
  ring

theorem balancedEL_multiplier_cost {a b μ : ℝ} (hel : BalancedEL a b μ) :
    μ * balancedTriangle a b = 1 - balancedCost a b - (a+b)/2 :=
  (balancedEL_multiplier_triangle hel).trans (balanced_log_entropy_identity a b)

/-- The multiplier identity for any balanced stationary graphon. -/
theorem balancedGraphon_multiplier_identity {U : Graphon} {a b μ : ℝ}
    (hU : IsBalanced U a b) (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hel : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ * codegree U p.1 p.2) :
    μ * triangle U = 1 - cost U - edgeDensity U := by
  obtain ⟨ha, hb⟩ := hU.values_mem_Icc
  have hs : BalancedEL a b μ := by
    have hh := (hU.ae_log_equation_iff ha hb ha_pos hb_pos μ).mp hel
    simpa only [BalancedEL, mul_div_assoc] using hh
  rw [hU.triangle_eq ha hb, hU.cost_eq ha hb, hU.edgeDensity_eq]
  exact balancedEL_multiplier_cost hs

/-- `lem:Bderivative`(a) for the graphon parametrized by z. -/
theorem branchGraphon_multiplier_identity {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    branchMu z * triangle (branchGraphon z hz hz1) =
      1 - cost (branchGraphon z hz hz1) - edgeDensity (branchGraphon z hz hz1) :=
  balancedGraphon_multiplier_identity (branchGraphon_isBalanced hz hz1)
    (branchA_pos hz) (branchB_pos z) (branchGraphon_ae_log_equation hz hz1)

end Section04
end SparseLowerTail

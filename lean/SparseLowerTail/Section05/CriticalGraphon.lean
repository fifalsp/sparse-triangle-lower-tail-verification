import SparseLowerTail.Section05.CriticalRegion
import SparseLowerTail.Section04.BalancedStationary
import SparseLowerTail.Section04.BipodalAlgebra

/-! All pointwise and integral properties of the canonical critical balanced graphon. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section05
open Section04

/-- The canonical critical graphon B_*. -/
def criticalGraphon : Graphon := balancedGraphon criticalA criticalB critical_pair_bounds.1 critical_pair_bounds.2
/-- The multiplier belonging to its exact branch parameter. -/
def criticalMu : ℝ := branchMu transitionParameter

theorem critical_strict_bounds : 0<criticalA ∧ criticalA<threshold ∧ threshold<criticalB ∧ criticalB<1 := by
  have hz : transitionParameter∈Ioo (0:ℝ) 1 :=
    ⟨transitionParameter_mem_Ioo.1,transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2⟩
  exact branch_pair_target_bounds hz (branchRho_transitionParameter.trans threshold_eq_transitionTarget.symm)

theorem criticalMu_pos : 0<criticalMu :=
  branchMu_pos transitionParameter_mem_Ioo.1 (transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2)

theorem criticalGraphon_integrals : triangle criticalGraphon=criticalTriangle ∧ cost criticalGraphon=criticalCost ∧
    edgeDensity criticalGraphon=criticalMean := by
  refine ⟨?_,?_,?_⟩
  · exact (triangle_balancedGraphon _ _ _ _).trans critical_pair_triangle
  · exact (cost_balancedGraphon _ _ _ _).trans critical_pair_cost
  · exact (balancedGraphon_isBalanced _ _ _ _).edgeDensity_eq

theorem criticalGraphon_mean_gt_threshold : threshold<criticalMean := by
  have hb := critical_strict_bounds
  have he := mean_cube_sub_balancedTriangle criticalA criticalB
  rw [critical_pair_triangle] at he
  have hp : 0<(criticalB-criticalA)^3 := pow_pos (sub_pos.mpr (hb.2.1.trans hb.2.2.1)) 3
  apply (show Odd (3:ℕ) by decide).strictMono_pow.lt_iff_lt.mp
  change threshold^3<((criticalA+criticalB)/2)^3
  nlinarith

theorem critical_balancedEL : BalancedEL criticalA criticalB criticalMu :=
  branch_balancedEL transitionParameter_mem_Ioo.1 (transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2)

/-- The critical logarithmic Euler equation holds at every point of the canonical graphon. -/
theorem criticalGraphon_log_equation (x y : ℝ) :
    Real.log (criticalGraphon (x,y))=-criticalMu*codegree criticalGraphon x y := by
  apply twoBlock_log_equation_of_scalar halfInterval_measurable halfInterval_mass criticalA criticalB criticalMu
    critical_pair_bounds.1 critical_pair_bounds.2
  simpa only [BalancedEL,mul_div_assoc] using critical_balancedEL

/-- The scalar multiplier identity at the critical point. -/
theorem critical_multiplier_identity : criticalMu*criticalTriangle=1-criticalCost-criticalMean := by
  have hh := balancedEL_multiplier_cost critical_balancedEL
  rw [critical_pair_triangle,critical_pair_cost] at hh
  exact hh

/-- Every row has the same exact k-integral, pointwise rather than only almost everywhere. -/
theorem criticalGraphon_row_vertexEntropy (x : ℝ) :
    (∫ y, vertexEntropy (criticalGraphon (x,y)) ∂unitMeasure)=
      2*criticalCost+criticalMu*criticalTriangle ∧
    (∫ y, vertexEntropy (criticalGraphon (x,y)) ∂unitMeasure)=1+criticalCost-criticalMean := by
  classical
  have hi : (∫ y, vertexEntropy (criticalGraphon (x,y)) ∂unitMeasure)=
      (vertexEntropy criticalA+vertexEntropy criticalB)/2 := by
    change (∫ y, vertexEntropy (blockValue halfInterval criticalA criticalB (x,y)) ∂unitMeasure)=_
    by_cases hx : x∈halfInterval
    · simp only [blockValue,hx,if_true,apply_ite vertexEntropy]
      exact integral_half_partition halfInterval_measurable halfInterval_mass _ _
    · simp only [blockValue,hx,if_false,apply_ite vertexEntropy]
      rw [integral_half_partition halfInterval_measurable halfInterval_mass]
      ring
  have he := balancedEL_multiplier_triangle critical_balancedEL
  rw [critical_pair_triangle] at he
  have hc := critical_pair_cost
  have hfirst : (vertexEntropy criticalA+vertexEntropy criticalB)/2=2*criticalCost+criticalMu*criticalTriangle := by
    dsimp only [criticalTriangle,criticalCost,vertexEntropy,balancedCost,entropy] at he hc ⊢
    linarith
  exact ⟨hi.trans hfirst,(hi.trans hfirst).trans (by linarith [critical_multiplier_identity])⟩

/-- The complete content of `cor:Bstar` for the actual critical representative. -/
theorem critical_graphon_properties :
    (0<criticalA ∧ criticalA<threshold ∧ threshold<criticalB ∧ criticalB<1 ∧
      0<criticalMu ∧ triangle criticalGraphon=criticalTriangle ∧ cost criticalGraphon=criticalCost ∧ threshold<criticalMean) ∧
    (BalancedEL criticalA criticalB criticalMu ∧ ∀ x y : ℝ,
      Real.log (criticalGraphon (x,y))=-criticalMu*codegree criticalGraphon x y) ∧
    (criticalMu*criticalTriangle=1-criticalCost-criticalMean ∧ ∀ x : ℝ,
      (∫ y, vertexEntropy (criticalGraphon (x,y)) ∂unitMeasure)=2*criticalCost+criticalMu*criticalTriangle ∧
      (∫ y, vertexEntropy (criticalGraphon (x,y)) ∂unitMeasure)=1+criticalCost-criticalMean) := by
  have hb := critical_strict_bounds
  exact ⟨⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,criticalMu_pos,criticalGraphon_integrals.1,
    criticalGraphon_integrals.2.1,criticalGraphon_mean_gt_threshold⟩,
    ⟨critical_balancedEL,criticalGraphon_log_equation⟩,⟨critical_multiplier_identity,criticalGraphon_row_vertexEntropy⟩⟩

end SparseLowerTail.Section05

import SparseLowerTail.MainStatement
import SparseLowerTail.Section06.Stability
import SparseLowerTail.Section04.ThresholdDigits

/-! Final theorem assembly. The internal critical and subcritical classification
obligations are explicit hypotheses, never axioms or an assumed main theorem. -/
noncomputable section
open Set
namespace SparseLowerTail
open Section02 Section04 Section05 Section06

/-- A fully classified branch supplies equality of the actual graphon and scalar values. -/
theorem value_eq_balancedValue_of_branchClassification {r : ℝ}
    (hr : r∈Ioo (0:ℝ) threshold) (h : BranchClassification r) :
    value r=balancedValue r := by
  have hrs : r∈Ioo (0:ℝ) spinodalValue := ⟨hr.1,by
    rw [threshold_eq_transitionTarget] at hr
    exact hr.2.trans transitionTarget_spec.1.2⟩
  have hz := leftBranch_mem_unit hrs
  let B := branchGraphon (leftBranch r) hz.1 hz.2
  have hB : IsBalanced B (branchA (leftBranch r)) (branchB (leftBranch r)) :=
    branchGraphon_isBalanced hz.1 hz.2
  have hmin := (h B).mpr hB
  exact (hB.minimizer_bridge ⟨hr.1.le,(hr.2.trans threshold_mem_Ioo.2).le⟩ hmin).2

/-- The full existing MainTheorem proposition follows from precisely the two
remaining global classification statements. This is a conditional theorem. -/
theorem mainTheorem_of_classifications (hcrit : CriticalClassification)
    (hsub : ∀ r∈Ioo (0:ℝ) threshold,BranchClassification r) : MainTheorem := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hh := threshold_digits
    norm_num [Numerics.Bounds] at hh ⊢
    exact hh
  · intro r hr
    rcases lt_trichotomy r threshold with hlt | rfl | hgt
    · exact value_eq_balancedValue_of_branchClassification ⟨hr.1,hlt⟩ (hsub r ⟨hr.1,hlt⟩)
    · rw [hcrit.1,threshold_eq_transitionTarget,balancedValue_at_transition]
    · rw [value_eq_entropy_above hcrit ⟨hgt,hr.2⟩]
      rw [threshold_eq_transitionTarget] at hgt
      exact (balancedValue_above_transition ⟨hgt,hr.2⟩).symm
  · exact fun r hr => strict_improvement_iff hcrit hr
  · exact fun r hr U => minimizer_above_iff hcrit hr U
  · have hbounds := branch_pair_target_bounds
      ⟨transitionParameter_mem_Ioo.1,transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2⟩ branchRho_transitionParameter
    rw [← threshold_eq_transitionTarget] at hbounds
    exact ⟨criticalA,criticalB,hbounds.1,hbounds.2.1,hbounds.2.2.1,hbounds.2.2.2,
      critical_pair_minimizer,minimizer_at_iff hcrit⟩
  · intro r hr
    have hrs : r∈Ioo (0:ℝ) spinodalValue := ⟨hr.1,by
      rw [threshold_eq_transitionTarget] at hr
      exact hr.2.trans transitionTarget_spec.1.2⟩
    have hz := leftBranch_mem_unit hrs
    have hbounds := branch_pair_target_bounds hz (branchRho_leftBranch ⟨hr.1.le,hrs.2.le⟩)
    have hrt : r∈Ioo (0:ℝ) transitionTarget := by
      simpa only [threshold_eq_transitionTarget] using hr
    have hmin := (balancedMinimizer_below_transition hrt _ _).mpr ⟨rfl,rfl⟩
    exact ⟨_,_,hbounds.1,hbounds.2.1,hbounds.2.2.1,hbounds.2.2.2,hmin,
      fun c d hcd => (balancedMinimizer_below_transition hrt c d).mp hcd,hsub r hr⟩

end SparseLowerTail

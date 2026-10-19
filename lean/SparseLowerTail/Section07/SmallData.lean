import SparseLowerTail.Section07.PenalizedPhase
import SparseLowerTail.Section07.PenalizedMultiplier
import SparseLowerTail.Section04.BalancedPhase

/-! The supporting-target range and KP26 transfer in `prop:smalldata`.
The range and supporting scalar minimum are proved here. KP26 is the sole
external input to the unrestricted-value conclusions. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04

/-- Scalar counterpart of the penalized-to-constrained transfer. -/
theorem balanced_constrained_of_penalized {γ r a b : ℝ} (hγ : 0<γ)
    (h : IsBalancedPenalizedMinimizer γ a b) (ht : balancedTriangle a b=r^3) :
    IsBalancedMinimizer r a b := by
  refine ⟨⟨h.1,h.2.1,ht.le⟩,?_⟩
  intro c d hcd
  have hh := h.2.2 c d hcd.1 hcd.2.1
  unfold balancedPenalty at hh
  rw [ht] at hh
  have hm := mul_le_mul_of_nonneg_left hcd.2.2 hγ.le
  linarith

/-- `lem:order`: the small-target endpoint is strictly below the balanced
transition. This proof uses the actual tie and constant minimum, with no
numerical digit enclosures. -/
theorem smallTarget_lt_threshold : smallTarget<threshold := by
  have hz := penalizedCrossing_mem_unit
  have hf := branch_pair_feasible hz (rfl : branchRho penalizedCrossing=smallTarget)
  have he := penalizedCrossing_spec.2
  rw [penalizedGap_eq hz.1] at he
  have hstrict := constantPenalty_strict_min criticalPenalty_pos
    ⟨smallTarget_mem_unit.1.le,smallTarget_mem_unit.2.le⟩
    (ne_of_lt smallTarget_lt_largeTarget)
  have hc : balancedCost (branchA penalizedCrossing) (branchB penalizedCrossing)<entropy smallTarget := by
    have ht : balancedTriangle (branchA penalizedCrossing) (branchB penalizedCrossing)=smallTarget^3 :=
      branch_triangle_eq_rho_cube hz.1
    change balancedCost (branchA penalizedCrossing) (branchB penalizedCrossing)+
      criticalPenalty*balancedTriangle (branchA penalizedCrossing) (branchB penalizedCrossing)-
      constantPenalty criticalPenalty (constantRoot criticalPenalty)=0 at he
    rw [ht] at he
    unfold constantPenalty at hstrict he
    linarith
  apply (balanced_strict_improvement_iff_threshold smallTarget_mem_unit).mp
  exact (balancedValue_le_cost hf).trans_lt hc

/-- The critical penalized point lies on the increasing triangle branch.
Its identification follows from constrained scalar uniqueness, avoiding digits. -/
theorem leftBranch_smallTarget : leftBranch smallTarget=penalizedCrossing := by
  have hz := penalizedCrossing_mem_unit
  have hp := branch_penalizedMinimizer
    (show penalizedCrossing∈Ioc (0:ℝ) penalizedCrossing from ⟨hz.1,le_rfl⟩)
  have ht : balancedTriangle (branchA penalizedCrossing) (branchB penalizedCrossing)=smallTarget^3 :=
    branch_triangle_eq_rho_cube hz.1
  have hmin := balanced_constrained_of_penalized criticalPenalty_pos hp ht
  have hr : smallTarget∈Ioo (0:ℝ) transitionTarget := by
    rw [← threshold_eq_transitionTarget]
    exact ⟨smallTarget_mem_unit.1,smallTarget_lt_threshold⟩
  have he := (balancedMinimizer_below_transition hr _ _).mp hmin
  have hratio (z : ℝ) : branchA z/branchB z=z := by
    unfold branchA
    exact mul_div_cancel_right₀ z (ne_of_gt (branchB_pos z))
  have hh := congrArg₂ (fun a b : ℝ => a/b) he.1 he.2
  simpa only [hratio] using hh.symm

theorem penalizedCrossing_lt_spinodal : penalizedCrossing<spinodal := by
  rw [← leftBranch_smallTarget]
  apply leftBranch_lt_spinodal
  refine ⟨smallTarget_mem_unit.1,?_⟩
  have hh := smallTarget_lt_threshold
  rw [threshold_eq_transitionTarget] at hh
  exact hh.trans transitionTarget_spec.1.2

/-- The full supporting range: all targets up to r_- correspond to z≤z_c,
with multiplier at least the critical multiplier. -/
theorem smallTarget_support {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) :
    leftBranch r∈Ioc (0:ℝ) penalizedCrossing ∧
    3*criticalPenalty≤branchMu (leftBranch r) ∧
    IsBalancedPenalizedMinimizer (branchMu (leftBranch r)/3)
      (branchA (leftBranch r)) (branchB (leftBranch r)) ∧
    balancedTriangle (branchA (leftBranch r)) (branchB (leftBranch r))=r^3 := by
  have hsmall : smallTarget<spinodalValue := by
    have hh := smallTarget_lt_threshold
    rw [threshold_eq_transitionTarget] at hh
    exact hh.trans transitionTarget_spec.1.2
  have hrspin : r∈Ioo (0:ℝ) spinodalValue := ⟨hr.1,hr.2.trans_lt hsmall⟩
  have hl := leftBranch_mem_unit hrspin
  have hz : leftBranch r∈Ioc (0:ℝ) penalizedCrossing := by
    refine ⟨hl.1,?_⟩
    rw [← leftBranch_smallTarget]
    exact strictMonoOn_leftBranch.monotoneOn ⟨hr.1.le,hrspin.2.le⟩
      ⟨smallTarget_mem_unit.1.le,hsmall.le⟩ hr.2
  have hμ := strictAntiOn_branchMu_left.antitoneOn
    (show leftBranch r∈Ioc (0:ℝ) foldPoint from ⟨hz.1,hz.2.trans penalizedCrossing_lt_fold.le⟩)
    (show penalizedCrossing∈Ioc (0:ℝ) foldPoint from
      ⟨penalizedCrossing_spec.1.1,penalizedCrossing_lt_fold.le⟩) hz.2
  refine ⟨hz,?_,branch_penalizedMinimizer hz,?_⟩
  · unfold criticalPenalty
    linarith
  · rw [branch_triangle_eq_rho_cube hl.1,branchRho_leftBranch ⟨hr.1.le,hrspin.2.le⟩]

/-- KP26 is sufficient on the whole proved range: V equals the branch cost,
and every constrained optimizer is also a global penalized optimizer. -/
theorem smallTarget_data (external : KP26PenalizedReduction) {r : ℝ}
    (hr : r∈Ioc (0:ℝ) smallTarget) :
    value r=branchCost (leftBranch r) ∧
    ∀ U : Graphon, IsMinimizer r U →
      triangle U=r^3 ∧ cost U=branchCost (leftBranch r) ∧
      ∀ W : Graphon, cost U+(branchMu (leftBranch r)/3)*triangle U ≤
        cost W+(branchMu (leftBranch r)/3)*triangle W := by
  obtain ⟨hz,hμ,hpair,ht⟩ := smallTarget_support hr
  have hz01 : leftBranch r∈Ioo (0:ℝ) 1 :=
    ⟨hz.1,hz.2.trans_lt penalizedCrossing_mem_unit.2⟩
  have hγ := div_pos (branchMu_pos hz01.1 hz01.2) (by norm_num : (0:ℝ)<3)
  have hv := value_eq_of_KP26 external hγ hpair ht
  refine ⟨hv,?_⟩
  intro U hU
  have hh := any_minimizer_penalized_of_KP26 external hγ hpair ht hU
  exact ⟨hh.1,(isMinimizer_iff.mp hU).2.trans hv,hh.2⟩

/-- Concrete attainment on the entire small-target range. -/
theorem smallTarget_branch_minimizer (external : KP26PenalizedReduction) {r : ℝ}
    (hr : r∈Ioc (0:ℝ) smallTarget) :
    ∃ U : Graphon, IsMinimizer r U ∧
      IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) := by
  obtain ⟨hz,_,hpair,ht⟩ := smallTarget_support hr
  have hz01 : leftBranch r∈Ioo (0:ℝ) 1 :=
    ⟨hz.1,hz.2.trans_lt penalizedCrossing_mem_unit.2⟩
  have hγ := div_pos (branchMu_pos hz01.1 hz01.2) (by norm_num : (0:ℝ)<3)
  exact ⟨balancedGraphon _ _ hpair.1 hpair.2.1,
    constrained_minimizer_of_KP26 external hγ hpair ht,
    balancedGraphon_isBalanced _ _ _ _⟩

theorem smallTarget_value_eq_balancedValue (external : KP26PenalizedReduction) {r : ℝ}
    (hr : r∈Ioc (0:ℝ) smallTarget) : value r=balancedValue r := by
  have hrt : r∈Ioo (0:ℝ) transitionTarget := by
    rw [← threshold_eq_transitionTarget]
    exact ⟨hr.1,hr.2.trans_lt smallTarget_lt_threshold⟩
  rw [(smallTarget_data external hr).1,(balancedValue_below_transition hrt).1]
  rfl

/-- Full optimizer data in `prop:smalldata`: the multiplier and edge density
are forced for every graphon minimizer, not merely for the balanced competitor. -/
theorem smallTarget_optimizer_data (external : KP26PenalizedReduction) {r : ℝ}
    (hr : r∈Ioc (0:ℝ) smallTarget) {U : Graphon} (hU : IsMinimizer r U) :
    triangle U=r^3 ∧ cost U=branchCost (leftBranch r) ∧
    graphonMultiplier U r=branchMu (leftBranch r) ∧
    edgeDensity U=(branchA (leftBranch r)+branchB (leftBranch r))/2 := by
  obtain ⟨ht,hc,hpen⟩ := (smallTarget_data external hr).2 U hU
  obtain ⟨hz,_,_,hbt⟩ := smallTarget_support hr
  have hz01 : leftBranch r∈Ioo (0:ℝ) 1 :=
    ⟨hz.1,hz.2.trans_lt penalizedCrossing_mem_unit.2⟩
  have hγ := div_pos (branchMu_pos hz01.1 hz01.2) (by norm_num : (0:ℝ)<3)
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hm := minimizer_multiplier_eq_three_penalty hr01 hγ.le hU hpen
  have hm' : graphonMultiplier U r=branchMu (leftBranch r) := by linarith
  refine ⟨ht,hc,hm',?_⟩
  have he := balancedEL_multiplier_cost (branch_balancedEL hz01.1 hz01.2)
  rw [hbt] at he
  have hformula : graphonMultiplier U r*r^3=1-cost U-edgeDensity U := by
    unfold graphonMultiplier
    exact div_mul_cancel₀ _ (pow_ne_zero 3 (ne_of_gt hr.1))
  change branchMu (leftBranch r)*r^3=1-branchCost (leftBranch r)-
    (branchA (leftBranch r)+branchB (leftBranch r))/2 at he
  rw [hm',hc] at hformula
  linarith

end SparseLowerTail.Section07

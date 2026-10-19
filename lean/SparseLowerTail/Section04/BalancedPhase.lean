import SparseLowerTail.Section04.Crossing
import SparseLowerTail.Section04.CrossingDelta
import SparseLowerTail.Section04.BalancedClassification

/-!
# Complete balanced phase classification

Manuscript `cor:Vbal`, and identification of the crossing with the supremum
in the definition of `threshold`. This file concerns the scalar balanced
problem; equality with the unrestricted graphon value remains a separate proof.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section04

/-- The transition lies strictly between zero and one. -/
theorem transitionTarget_mem_Ioo : transitionTarget ∈ Ioo (0 : ℝ) 1 :=
  ⟨transitionTarget_spec.1.1, transitionTarget_spec.1.2.trans spinodalValue_mem_Ioo.2⟩

theorem leftBranch_mem_unit {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    leftBranch r ∈ Ioo (0 : ℝ) 1 := by
  have h := (leftBranch_spec ⟨hr.1,hr.2.le⟩).1
  exact ⟨h.1,h.2.trans_lt spinodal_spec.1.2⟩

/-- Unique nonpositive gap minimum at and below the transition. -/
theorem rayGap_unique_min_le_transition {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) transitionTarget) :
    rayGap r (leftBranch r) ≤ 0 ∧
    ∀ z ∈ Ioo (0 : ℝ) 1, rayGap r (leftBranch r) ≤ rayGap r z ∧
      (rayGap r z = rayGap r (leftBranch r) ↔ z = leftBranch r) := by
  have hrs : r ∈ Ioo (0 : ℝ) spinodalValue :=
    ⟨hr.1,hr.2.trans_lt transitionTarget_spec.1.2⟩
  have hshape := rayGap_shape_actual hrs
  have hl := (leftBranch_spec ⟨hrs.1,hrs.2.le⟩).1
  have hu := (rightBranch_spec ⟨hrs.1,hrs.2.le⟩).1
  have hlu := (leftBranch_lt_spinodal hrs).trans (spinodal_lt_rightBranch hrs)
  have hn : crossingDelta r ≤ 0 := by
    have h := strictMonoOn_crossingDelta_Ioc.monotoneOn
      ⟨hr.1,hrs.2.le⟩ ⟨transitionTarget_spec.1.1,transitionTarget_spec.1.2.le⟩ hr.2
    simpa only [transitionTarget_spec.2] using h
  change rayGap r (leftBranch r) ≤ 0 at hn
  exact ⟨hn,fun z hz => rayGap_unique_min_of_nonpos hl.1 hlu hu.2
    hshape.1 hshape.2.1 hshape.2.2 hn hz⟩

/-- `cor:Vbal`(a): below the transition exactly one balanced pair minimizes. -/
theorem balancedMinimizer_below_transition {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) transitionTarget)
    (a b : ℝ) :
    IsBalancedMinimizer r a b ↔ a = branchA (leftBranch r) ∧ b = branchB (leftBranch r) := by
  have hrs : r ∈ Ioo (0 : ℝ) spinodalValue := ⟨hr.1,hr.2.trans transitionTarget_spec.1.2⟩
  have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1,hrs.2.trans spinodalValue_mem_Ioo.2⟩
  have hz := leftBranch_mem_unit hrs
  have hi := branchRho_leftBranch ⟨hrs.1.le,hrs.2.le⟩
  have hg := rayGap_unique_min_le_transition ⟨hr.1,hr.2.le⟩
  have hn : rayGap r (leftBranch r) < 0 := (crossingDelta_neg_iff ⟨hr.1,hrs.2.le⟩).mpr hr.2
  rw [balancedMinimizer_iff_of_unique_gap_min hr1 hz hi hg.1 hg.2]
  exact or_iff_left (fun h => hn.ne h.2.2)

/-- `cor:Vbal`(a): the value and strict improvement below the transition. -/
theorem balancedValue_below_transition {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) transitionTarget) :
    balancedValue r = balancedCost (branchA (leftBranch r)) (branchB (leftBranch r)) ∧
    balancedValue r = entropy r + r*crossingDelta r ∧ balancedValue r < entropy r := by
  have hm := (balancedMinimizer_below_transition hr _ _).mpr ⟨rfl,rfl⟩
  have he := (isBalancedMinimizer_iff.mp hm).2.symm
  have hrs : r ∈ Ioo (0 : ℝ) spinodalValue := ⟨hr.1,hr.2.trans transitionTarget_spec.1.2⟩
  have hi := branchRho_leftBranch ⟨hrs.1.le,hrs.2.le⟩
  have hc := branch_cost_eq_gap hr.1 (leftBranch_mem_unit hrs).1 hi
  change balancedCost _ _ = entropy r + r*crossingDelta r at hc
  have hn := (crossingDelta_neg_iff ⟨hr.1,hrs.2.le⟩).mpr hr.2
  exact ⟨he,he.trans hc,by rw [he,hc]; linarith [mul_neg_of_pos_of_neg hr.1 hn]⟩

/-- `cor:Vbal`(b): precisely two balanced pairs minimize at the transition. -/
theorem balancedMinimizer_at_transition (a b : ℝ) :
    IsBalancedMinimizer transitionTarget a b ↔
      (a = transitionTarget ∧ b = transitionTarget) ∨
      (a = branchA (leftBranch transitionTarget) ∧ b = branchB (leftBranch transitionTarget)) := by
  have hz := leftBranch_mem_unit transitionTarget_spec.1
  have hi := branchRho_leftBranch ⟨transitionTarget_spec.1.1.le,transitionTarget_spec.1.2.le⟩
  have hg := rayGap_unique_min_le_transition ⟨transitionTarget_spec.1.1,le_rfl⟩
  rw [balancedMinimizer_iff_of_unique_gap_min transitionTarget_mem_Ioo hz hi hg.1 hg.2]
  have he : rayGap transitionTarget (leftBranch transitionTarget) = 0 := transitionTarget_spec.2
  simp only [he,and_true,or_comm]

theorem balancedValue_at_transition : balancedValue transitionTarget = entropy transitionTarget := by
  have hm := (balancedMinimizer_at_transition transitionTarget transitionTarget).mpr (Or.inl ⟨rfl,rfl⟩)
  simpa using (isBalancedMinimizer_iff.mp hm).2.symm

/-- `cor:Vbal`(c): only the constant pair minimizes above the transition. -/
theorem balancedMinimizer_above_transition {r : ℝ} (hr : r ∈ Ioo transitionTarget 1)
    (a b : ℝ) : IsBalancedMinimizer r a b ↔ a = r ∧ b = r := by
  apply balancedMinimizer_iff_diagonal_of_gap_pos ⟨transitionTarget_mem_Ioo.1.trans hr.1,hr.2⟩
  intro z hz
  exact rayGap_pos_above_transition hr.1 hz

theorem balancedValue_above_transition {r : ℝ} (hr : r ∈ Ioo transitionTarget 1) :
    balancedValue r = entropy r := by
  have hm := (balancedMinimizer_above_transition hr r r).mpr ⟨rfl,rfl⟩
  simpa using (isBalancedMinimizer_iff.mp hm).2.symm

/-- Strict improvement is exactly the interval below the crossing. -/
theorem balanced_strict_improvement_iff {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedValue r < entropy r ↔ r < transitionTarget := by
  rcases lt_trichotomy r transitionTarget with h | rfl | h
  · exact iff_of_true (balancedValue_below_transition ⟨hr.1,h⟩).2.2 h
  · simp [balancedValue_at_transition]
  · simp [balancedValue_above_transition ⟨h,hr.2⟩,not_lt_of_gt h]

/-- The crossing target agrees with the threshold used in the main theorem. -/
theorem threshold_eq_transitionTarget : threshold = transitionTarget :=
  threshold_eq_of_balanced_improvement transitionTarget_mem_Ioo
    (fun _ hr => balanced_strict_improvement_iff hr)

theorem threshold_mem_Ioo : threshold ∈ Ioo (0 : ℝ) 1 := by
  rw [threshold_eq_transitionTarget]
  exact transitionTarget_mem_Ioo

theorem balanced_strict_improvement_iff_threshold {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedValue r < entropy r ↔ r < threshold := by
  rw [threshold_eq_transitionTarget]
  exact balanced_strict_improvement_iff hr

end SparseLowerTail.Section04

import SparseLowerTail.Section04.BranchInverse
import SparseLowerTail.Section04.CrossingShape
import SparseLowerTail.Section04.CrossingDelta

/-! The normalized gap comparisons in `thm:crossing`, using the actual inverse
branches constructed from `lem:unimodal`. -/
noncomputable section
open Set
namespace SparseLowerTail.Section04

/-- The three monotonicity intervals in the proof of `thm:crossing`. -/
theorem rayGap_shape_actual {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    StrictAntiOn (rayGap r) (Ioc (0 : ℝ) (leftBranch r)) ∧
    StrictMonoOn (rayGap r) (Icc (leftBranch r) (rightBranch r)) ∧
    StrictAntiOn (rayGap r) (Icc (rightBranch r) 1) := by
  have hl := (leftBranch_spec ⟨hr.1, le_of_lt hr.2⟩).1
  have hu := (rightBranch_spec ⟨hr.1, le_of_lt hr.2⟩).1
  have hlu := (leftBranch_lt_spinodal hr).trans (spinodal_lt_rightBranch hr)
  obtain ⟨h1, h2, h3⟩ := branchRho_level_signs hr
  exact rayGap_shape hr.1 hl.1 hlu hu.2 h1 h2 h3

/-- At and above the spinodal the full open ray is strictly decreasing. -/
theorem rayGap_strictAnti_above_spinodal {r : ℝ} (hr : spinodalValue ≤ r) :
    StrictAntiOn (rayGap r) (Ioc (0 : ℝ) 1) := by
  apply rayGap_strictAnti_of_single_exception (lt_of_lt_of_le spinodalValue_mem_Ioo.1 hr) spinodal_spec.1
  intro z hz hne
  exact (branchRho_lt_spinodalValue hz hne).trans_le hr

theorem rayGap_pos_above_spinodal {r z : ℝ} (hr : spinodalValue ≤ r)
    (hz : z ∈ Ioo (0 : ℝ) 1) : 0 < rayGap r z := by
  have h := rayGap_strictAnti_above_spinodal hr ⟨hz.1, le_of_lt hz.2⟩ ⟨by norm_num, le_rfl⟩ hz.2
  simpa using h

/-- The decreasing upper branch has positive gap, regardless of the lower minimum. -/
theorem rayGap_pos_at_rightBranch {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    0 < rayGap r (rightBranch r) := by
  have hu := (rightBranch_spec ⟨hr.1, le_of_lt hr.2⟩).1
  exact rayGap_pos_on_right hu.2 (rayGap_shape_actual hr).2.2 ⟨le_rfl, hu.2⟩

/-- The paper's crossing parameter z_* on the increasing inverse branch. -/
def transitionParameter : ℝ := leftBranch transitionTarget

theorem transitionParameter_mem_Ioo : transitionParameter ∈ Ioo (0 : ℝ) spinodal :=
  ⟨(leftBranch_spec ⟨transitionTarget_spec.1.1, le_of_lt transitionTarget_spec.1.2⟩).1.1,
    leftBranch_lt_spinodal transitionTarget_spec.1⟩

theorem branchRho_transitionParameter : branchRho transitionParameter = transitionTarget :=
  branchRho_leftBranch ⟨le_of_lt transitionTarget_spec.1.1, le_of_lt transitionTarget_spec.1.2⟩

/-- `thm:crossing` (b), below the transition: the unique negative global minimum. -/
theorem rayGap_unique_min_below_transition {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) transitionTarget) :
    crossingDelta r < 0 ∧ ∀ z ∈ Ioo (0 : ℝ) 1,
      crossingDelta r ≤ rayGap r z ∧ (rayGap r z = crossingDelta r ↔ z = leftBranch r) := by
  have hrs : r ∈ Ioo (0 : ℝ) spinodalValue := ⟨hr.1, hr.2.trans transitionTarget_spec.1.2⟩
  have hδ := (crossingDelta_neg_iff ⟨hrs.1, le_of_lt hrs.2⟩).mpr hr.2
  refine ⟨hδ, ?_⟩
  intro z hz
  have hl := (leftBranch_spec ⟨hrs.1, le_of_lt hrs.2⟩).1
  have hu := (rightBranch_spec ⟨hrs.1, le_of_lt hrs.2⟩).1
  have hshape := rayGap_shape_actual hrs
  exact rayGap_unique_min_of_nonpos hl.1
    ((leftBranch_lt_spinodal hrs).trans (spinodal_lt_rightBranch hrs)) hu.2
    hshape.1 hshape.2.1 hshape.2.2 (le_of_lt hδ) hz

/-- `thm:crossing` (b), at the transition: a unique zero and no negative rays. -/
theorem rayGap_at_transition {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ rayGap transitionTarget z ∧ (rayGap transitionTarget z = 0 ↔ z = transitionParameter) := by
  have hr := transitionTarget_spec.1
  have hl := (leftBranch_spec ⟨hr.1, le_of_lt hr.2⟩).1
  have hu := (rightBranch_spec ⟨hr.1, le_of_lt hr.2⟩).1
  have hshape := rayGap_shape_actual hr
  have hzero : rayGap transitionTarget (leftBranch transitionTarget) = 0 := transitionTarget_spec.2
  have h := rayGap_unique_min_of_nonpos hl.1
    ((leftBranch_lt_spinodal hr).trans (spinodal_lt_rightBranch hr)) hu.2
    hshape.1 hshape.2.1 hshape.2.2 (le_of_eq hzero) hz
  simpa only [hzero, transitionParameter] using h

/-- `thm:crossing` (b), above the transition: every nonconstant ray has positive gap. -/
theorem rayGap_pos_above_transition {r z : ℝ} (hr : transitionTarget < r)
    (hz : z ∈ Ioo (0 : ℝ) 1) : 0 < rayGap r z := by
  by_cases hsp : r < spinodalValue
  · have hrs : r ∈ Ioo (0 : ℝ) spinodalValue := ⟨transitionTarget_spec.1.1.trans hr, hsp⟩
    have hl := (leftBranch_spec ⟨hrs.1, le_of_lt hrs.2⟩).1
    have hu := (rightBranch_spec ⟨hrs.1, le_of_lt hrs.2⟩).1
    have hshape := rayGap_shape_actual hrs
    have hδ := (crossingDelta_pos_iff ⟨hrs.1, le_of_lt hrs.2⟩).mpr hr
    exact rayGap_pos_of_left_root_pos hl.1
      ((leftBranch_lt_spinodal hrs).trans (spinodal_lt_rightBranch hrs)) hu.2
      hshape.1 hshape.2.1 hshape.2.2 hδ hz
  · exact rayGap_pos_above_spinodal (le_of_not_gt hsp) hz

/-- `thm:crossing` (c), the positive side of D. -/
theorem branchDifference_pos_before_transition {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) transitionParameter) : 0 < branchDifference z := by
  have hzs : z < spinodal := hz.2.trans transitionParameter_mem_Ioo.2
  have hz1 : z < 1 := hzs.trans spinodal_spec.1.2
  have hr : branchRho z ∈ Ioo (0 : ℝ) transitionTarget := by
    refine ⟨(branchRho_mem_Ioo hz.1 hz1).1, ?_⟩
    rw [← branchRho_transitionParameter]
    exact strictMonoOn_branchRho_left ⟨le_of_lt hz.1, le_of_lt hzs⟩
      ⟨le_of_lt transitionParameter_mem_Ioo.1, le_of_lt transitionParameter_mem_Ioo.2⟩ hz.2
  have hδ := (rayGap_unique_min_below_transition hr).1
  have hinv := leftBranch_branchRho ⟨le_of_lt hz.1, le_of_lt hzs⟩
  change rayGap (branchRho z) (leftBranch (branchRho z)) < 0 at hδ
  rw [hinv] at hδ
  rw [branchDifference_eq hz.1 hz1]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hr.1) hδ

@[simp] theorem branchDifference_transition : branchDifference transitionParameter = 0 := by
  have hz := transitionParameter_mem_Ioo
  rw [branchDifference_eq hz.1 (hz.2.trans spinodal_spec.1.2), branchRho_transitionParameter]
  have he : rayGap transitionTarget transitionParameter = 0 := transitionTarget_spec.2
  rw [he, mul_zero]

/-- `thm:crossing` (c), the negative side of D, including the upper inverse branch. -/
theorem branchDifference_neg_after_transition {z : ℝ}
    (hz : z ∈ Ioo transitionParameter 1) : branchDifference z < 0 := by
  have hzp : 0 < z := transitionParameter_mem_Ioo.1.trans hz.1
  have hρ := branchRho_mem_Ioo hzp hz.2
  have hgap : 0 < rayGap (branchRho z) z := by
    by_cases hzs : z ≤ spinodal
    · have hr : transitionTarget < branchRho z := by
        rw [← branchRho_transitionParameter]
        exact strictMonoOn_branchRho_left
          ⟨le_of_lt transitionParameter_mem_Ioo.1, le_of_lt transitionParameter_mem_Ioo.2⟩
          ⟨le_of_lt hzp, hzs⟩ hz.1
      exact rayGap_pos_above_transition hr ⟨hzp, hz.2⟩
    · have hsz := lt_of_not_ge hzs
      have hrs : branchRho z ∈ Ioo (0 : ℝ) spinodalValue :=
        ⟨hρ.1, branchRho_lt_spinodalValue ⟨hzp, hz.2⟩ (ne_of_gt hsz)⟩
      have h := rayGap_pos_at_rightBranch hrs
      rwa [rightBranch_branchRho ⟨le_of_lt hsz, hz.2⟩] at h
  rw [branchDifference_eq hzp hz.2]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hρ.1) hgap

/-- The crossing of D is unique, with no numerical approximation used. -/
theorem branchDifference_zero_iff {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    branchDifference z = 0 ↔ z = transitionParameter := by
  constructor
  · intro he
    rcases lt_trichotomy z transitionParameter with hl | heq | hr
    · exact False.elim ((ne_of_gt (branchDifference_pos_before_transition ⟨hz.1, hl⟩)) he)
    · exact heq
    · exact False.elim ((ne_of_lt (branchDifference_neg_after_transition ⟨hr, hz.2⟩)) he)
  · rintro rfl
    exact branchDifference_transition

end SparseLowerTail.Section04

import SparseLowerTail.Section07.PenalizedHessian
import SparseLowerTail.Section07.PenalizedCrossing

/-! The complete scalar penalized phase classification, `prop:pen`.
All supporting-pair and branch-range assertions are derived from the stationary,
fold and crossing theorems; no KP26 theorem is needed in this module. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

/-- The critical penalty γ_c. -/
def criticalPenalty : ℝ := branchMu penalizedCrossing/3
/-- The triangle target of the nonconstant critical minimizer, r_-. -/
def smallTarget : ℝ := branchRho penalizedCrossing
/-- The constant critical minimizer, r_+. -/
def largeTarget : ℝ := constantRoot criticalPenalty

theorem penalizedCrossing_mem_unit : penalizedCrossing ∈ Ioo (0:ℝ) 1 :=
  ⟨penalizedCrossing_spec.1.1,penalizedCrossing_lt_fold.trans foldPoint_spec.1.2⟩

theorem criticalPenalty_pos : 0<criticalPenalty :=
  div_pos (branchMu_pos penalizedCrossing_mem_unit.1 penalizedCrossing_mem_unit.2) (by norm_num)

theorem smallTarget_mem_unit : smallTarget ∈ Ioo (0:ℝ) 1 :=
  branchRho_mem_Ioo penalizedCrossing_mem_unit.1 penalizedCrossing_mem_unit.2

theorem largeTarget_mem_unit : largeTarget ∈ Ioo (0:ℝ) 1 :=
  (constantRoot_spec criticalPenalty_pos).1

theorem smallTarget_lt_largeTarget : smallTarget<largeTarget :=
  (penalizedGap_zero_density_order penalizedCrossing_mem_unit penalizedCrossing_spec.2).2

/-- Every nonconstant minimum lies on or before the unique penalized crossing. -/
theorem penalizedMinimizer_nonconstant_range {γ a b : ℝ} (hγ : 0<γ)
    (h : IsBalancedPenalizedMinimizer γ a b) (hne : a≠b) :
    ∃ z ∈ Ioc (0:ℝ) penalizedCrossing,
      a=branchA z ∧ b=branchB z ∧ branchMu z=3*γ := by
  obtain ⟨_,hz,ha,hb,hm⟩ := penalizedMinimizer_branch hγ h hne
  have hfold := penalizedMinimizer_branch_le_fold hγ h hne
  have hγeq : γ=branchMu (a/b)/3 := by rw [hm]; ring
  have hc := h.2.2 (constantRoot γ) (constantRoot γ)
    ⟨(constantRoot_spec hγ).1.1.le,(constantRoot_spec hγ).1.2.le⟩
    ⟨(constantRoot_spec hγ).1.1.le,(constantRoot_spec hγ).1.2.le⟩
  rw [balancedPenalty_diagonal] at hc
  have hgap : penalizedGap (a/b)≤0 := by
    rw [penalizedGap_eq hz.1,← hγeq,← ha,← hb]
    exact sub_nonpos.mpr hc
  have hzc : a/b≤penalizedCrossing := by
    by_contra hn
    have hh := penalizedGap_pos_after ⟨lt_of_not_ge hn,hfold⟩
    linarith
  exact ⟨a/b,⟨hz.1,hzc⟩,ha,hb,hm⟩

private theorem penalizedGap_nonpos_before {z : ℝ} (hz : z ∈ Ioc (0:ℝ) penalizedCrossing) :
    penalizedGap z≤0 := by
  rcases lt_or_eq_of_le hz.2 with hlt|rfl
  · exact (penalizedGap_neg_before ⟨hz.1,hlt⟩).le
  · rw [penalizedCrossing_spec.2]

/-- Every point on the pre-crossing stationary branch is a genuine global
minimum of its scalar penalized objective. -/
theorem branch_penalizedMinimizer {z : ℝ} (hz : z ∈ Ioc (0:ℝ) penalizedCrossing) :
    IsBalancedPenalizedMinimizer (branchMu z/3) (branchA z) (branchB z) := by
  have hz01 : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1,hz.2.trans_lt penalizedCrossing_mem_unit.2⟩
  have hγ : 0<branchMu z/3 := div_pos (branchMu_pos hz01.1 hz01.2) (by norm_num)
  obtain ⟨a,b,hm⟩ := exists_balancedPenalizedMinimizer (branchMu z/3)
  have hs := branch_spec hz01.1 hz01.2
  have ha : branchA z∈Icc (0:ℝ) 1 := ⟨hs.1.le,(hs.2.1.trans hs.2.2.1).le⟩
  have hb : branchB z∈Icc (0:ℝ) 1 := ⟨(branchB_pos z).le,hs.2.2.1.le⟩
  refine ⟨ha,hb,?_⟩
  intro c d hc hd
  apply le_trans _ (hm.2.2 c d hc hd)
  by_cases he : a=b
  · have hclass := (penalized_stationary_iff hγ
      (penalizedMinimizer_interior hγ hm).1 (penalizedMinimizer_interior hγ hm).2).mp
      (penalizedMinimizer_balancedEL hγ hm)
    have haRoot : a=constantRoot (branchMu z/3) := by
      apply constantRoot_unique hγ (penalizedMinimizer_pos hγ hm).1
      have hh := (penalizedMinimizer_balancedEL hγ hm).2
      rw [← he] at hh
      unfold constantEquation
      nlinarith
    rw [← he,haRoot,balancedPenalty_diagonal]
    have hgap := penalizedGap_nonpos_before hz
    rw [penalizedGap_eq hz.1] at hgap
    exact sub_nonpos.mp hgap
  · obtain ⟨w,hw,rfl,rfl,hμ⟩ := penalizedMinimizer_nonconstant_range hγ hm he
    have hwfold : w∈Ioc (0:ℝ) foldPoint := ⟨hw.1,hw.2.trans penalizedCrossing_lt_fold.le⟩
    have hzfold : z∈Ioc (0:ℝ) foldPoint := ⟨hz.1,hz.2.trans penalizedCrossing_lt_fold.le⟩
    have heq : w=z := strictAntiOn_branchMu_left.injOn hwfold hzfold (by
      calc branchMu w=3*(branchMu z/3) := hμ
           _=branchMu z := by ring)
    rw [heq]

/-- Below γ_c only the constant pair minimizes. -/
theorem penalizedMinimizer_below_critical {γ : ℝ} (hγ : 0<γ) (hcrit : γ<criticalPenalty)
    (a b : ℝ) : IsBalancedPenalizedMinimizer γ a b ↔
      a=constantRoot γ ∧ b=constantRoot γ := by
  have hclass : ∀ a b, IsBalancedPenalizedMinimizer γ a b →
      a=constantRoot γ ∧ b=constantRoot γ := by
    intro a b h
    by_cases he : a=b
    · have hh := (penalizedMinimizer_balancedEL hγ h).2
      rw [← he] at hh
      have ha : a=constantRoot γ := constantRoot_unique hγ (penalizedMinimizer_pos hγ h).1
        (by unfold constantEquation; nlinarith)
      exact ⟨ha,he.symm.trans ha⟩
    · obtain ⟨z,hz,_,_,hμ⟩ := penalizedMinimizer_nonconstant_range hγ h he
      have hh := strictAntiOn_branchMu_left.antitoneOn
        (show z∈Ioc (0:ℝ) foldPoint from ⟨hz.1,hz.2.trans penalizedCrossing_lt_fold.le⟩)
        (show penalizedCrossing∈Ioc (0:ℝ) foldPoint from
          ⟨penalizedCrossing_spec.1.1,penalizedCrossing_lt_fold.le⟩) hz.2
      rw [hμ] at hh
      unfold criticalPenalty at hcrit
      exfalso
      linarith
  constructor
  · exact hclass a b
  · rintro ⟨rfl,rfl⟩
    obtain ⟨a,b,hm⟩ := exists_balancedPenalizedMinimizer γ
    obtain ⟨rfl,rfl⟩ := hclass a b hm
    exact hm

/-- At γ_c exactly the constant pair and the crossing pair minimize. -/
theorem penalizedMinimizer_at_critical (a b : ℝ) :
    IsBalancedPenalizedMinimizer criticalPenalty a b ↔
      (a=largeTarget ∧ b=largeTarget) ∨
      (a=branchA penalizedCrossing ∧ b=branchB penalizedCrossing) := by
  have hbranch := branch_penalizedMinimizer
    (show penalizedCrossing∈Ioc (0:ℝ) penalizedCrossing from ⟨penalizedCrossing_spec.1.1,le_rfl⟩)
  constructor
  · intro h
    by_cases he : a=b
    · left
      have hh := (penalizedMinimizer_balancedEL criticalPenalty_pos h).2
      rw [← he] at hh
      have ha : a=largeTarget := constantRoot_unique criticalPenalty_pos
        (penalizedMinimizer_pos criticalPenalty_pos h).1 (by unfold constantEquation; nlinarith)
      exact ⟨ha,he.symm.trans ha⟩
    · right
      obtain ⟨z,hz,ha,hb,hμ⟩ := penalizedMinimizer_nonconstant_range criticalPenalty_pos h he
      have heq : z=penalizedCrossing := strictAntiOn_branchMu_left.injOn
        ⟨hz.1,hz.2.trans penalizedCrossing_lt_fold.le⟩
        ⟨penalizedCrossing_spec.1.1,penalizedCrossing_lt_fold.le⟩ (by
          rw [hμ,criticalPenalty]; ring)
      simpa only [heq] using And.intro ha hb
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · refine ⟨⟨largeTarget_mem_unit.1.le,largeTarget_mem_unit.2.le⟩,
        ⟨largeTarget_mem_unit.1.le,largeTarget_mem_unit.2.le⟩,?_⟩
      intro c d hc hd
      have he := penalizedCrossing_spec.2
      rw [penalizedGap_eq penalizedCrossing_spec.1.1] at he
      rw [balancedPenalty_diagonal]
      change constantPenalty criticalPenalty (constantRoot criticalPenalty) ≤ _
      change balancedPenalty criticalPenalty (branchA penalizedCrossing) (branchB penalizedCrossing)-
        constantPenalty criticalPenalty (constantRoot criticalPenalty)=0 at he
      rw [← sub_eq_zero.mp he]
      exact hbranch.2.2 c d hc hd
    · exact hbranch

/-- Every penalty above γ_c has exactly one stationary parameter before z_c. -/
theorem existsUnique_penalized_parameter {γ : ℝ} (hγ : criticalPenalty<γ) :
    ∃! z, z∈Ioo (0:ℝ) penalizedCrossing ∧ branchMu z=3*γ := by
  have hlarge : ∀ᶠ z in 𝓝[>] (0:ℝ), 3*γ<branchMu z :=
    tendsto_branchMu_zero.eventually (eventually_gt_atTop _)
  have hsmall : ∀ᶠ z in 𝓝[>] (0:ℝ), z<penalizedCrossing :=
    (eventually_lt_nhds penalizedCrossing_spec.1.1).filter_mono nhdsWithin_le_nhds
  obtain ⟨a,ha,hac,hμa⟩ := ((show ∀ᶠ z in 𝓝[>] (0:ℝ),0<z from self_mem_nhdsWithin).and
    (hsmall.and hlarge)).exists
  have hc : ContinuousOn branchMu (Icc a penalizedCrossing) := by
    intro z hz
    exact (hasDerivAt_branchMu ⟨ha.trans_le hz.1,hz.2.trans_lt penalizedCrossing_mem_unit.2⟩).continuousAt.continuousWithinAt
  have hμc : branchMu penalizedCrossing<3*γ := by unfold criticalPenalty at hγ; linarith
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc' hac.le hc ⟨hμc.le,hμa.le⟩
  have hz0 := ha.trans_le hz.1
  have hzc : z<penalizedCrossing := lt_of_le_of_ne hz.2 (by intro hh; rw [hh] at he; linarith)
  refine ⟨z,⟨⟨hz0,hzc⟩,he⟩,?_⟩
  intro w hw
  exact strictAntiOn_branchMu_left.injOn
    ⟨hw.1.1,(hw.1.2.trans penalizedCrossing_lt_fold).le⟩
    ⟨hz0,(hzc.trans penalizedCrossing_lt_fold).le⟩ (hw.2.trans he.symm)

/-- Above γ_c the supported nonconstant pair is the unique minimum. -/
theorem penalizedMinimizer_above_critical {γ z : ℝ} (hγ : criticalPenalty<γ)
    (hz : z∈Ioo (0:ℝ) penalizedCrossing) (hμ : branchMu z=3*γ) (a b : ℝ) :
    IsBalancedPenalizedMinimizer γ a b ↔ a=branchA z ∧ b=branchB z := by
  have hγpos := criticalPenalty_pos.trans hγ
  have hγeq : γ=branchMu z/3 := by rw [hμ]; ring
  have hsupport : IsBalancedPenalizedMinimizer γ (branchA z) (branchB z) := by
    rw [hγeq]; exact branch_penalizedMinimizer ⟨hz.1,hz.2.le⟩
  constructor
  · intro h
    by_cases he : a=b
    · have hh := (penalizedMinimizer_balancedEL hγpos h).2
      rw [← he] at hh
      have ha : a=constantRoot γ := constantRoot_unique hγpos
        (penalizedMinimizer_pos hγpos h).1 (by unfold constantEquation; nlinarith)
      have hc := h.2.2 (branchA z) (branchB z) hsupport.1 hsupport.2.1
      rw [← he,ha,balancedPenalty_diagonal,hγeq] at hc
      have hgap := penalizedGap_neg_before hz
      rw [penalizedGap_eq hz.1] at hgap
      exfalso
      linarith
    · obtain ⟨w,hw,ha,hb,hwμ⟩ := penalizedMinimizer_nonconstant_range hγpos h he
      have hwz : w=z := strictAntiOn_branchMu_left.injOn
        ⟨hw.1,hw.2.trans penalizedCrossing_lt_fold.le⟩
        ⟨hz.1,(hz.2.trans penalizedCrossing_lt_fold).le⟩ (hwμ.trans hμ.symm)
      simpa only [hwz] using And.intro ha hb
  · rintro ⟨rfl,rfl⟩
    exact hsupport

end SparseLowerTail.Section07

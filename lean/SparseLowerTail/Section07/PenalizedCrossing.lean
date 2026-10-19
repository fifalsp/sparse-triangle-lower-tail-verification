import SparseLowerTail.Section07.SingleCrossing

/-! The unique penalized crossing `lem:zc`, including the fold endpoint.
The compact-set upward-crossing lemma replaces the manuscript's finite-zero-set
argument and needs no global discreteness premise. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

private def densityGap (z : ℝ) : ℝ := branchRho z^3-(constantRoot (branchMu z/3))^3

private theorem continuousAt_densityGap {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt densityGap z := by
  have hm := (contDiffAt_branchMu hz.1 hz.2).continuousAt.div_const 3
  have hg : 0<branchMu z/3 := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)
  have hc : ContinuousAt constantRoot (branchMu z/3) :=
    continuousOn_constantRoot.continuousAt (isOpen_Ioi.mem_nhds hg)
  exact ((contDiffAt_branchRho hz.1 hz.2).continuousAt.pow 3).sub ((ContinuousAt.comp (f := fun x : ℝ => branchMu x/3) (x := z) hc hm).pow 3)

private theorem densityGap_neg_of_zero {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1)
    (he : penalizedGap z=0) : densityGap z<0 := by
  have hh := (penalizedGap_zero_density_order hz he).2
  have hp := (branchRho_mem_Ioo hz.1 hz.2).1
  unfold densityGap
  exact sub_neg.mpr ((pow_lt_pow_iff_left₀ hp.le (hp.trans hh).le (by decide : 3≠0)).mpr hh)

theorem deriv_penalizedGap_pos_at_zero {z : ℝ} (hz : z ∈ Ioo (0:ℝ) foldPoint)
    (he : penalizedGap z=0) : 0<deriv penalizedGap z := by
  have hz01 : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1,hz.2.trans foldPoint_spec.1.2⟩
  rw [(hasDerivAt_penalizedGap hz01).deriv]
  exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (deriv_branchMu_neg hz) (by norm_num))
    (densityGap_neg_of_zero hz01 he)

private theorem exists_penalizedGap_zero_milli :
    ∃ z ∈ Ioo (0:ℝ) (1/1000), penalizedGap z=0 := by
  have hneg : ∀ᶠ z in 𝓝[>] (0:ℝ), penalizedGap z<0 :=
    tendsto_penalizedGap_zero.eventually (eventually_lt_nhds (by norm_num : -(1:ℝ)/2<0))
  have hsmall : ∀ᶠ z in 𝓝[>] (0:ℝ), z<1/1000 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/1000)).filter_mono nhdsWithin_le_nhds
  obtain ⟨a,ha,ha1,hfa⟩ := ((show ∀ᶠ z in 𝓝[>] (0:ℝ), 0<z from self_mem_nhdsWithin).and
    (hsmall.and hneg)).exists
  have hc : ContinuousOn penalizedGap (Icc a (1/1000)) := by
    intro x hx
    exact (hasDerivAt_penalizedGap ⟨ha.trans_le hx.1,by linarith [hx.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc ha1.le hc ⟨hfa.le,penalizedGap_milli_pos.le⟩
  refine ⟨z,⟨ha.trans_le hz.1,lt_of_le_of_ne hz.2 ?_⟩,he⟩
  intro hh
  rw [hh] at he
  linarith [penalizedGap_milli_pos]

theorem penalizedGap_positive_after_zero {p q : ℝ}
    (hp : p ∈ Ioo (0:ℝ) foldPoint) (hpq : p<q) (hq : q<foldPoint)
    (he : penalizedGap p=0) : 0<penalizedGap q := by
  apply positive_after_upward_crossing hpq
  · intro x hx
    exact (hasDerivAt_penalizedGap ⟨hp.1.trans_le hx.1,(hx.2.trans_lt hq).trans foldPoint_spec.1.2⟩).continuousAt
  · intro x hx hzero
    exact deriv_penalizedGap_pos_at_zero ⟨hp.1.trans_le hx.1,hx.2.trans_lt hq⟩ hzero
  · rw [he]

/-- The critical crossing is constructed in the certified subinterval. -/
def penalizedCrossing : ℝ := Classical.choose exists_penalizedGap_zero_milli

theorem penalizedCrossing_spec : penalizedCrossing ∈ Ioo (0:ℝ) (1/1000) ∧
    penalizedGap penalizedCrossing=0 := Classical.choose_spec exists_penalizedGap_zero_milli

theorem penalizedCrossing_lt_fold : penalizedCrossing<foldPoint :=
  penalizedCrossing_spec.1.2.trans foldPoint_bounds.1

theorem penalizedGap_neg_before {z : ℝ} (hz : z ∈ Ioo (0:ℝ) penalizedCrossing) :
    penalizedGap z<0 := by
  by_contra hn
  have hp : 0≤penalizedGap z := le_of_not_gt hn
  have h := positive_after_upward_crossing hz.2
    (f := penalizedGap)
    (fun x hx => (hasDerivAt_penalizedGap ⟨hz.1.trans_le hx.1,
      (hx.2.trans_lt penalizedCrossing_lt_fold).trans foldPoint_spec.1.2⟩).continuousAt)
    (fun x hx he => deriv_penalizedGap_pos_at_zero
      ⟨hz.1.trans_le hx.1,hx.2.trans_lt penalizedCrossing_lt_fold⟩ he) hp
  rw [penalizedCrossing_spec.2] at h
  exact lt_irrefl _ h

theorem penalizedGap_pos_after_open {z : ℝ} (hz : z ∈ Ioo penalizedCrossing foldPoint) :
    0<penalizedGap z := penalizedGap_positive_after_zero
      ⟨penalizedCrossing_spec.1.1,penalizedCrossing_lt_fold⟩ hz.1 hz.2 penalizedCrossing_spec.2

/-- The stationary fold itself cannot be a tie: a hypothetical tie has a
negative density gap nearby, forcing strict increase from the left. -/
theorem penalizedGap_fold_pos : 0<penalizedGap foldPoint := by
  have hc := (hasDerivAt_penalizedGap foldPoint_spec.1).continuousAt
  have hn : 0≤penalizedGap foldPoint := by
    apply ge_of_tendsto (show Tendsto penalizedGap (𝓝[<] foldPoint)
      (𝓝 (penalizedGap foldPoint)) from hc.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds penalizedCrossing_lt_fold).filter_mono nhdsWithin_le_nhds] with z hz hzc
    exact (penalizedGap_pos_after_open ⟨hzc,hz⟩).le
  by_contra hnot
  have he : penalizedGap foldPoint=0 := le_antisymm (le_of_not_gt hnot) hn
  have hD := densityGap_neg_of_zero foldPoint_spec.1 he
  have hnear : ∀ᶠ z in 𝓝 foldPoint, densityGap z<0 :=
    (continuousAt_densityGap foldPoint_spec.1).tendsto.eventually (eventually_lt_nhds hD)
  obtain ⟨l,u,⟨hl,hu⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let v := max ((penalizedCrossing+foldPoint)/2) ((l+foldPoint)/2)
  have hvC : penalizedCrossing<v := by
    exact lt_of_lt_of_le (by linarith [penalizedCrossing_lt_fold]) (le_max_left _ _)
  have hvl : l<v := by exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hv : v<foldPoint := max_lt (by linarith [penalizedCrossing_lt_fold]) (by linarith)
  have hv0 : 0<v := penalizedCrossing_spec.1.1.trans hvC
  have hmono : StrictMonoOn penalizedGap (Icc v foldPoint) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro z hz
      exact (hasDerivAt_penalizedGap ⟨hv0.trans_le hz.1,hz.2.trans_lt foldPoint_spec.1.2⟩).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz01 : z ∈ Ioo (0:ℝ) 1 := ⟨hv0.trans hz.1,hz.2.trans foldPoint_spec.1.2⟩
      rw [(hasDerivAt_penalizedGap hz01).deriv]
      have hDz : densityGap z<0 := hsub ⟨hvl.trans hz.1,hz.2.trans hu⟩
      exact mul_pos_of_neg_of_neg
        (div_neg_of_neg_of_pos (deriv_branchMu_neg ⟨hz01.1,hz.2⟩) (by norm_num)) hDz
  have hh := hmono ⟨le_rfl,hv.le⟩ ⟨hv.le,le_rfl⟩ hv
  rw [he] at hh
  linarith [penalizedGap_pos_after_open ⟨hvC,hv⟩]

/-- Full `lem:zc`: unique zero and the signs on the entire stable branch,
including its fold endpoint. -/
theorem penalizedGap_zero_iff {z : ℝ} (hz : z ∈ Ioc (0:ℝ) foldPoint) :
    penalizedGap z=0 ↔ z=penalizedCrossing := by
  constructor
  · intro he
    rcases lt_trichotomy z penalizedCrossing with hlt|heq|hgt
    · have hh := penalizedGap_neg_before ⟨hz.1,hlt⟩
      rw [he] at hh
      exact (lt_irrefl _ hh).elim
    · exact heq
    · rcases lt_or_eq_of_le hz.2 with hlt|heq
      · have hh := penalizedGap_pos_after_open ⟨hgt,hlt⟩
        rw [he] at hh
        exact (lt_irrefl _ hh).elim
      · rw [heq] at he
        linarith [penalizedGap_fold_pos]
  · rintro rfl
    exact penalizedCrossing_spec.2

theorem penalizedGap_pos_after {z : ℝ} (hz : z ∈ Ioc penalizedCrossing foldPoint) :
    0<penalizedGap z := by
  rcases lt_or_eq_of_le hz.2 with hlt|rfl
  · exact penalizedGap_pos_after_open ⟨hz.1,hlt⟩
  · exact penalizedGap_fold_pos

end SparseLowerTail.Section07

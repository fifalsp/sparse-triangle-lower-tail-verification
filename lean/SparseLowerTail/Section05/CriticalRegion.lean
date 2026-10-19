import SparseLowerTail.Section05.SupportBounds
import SparseLowerTail.Section05.ThresholdReduction
import SparseLowerTail.Section02.Isolation
import SparseLowerTail.Section04.ThresholdDigits

/-!
# Confinement to the compact critical parameter region

Stable manuscript anchors: `s5:Omega`, `lem:region`, `s5:params`.
All numerical comparisons below follow from the kernel-checked threshold digits
and logarithm bounds. The definitions are tied to exact variational parameters.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section05
open Section02 Section04

/-- Exact critical triangle density. -/
def criticalTriangle : ℝ := threshold^3
/-- Exact critical cost. -/
def criticalCost : ℝ := entropy threshold
/-- Exact critical edge density. -/
def criticalMean : ℝ := (criticalA+criticalB)/2
/-- The isolation lower endpoint M₁. -/
def criticalMeanLower : ℝ := isolatedMean threshold
/-- The Goodman upper endpoint m_G. -/
def criticalMeanUpper : ℝ := (1+Real.sqrt (1+8*criticalTriangle))/4
/-- The full B1 lower cost bound at the critical triangle density. -/
def criticalFB1 (m : ℝ) : ℝ :=
  entropy m+beta m*(max (m^3-criticalTriangle) 0)^(2/3:ℝ)
/-- The compact region Ω from `s5:Omega`. -/
def criticalRegion : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc criticalMeanLower criticalMeanUpper ∧ criticalFB1 p.1 ≤ p.2 ∧ p.2 ≤ criticalCost}
/-- The open parameter domain Π for the triangle-law relaxation. -/
def parameterDomain : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1+p.2 < 1}

theorem critical_threshold_coarse : (205/1000:ℝ) < threshold ∧ threshold < 215/1000 := by
  have h := threshold_digits
  constructor <;> linarith [h.1,h.2]

theorem criticalTriangle_lt_one_hundredth : criticalTriangle < 1/100 := by
  have h : threshold^3 < (215/1000:ℝ)^3 := by
    gcongr
    · exact threshold_mem_Ioo.1.le
    · exact critical_threshold_coarse.2
  norm_num at h
  exact h.trans (by norm_num)

theorem criticalMeanUpper_lt : criticalMeanUpper < 51/100 := by
  have ht := criticalTriangle_lt_one_hundredth
  have hn : 0 ≤ 1+8*criticalTriangle := by
    have h : 0 ≤ criticalTriangle := pow_nonneg threshold_mem_Ioo.1.le 3
    linarith
  have hs := Real.sq_sqrt hn
  have hsn := Real.sqrt_nonneg (1+8*criticalTriangle)
  unfold criticalMeanUpper
  nlinarith

/-- A small exact logarithm estimate sufficient for Ω⊂Π. -/
theorem log_critical_lowerEndpoint_lt : Real.log (205/1000:ℝ) < -(3/2:ℝ) := by
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 82/100)
  have hid : Real.log (82/100:ℝ) = 2*Real.log 2 + Real.log (205/1000:ℝ) := by
    rw [show (82/100:ℝ) = (2:ℝ)^2*(205/1000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [hid] at hlog
  have htwo := Numerics.log_two_bounds_22.1
  linarith

theorem criticalCost_lt : criticalCost < 49/100 := by
  have h := strictAntiOn_entropy (show (205/1000:ℝ) ∈ Icc 0 1 by norm_num)
    ⟨threshold_mem_Ioo.1.le, threshold_mem_Ioo.2.le⟩ critical_threshold_coarse.1
  have hn : entropy (205/1000:ℝ) < 49/100 := by
    unfold entropy
    linarith [log_critical_lowerEndpoint_lt]
  exact h.trans hn

theorem criticalMeanUpper_add_cost_lt_one : criticalMeanUpper+criticalCost < 1 := by
  linarith [criticalMeanUpper_lt,criticalCost_lt]

theorem criticalMeanLower_gt_threshold : threshold < criticalMeanLower :=
  isolatedMean_gt threshold_mem_Ioo

theorem criticalMean_interval_subset : Icc criticalMeanLower criticalMeanUpper ⊆ Ioo (0:ℝ) 1 := by
  intro m hm
  exact ⟨threshold_mem_Ioo.1.trans (criticalMeanLower_gt_threshold.trans_le hm.1),
    hm.2.trans_lt (criticalMeanUpper_lt.trans (by norm_num))⟩

/-- `lem:region`(a): every qualifying graphon belongs to Ω. -/
theorem graphon_mem_criticalRegion {U : Graphon}
    (ht : triangle U = criticalTriangle) (hF : cost U ≤ criticalCost)
    (hn : ¬IsConstant U threshold) : (edgeDensity U,cost U) ∈ criticalRegion := by
  have hf : Feasible threshold U := ht.le
  have hlo := (isolation threshold_mem_Ioo hf hF hn).2
  have hhi : edgeDensity U ≤ criticalMeanUpper := by
    simpa only [ht,criticalMeanUpper] using goodman_mean_bound U
  have hmem : edgeDensity U ∈ Icc criticalMeanLower criticalMeanUpper := ⟨hlo,hhi⟩
  refine ⟨hmem, ?_, hF⟩
  have h := cost_ge_entropy_triangle_deficit (criticalMean_interval_subset hmem)
  simpa only [criticalFB1,ht] using h

/-- `lem:region`(b), stated for the stronger exclusion of the constant threshold graphon. -/
theorem minimizer_mem_criticalRegion {U : Graphon} (hU : IsMinimizer threshold U)
    (hn : ¬IsConstant U threshold) : (edgeDensity U,cost U) ∈ criticalRegion :=
  graphon_mem_criticalRegion (minimizer_triangle_eq threshold_mem_Ioo hU)
    (minimizer_cost_le_entropy threshold_mem_Ioo hU) hn

/-- The critical balanced pair has strictly more edges than the constant graphon. -/
theorem criticalMean_gt_threshold : threshold < criticalMean := by
  have hid := mean_cube_sub_balancedTriangle (a := criticalA) (b := criticalB)
  rw [critical_pair_triangle] at hid
  have hab : criticalA < criticalB := branchA_lt_branchB (transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2)
  have hpos := pow_pos (sub_pos.mpr hab) 3
  have hcube : threshold^3 < criticalMean^3 := by
    change threshold^3 < ((criticalA+criticalB)/2)^3
    linarith
  exact (show Odd (3:ℕ) by decide).strictMono_pow.lt_iff_lt.mp hcube

/-- `lem:region`(c): the exact critical balanced point lies in Ω. -/
theorem criticalPoint_mem_criticalRegion : (criticalMean,criticalCost) ∈ criticalRegion := by
  let U := balancedGraphon criticalA criticalB critical_pair_bounds.1 critical_pair_bounds.2
  have hB : IsBalanced U criticalA criticalB :=
    balancedGraphon_isBalanced _ _ _ _
  have ht : triangle U = criticalTriangle :=
    (hB.triangle_eq critical_pair_bounds.1 critical_pair_bounds.2).trans critical_pair_triangle
  have hF : cost U = criticalCost :=
    (hB.cost_eq critical_pair_bounds.1 critical_pair_bounds.2).trans critical_pair_cost
  have hm : edgeDensity U = criticalMean := hB.edgeDensity_eq
  have hn : ¬IsConstant U threshold := by
    intro hc
    have he := edgeDensity_congr_ae (U := U)
      (W := constant threshold ⟨threshold_mem_Ioo.1.le,threshold_mem_Ioo.2.le⟩) hc
    have he' : edgeDensity U = threshold := by simpa [edgeDensity,constant] using he
    linarith [criticalMean_gt_threshold]
  simpa only [hm,hF] using graphon_mem_criticalRegion ht hF.le hn

/-- `lem:region`(c): the entire closed region lies in the admissible open domain. -/
theorem criticalRegion_subset_parameterDomain : criticalRegion ⊆ parameterDomain := by
  intro p hp
  refine ⟨(criticalMean_interval_subset hp.1).1, ?_⟩
  have h := criticalMeanUpper_add_cost_lt_one
  linarith [hp.1.2,hp.2.2]

/-- Continuity of the B1 boundary on the mean interval. -/
theorem continuousOn_criticalFB1 : ContinuousOn criticalFB1 (Icc criticalMeanLower criticalMeanUpper) := by
  intro m hm
  have hbeta := continuousAt_beta (criticalMean_interval_subset hm)
  have hcont : ContinuousAt criticalFB1 m := by
    unfold criticalFB1
    exact continuous_entropy.continuousAt.add
      (hbeta.mul (((continuousAt_id.pow 3).sub continuousAt_const).max continuousAt_const |>.rpow_const (Or.inr (by norm_num))))
  exact hcont.continuousWithinAt

theorem criticalFB1_nonneg {m : ℝ} (hm : m ∈ Icc criticalMeanLower criticalMeanUpper) :
    0 ≤ criticalFB1 m := by
  have hi := criticalMean_interval_subset hm
  have hb : 0 ≤ beta m := le_trans (by norm_num) (beta_ge_half hi)
  unfold criticalFB1
  exact add_nonneg (entropy_nonneg hi.1.le) (mul_nonneg hb (Real.rpow_nonneg (le_max_right _ _) _))

/-- The critical parameter region is closed. -/
theorem isClosed_criticalRegion : IsClosed criticalRegion := by
  have he := isClosed_Icc.epigraph continuousOn_criticalFB1
  have hf : IsClosed {p : ℝ × ℝ | p.2 ≤ criticalCost} := isClosed_le continuous_snd continuous_const
  convert he.inter hf using 1
  ext p
  simp only [criticalRegion,mem_setOf_eq,mem_inter_iff]
  tauto

/-- Compactness asserted immediately after `s5:Omega`. -/
theorem isCompact_criticalRegion : IsCompact criticalRegion := by
  apply ((isCompact_Icc : IsCompact (Icc criticalMeanLower criticalMeanUpper)).prod
    (isCompact_Icc : IsCompact (Icc (0:ℝ) criticalCost))).of_isClosed_subset isClosed_criticalRegion
  intro p hp
  exact ⟨hp.1, (criticalFB1_nonneg hp.1).trans hp.2.1, hp.2.2⟩

end SparseLowerTail.Section05

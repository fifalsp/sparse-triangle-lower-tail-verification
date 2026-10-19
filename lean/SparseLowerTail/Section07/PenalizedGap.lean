import SparseLowerTail.Section07.ConstantRootCalculus
import SparseLowerTail.Section04.CrossingDelta
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The analytic penalized gap in `lem:tie`: derivative, strict density order
at a zero, the limit at zero, and a certified positive endpoint sign. This
completes `lem:tie`; fold location and unique crossing are separate obligations. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

/-- The manuscript's Δ(z), comparing the two stationary penalized costs. -/
def penalizedGap (z : ℝ) : ℝ := branchCost z+branchMu z/3*branchRho z^3-
  constantMinimum (branchMu z/3)

theorem penalizedGap_eq {z : ℝ} (hz : 0 < z) :
    penalizedGap z = balancedPenalty (branchMu z/3) (branchA z) (branchB z)-
      constantPenalty (branchMu z/3) (constantRoot (branchMu z/3)) := by
  rw [balancedPenalty,branch_triangle_eq_rho_cube hz]
  rfl

theorem hasDerivAt_penalizedGap {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    HasDerivAt penalizedGap (deriv branchMu z/3*
      (branchRho z^3-(constantRoot (branchMu z/3))^3)) z := by
  have hm := ((contDiffAt_branchMu hz.1 hz.2).differentiableAt (by norm_num)).hasDerivAt
  have hr := ((contDiffAt_branchRho hz.1 hz.2).differentiableAt (by norm_num)).hasDerivAt
  have hγ : 0 < branchMu z/3 := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)
  have hc := (hasDerivAt_constantMinimum hγ).comp z (hm.div_const 3)
  convert ((hasDerivAt_branchCost hz.1 hz.2).add ((hm.div_const 3).mul (hr.pow 3))).sub hc using 1
  dsimp
  ring

theorem contDiffOn_penalizedGap : ContDiffOn ℝ 1 penalizedGap (Ioo (0:ℝ) 1) := by
  intro z hz
  have hm := (contDiffAt_branchMu hz.1 hz.2).div_const 3
  have hγ : 0 < branchMu z/3 := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)
  have hc := contDiffOn_constantMinimum.contDiffAt (isOpen_Ioi.mem_nhds hγ)
  exact (((contDiffAt_branchCost hz.1 hz.2).add
    (hm.mul ((contDiffAt_branchRho hz.1 hz.2).pow 3))).sub (hc.comp z hm)).contDiffWithinAt

theorem penalizedGap_zero_density_order {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1)
    (he : penalizedGap z=0) :
    constantRoot (branchMu z/3) < (branchA z+branchB z)/2 ∧
      branchRho z < constantRoot (branchMu z/3) := by
  have hγ : 0 < branchMu z/3 := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)
  obtain ⟨ha,hab,hb,_,hel⟩ := branch_spec hz.1 hz.2
  have hel' : BalancedEL (branchA z) (branchB z) (3*(branchMu z/3)) := by
    convert hel using 1
    ring
  have htie : balancedPenalty (branchMu z/3) (branchA z) (branchB z) =
      constantPenalty (branchMu z/3) (constantRoot (branchMu z/3)) := by
    rw [penalizedGap_eq hz.1] at he
    exact sub_eq_zero.mp he
  obtain ⟨hm,ht⟩ := stationary_tie_density_order hγ ⟨ha,hab.trans hb⟩
    ⟨branchB_pos z,hb⟩ (ne_of_lt hab) hel' htie
  rw [branch_triangle_eq_rho_cube hz.1] at ht
  refine ⟨hm,?_⟩
  exact (pow_lt_pow_iff_left₀ (branchRho_mem_Ioo hz.1 hz.2).1.le
    (constantRoot_spec hγ).1.1.le (by decide : 3≠0)).mp ht

theorem branchMu_lower_bound {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    2*branchLog z ≤ branchMu z := by
  have hb := branchB_pos z
  have hb1 := branchB_lt_one hz.1 hz.2
  have hd : 0 < (1-z)^2*(branchB z)^2 := by
    exact mul_pos (sq_pos_of_pos (sub_pos.mpr hz.2)) (sq_pos_of_pos hb)
  have hden : (1-z)^2*(branchB z)^2 ≤ 1 := by
    have hz2 : (1-z)^2 ≤ 1 := by nlinarith [hz.1,hz.2]
    have hb2 : (branchB z)^2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (1-z),sq_nonneg (branchB z)]
  have hm := branchMu_pos hz.1 hz.2
  have he : branchMu z*((1-z)^2*(branchB z)^2) = 2*branchLog z := by
    unfold branchMu
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  nlinarith

theorem tendsto_branchMu_zero : Tendsto branchMu (𝓝[>] (0:ℝ)) atTop := by
  have hlog : Tendsto (fun z => 2*branchLog z) (𝓝[>] (0:ℝ)) atTop := by
    simp only [branchLog_eq_neg_log]
    exact Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2)
      (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  apply tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds]
      with z hz hz1
  exact branchMu_lower_bound ⟨hz,hz1⟩

theorem branch_penalized_cost_eq {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    branchCost z+branchMu z/3*branchRho z^3 =
      (2*branchCost z+1-(branchA z+branchB z)/2)/3 := by
  have h := balancedEL_multiplier_cost (branch_balancedEL hz.1 hz.2)
  rw [branch_triangle_eq_rho_cube hz.1] at h
  change branchMu z*branchRho z^3=1-branchCost z-(branchA z+branchB z)/2 at h
  linarith

theorem tendsto_penalizedGap_zero : Tendsto penalizedGap (𝓝[>] (0:ℝ)) (𝓝 (-1/2)) := by
  have hm : Tendsto (fun z => branchMu z/3) (𝓝[>] (0:ℝ)) atTop := by
    simpa only [div_eq_mul_inv,mul_comm] using
      Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<(3:ℝ)⁻¹) tendsto_branchMu_zero
  have hc := tendsto_constantMinimum_atTop.comp hm
  have hA : ContinuousAt branchA 0 := continuousAt_id.mul continuousAt_branchB_zero
  have hC := continuousAt_branchCost_zero.tendsto.mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hmean := ((hA.add continuousAt_branchB_zero).div_const 2).tendsto.mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim := ((((hC.const_mul 2).add_const 1).sub hmean).div_const 3).sub hc
  have he : penalizedGap =ᶠ[𝓝[>] (0:ℝ)] (fun z =>
      (2*branchCost z+1-(branchA z+branchB z)/2)/3-constantMinimum (branchMu z/3)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds]
        with z hz hz1
    rw [penalizedGap,branch_penalized_cost_eq ⟨hz,hz1⟩]
  apply Tendsto.congr' he.symm
  norm_num [branchA,branchB] at hlim ⊢
  exact hlim

/-- A coarse certified endpoint sign suffices: trial constant 1/4 gives an
upper bound below 0.484, while the nonconstant stationary cost exceeds 0.496.
Only mathlib's proved logarithm-of-two bounds are used. -/
theorem penalizedGap_milli_pos : 0 < penalizedGap (1/1000:ℝ) := by
  let z : ℝ := 1/1000
  have hz : z ∈ Ioo (0:ℝ) 1 := by norm_num [z]
  have hL : branchLog z < 7 := by
    have hl := Real.log_lt_log (by norm_num : (0:ℝ)<1000)
      (by norm_num : (1000:ℝ)<2^10)
    rw [Real.log_pow] at hl
    have ht := Real.log_two_lt_d9
    have he : branchLog z = Real.log 1000 := by norm_num [branchLog,z]
    rw [he]
    norm_num at hl
    linarith
  have hbpos := branchB_pos z
  have hb1 := branchB_lt_one hz.1 hz.2
  have hb : 197/200 < branchB z := by
    have he : -(3/200:ℝ) < -2*z*branchLog z/(1-z)^2 := by
      have hden : (1-z)^2 = (998001/1000000:ℝ) := by norm_num [z]
      rw [hden]
      change -(3/200:ℝ) < -2*(1/1000)*branchLog z/(998001/1000000)
      linarith
    have hexp := Real.add_one_le_exp (-2*z*branchLog z/(1-z)^2)
    change _ ≤ branchB z at hexp
    linarith
  have hb2 : (97/100:ℝ) < (branchB z)^2 := by nlinarith
  let γ := branchMu z/3
  have hγ : 0 < γ := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)
  have hγ5 : γ < 5 := by
    change (2*branchLog z/((1-z)^2*(branchB z)^2))/3 < 5
    rw [div_div]
    apply (div_lt_iff₀ (by positivity : 0 < ((1-z)^2*(branchB z)^2)*3)).mpr
    have hd : (1-z)^2 = (998001/1000000:ℝ) := by norm_num [z]
    rw [hd]
    nlinarith
  have ha := branchA_pos hz.1
  have haz : branchA z < z := by
    unfold branchA
    nlinarith [hz.1]
  have hcost : (496/1000:ℝ) < balancedPenalty γ (branchA z) (branchB z) := by
    have hh := strictAntiOn_entropy ⟨ha.le,(haz.trans hz.2).le⟩
      ⟨hz.1.le,hz.2.le⟩ haz
    have hbent := entropy_nonneg hbpos.le
    have htpos : 0 ≤ balancedTriangle (branchA z) (branchB z) := by
      unfold balancedTriangle
      positivity
    have hent : (992/1000:ℝ) < entropy z := by
      have he := branchLog_eq_neg_log z
      unfold entropy
      dsimp [z] at *
      nlinarith
    unfold balancedPenalty balancedCost
    nlinarith [mul_nonneg hγ.le htpos]
  have htrial : constantPenalty γ (1/4:ℝ) < 484/1000 := by
    have hl : Real.log (1/4:ℝ) = -2*Real.log 2 := by
      rw [show (1/4:ℝ)=((2:ℝ)^2)⁻¹ by norm_num,Real.log_inv,Real.log_pow]
      ring
    have ht := Real.log_two_gt_d9
    unfold constantPenalty entropy
    rw [hl]
    norm_num
    linarith
  have hmin := constantPenalty_min hγ (by norm_num : (1/4:ℝ) ∈ Icc 0 1)
  rw [penalizedGap_eq hz.1]
  change 0 < balancedPenalty γ (branchA z) (branchB z)-constantPenalty γ (constantRoot γ)
  linarith

end SparseLowerTail.Section07

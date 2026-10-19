import SparseLowerTail.Section07.SmallData
import SparseLowerTail.Section04.ThresholdDigits
import SparseLowerTail.Numerics.IntervalArithmetic

/-! The actual logarithmic parameter interval required by the intermediate
certificate. A coarse lower bracket for the penalized crossing is proved
here; no unproved printed numerical constants are used. -/
noncomputable section
open Set
namespace SparseLowerTail.Section08
open Section04 Section07 Numerics

def familySmallLower : ℝ := 1/12500

private theorem family_log_lower : Bounds (Real.log (1/12500:ℝ)) (-18867/2000:ℝ) (-47167/5000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-971/3125:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (4096/3125:ℝ) = 14*Real.log 2+Real.log (1/12500:ℝ) := by
    rw [show (4096/3125:ℝ)=(2:ℝ)^14*(1/12500:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem family_log_root : Bounds (Real.log (53/200:ℝ)) (-13281/10000:ℝ) (-13279/10000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-3/50:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (53/50:ℝ) = 2*Real.log 2+Real.log (53/200:ℝ) := by
    rw [show (53/50:ℝ)=(2:ℝ)^2*(53/200:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem family_lower_log : Bounds (branchLog familySmallLower) (94334/10000) (94335/10000) := by
  rw [branchLog_eq_neg_log]
  have h := family_log_lower
  norm_num only [familySmallLower]
  constructor <;> linarith [h.1,h.2]

private theorem family_lower_delta : Bounds
    (2*familySmallLower*branchLog familySmallLower/(1-familySmallLower)^2)
    (1509/1000000) (151/100000) := by
  have h := family_lower_log
  norm_num only [familySmallLower] at h ⊢
  constructor <;> linarith [h.1,h.2]

private theorem family_lower_b : Bounds (branchB familySmallLower) (99849/100000) (99850/100000) := by
  have hd := family_lower_delta
  have hlo := Real.exp_bound (x := (-151/100000:ℝ)) (by norm_num) (n := 6) (by norm_num)
  have hhi := Real.exp_bound (x := (-1509/1000000:ℝ)) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hlo hhi
  have hbl := (abs_le.mp hlo).1
  have hbu := (abs_le.mp hhi).2
  have hex : branchB familySmallLower=Real.exp (-(2*familySmallLower*branchLog familySmallLower/(1-familySmallLower)^2)) := by
    unfold branchB
    congr 1
    ring
  have hl := Real.exp_le_exp.mpr (neg_le_neg hd.2)
  have hu := Real.exp_le_exp.mpr (neg_le_neg hd.1)
  rw [←hex] at hl hu
  constructor <;> linarith

private theorem family_lower_mu : Bounds (branchMu familySmallLower) (1892/100) (1893/100) := by
  have hL := family_lower_log
  have hb := family_lower_b
  have hd := ((Bounds.refl (1-familySmallLower)).pow (by norm_num [familySmallLower]) 2).mul_nonneg
    (hb.pow (by norm_num) 2) (by positivity) (by norm_num)
  have hh := ((Bounds.refl (2:ℝ)).mul_nonneg hL (by norm_num) (by norm_num)).div_pos hd
    (by norm_num) (by norm_num [familySmallLower])
  exact hh.weaken (by norm_num [familySmallLower]) (by norm_num [familySmallLower])

private theorem family_lower_triangle : (597/10000000:ℝ)≤
    balancedTriangle (branchA familySmallLower) (branchB familySmallLower) := by
  rw [branch_triangle]
  have h := ((family_lower_b.pow (by norm_num) 3).mul_nonneg
    (Bounds.refl (familySmallLower^3+3*familySmallLower)) (by norm_num) (by norm_num [familySmallLower])).div_pos
    (Bounds.refl (4:ℝ)) (by norm_num [familySmallLower]) (by norm_num)
  exact (show (597/10000000:ℝ)≤_ by norm_num [familySmallLower]).trans h.1

private theorem family_lower_branch_cost :
    balancedPenalty (branchMu familySmallLower/3) (branchA familySmallLower) (branchB familySmallLower)<(5001/10000:ℝ) := by
  have hEL := balancedEL_multiplier_cost (branch_balancedEL (z := familySmallLower)
    (by norm_num [familySmallLower]) (by norm_num [familySmallLower]))
  have hb := family_lower_b.1
  have ha : (99849/100000:ℝ)*familySmallLower≤branchA familySmallLower := by
    unfold branchA
    nlinarith [mul_le_mul_of_nonneg_left hb (by norm_num [familySmallLower] : 0≤familySmallLower)]
  have hm := mul_le_mul family_lower_mu.1 family_lower_triangle (by norm_num : (0:ℝ)≤597/10000000)
    (by linarith [family_lower_mu.1] : 0≤branchMu familySmallLower)
  unfold balancedPenalty
  norm_num only [familySmallLower] at *
  nlinarith

private theorem family_lower_root_upper :
    constantRoot (branchMu familySmallLower/3)<(53/200:ℝ) := by
  have hμ := family_lower_mu
  have hγ : 0<branchMu familySmallLower/3 := by linarith [hμ.1]
  have hc := constantRoot_spec hγ
  have hpos : 0<constantEquation (branchMu familySmallLower/3) (53/200) := by
    unfold constantEquation
    have hl := family_log_root.1
    nlinarith [hμ.1]
  by_contra hn
  have hh := (constantEquation_strictMono hγ.le).monotoneOn
    (by norm_num : (53/200:ℝ)∈Ioi (0:ℝ)) hc.1.1 (le_of_not_gt hn)
  rw [hc.2] at hh
  linarith

private theorem family_lower_constant_cost : (5001/10000:ℝ)<
    constantPenalty (branchMu familySmallLower/3) (constantRoot (branchMu familySmallLower/3)) := by
  let c := constantRoot (branchMu familySmallLower/3)
  have hμ := family_lower_mu
  have hγ : 0<branchMu familySmallLower/3 := by linarith [hμ.1]
  have hc := constantRoot_spec hγ
  have hcu : c≤(53/200:ℝ) := family_lower_root_upper.le
  have hcb : Bounds c 0 (53/200) := ⟨hc.1.1.le,hcu⟩
  have hprod := hμ.mul_nonneg (hcb.pow (by norm_num) 3) (by norm_num) (by norm_num)
  have he : constantPenalty (branchMu familySmallLower/3) c=
      1-c-2*branchMu familySmallLower*c^3/3 := by
    have hr := hc.2
    change Real.log c+3*(branchMu familySmallLower/3)*c^2=0 at hr
    have hl : Real.log c= -branchMu familySmallLower*c^2 := by linarith
    unfold constantPenalty entropy
    rw [hl]
    ring
  change (5001/10000:ℝ)<constantPenalty (branchMu familySmallLower/3) c
  rw [he]
  nlinarith [hprod.2]

theorem penalizedGap_familySmallLower_neg : penalizedGap familySmallLower<0 := by
  rw [penalizedGap_eq (by norm_num [familySmallLower])]
  linarith [family_lower_branch_cost,family_lower_constant_cost]

/-- A sufficient lower crossing bracket; not the full printed penconstants. -/
theorem familySmallLower_lt_penalizedCrossing : familySmallLower<penalizedCrossing := by
  rcases lt_trichotomy familySmallLower penalizedCrossing with h|h|h
  · exact h
  · have hh := penalizedGap_familySmallLower_neg
    rw [h,penalizedCrossing_spec.2] at hh
    linarith
  · have hh := penalizedGap_pos_after_open ⟨h,
      lt_trans (by norm_num [familySmallLower] : familySmallLower<(1/1000:ℝ)) foldPoint_bounds.1⟩
    linarith [penalizedGap_familySmallLower_neg]

theorem penalizedCrossing_log_lt_nineteen_halves : branchLog penalizedCrossing<(19/2:ℝ) := by
  have h := Real.log_lt_log (by norm_num [familySmallLower] : 0<familySmallLower)
    familySmallLower_lt_penalizedCrossing
  have hL := family_lower_log.2
  rw [branchLog_eq_neg_log] at hL ⊢
  linarith

theorem transitionParameter_log_gt_thirtynine_tenths :
    (39/10:ℝ)<branchLog transitionParameter := by
  have h := digit_log_range ⟨transitionParameter_digits.1.le,transitionParameter_digits.2.le⟩
  linarith [h.1]

/-- Monotonicity identifies both endpoints of the actual intermediate family. -/
theorem middle_branch_parameter_bounds {r : ℝ} (hr : r∈Icc smallTarget threshold) :
    leftBranch r∈Icc penalizedCrossing transitionParameter := by
  have htspin : threshold<spinodalValue := by
    rw [threshold_eq_transitionTarget]
    exact transitionTarget_spec.1.2
  have hrs : r∈Icc (0:ℝ) spinodalValue :=
    ⟨smallTarget_mem_unit.1.le.trans hr.1,hr.2.trans htspin.le⟩
  have hsmall : smallTarget∈Icc (0:ℝ) spinodalValue :=
    ⟨smallTarget_mem_unit.1.le,smallTarget_lt_threshold.le.trans htspin.le⟩
  have hthresh : threshold∈Icc (0:ℝ) spinodalValue := ⟨threshold_mem_Ioo.1.le,htspin.le⟩
  have hlo := strictMonoOn_leftBranch.monotoneOn hsmall hrs hr.1
  have hhi := strictMonoOn_leftBranch.monotoneOn hrs hthresh hr.2
  rw [leftBranch_smallTarget] at hlo
  have he : leftBranch threshold=transitionParameter := by rw [threshold_eq_transitionTarget]; rfl
  rw [he] at hhi
  exact ⟨hlo,hhi⟩

/-- The logarithmic family domain, derived entirely from proved scalar facts. -/
theorem middle_branch_log_range {r : ℝ} (hr : r∈Icc smallTarget threshold) :
    branchLog (leftBranch r)∈Icc (39/10:ℝ) (19/2) := by
  have hp := middle_branch_parameter_bounds hr
  have hz : 0<leftBranch r := penalizedCrossing_spec.1.1.trans_le hp.1
  have hlo := Real.log_le_log hz hp.2
  have hhi := Real.log_le_log penalizedCrossing_spec.1.1 hp.1
  have hzc := penalizedCrossing_log_lt_nineteen_halves
  have htr := transitionParameter_log_gt_thirtynine_tenths
  simp only [branchLog_eq_neg_log] at hzc htr ⊢
  constructor <;> linarith

end SparseLowerTail.Section08

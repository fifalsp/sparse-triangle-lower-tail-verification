import SparseLowerTail.Section07.PenalizedCrossing
import SparseLowerTail.Numerics.IntervalArithmetic

/-! Coarse crossing bracket for lem:smallparams. Generated exact numerical
proposals are checked using proved logarithm/exponential Taylor estimates. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04 Numerics

def smallParameterUpper : ℝ := 209/2500000
theorem smallUpper_log : Bounds (-Real.log (209/2500000 : ℝ)) (586841689867/62500000000 : ℝ) (75115736303/8000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-28883/78125 : ℝ)) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (107008/78125 : ℝ) = 14*Real.log 2 + Real.log (209/2500000 : ℝ) := by
    rw [show (107008/78125 : ℝ) = (2:ℝ)^14*(209/2500000 : ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem smallUpper_trial_log : Bounds (-Real.log (5307/20000 : ℝ)) (1326705569707/1000000000000 : ℝ) (132670556971/100000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-307/5000 : ℝ)) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (5307/5000 : ℝ) = 2*Real.log 2 + Real.log (5307/20000 : ℝ) := by
    rw [show (5307/5000 : ℝ) = (2:ℝ)^2*(5307/20000 : ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem smallUpper_exponent : Bounds (2*(209/2500000 : ℝ)*branchLog (209/2500000 : ℝ)/(1-(209/2500000 : ℝ))^2) (122649913182203/78111938046012500 : ℝ) (15699188887327/9998328069889600 : ℝ) := by
  have h := smallUpper_log
  rw [branchLog_eq_neg_log]
  norm_num only [sub_self,one_pow] at *
  constructor <;> norm_num <;> nlinarith [h.1,h.2]

theorem smallUpper_exp_lower : Bounds (Real.exp (-15699188887327/9998328069889600 : ℝ)) (249607762669/250000000000 : ℝ) (998431050679/1000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-15699188887327/9998328069889600 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem smallUpper_exp_upper : Bounds (Real.exp (-122649913182203/78111938046012500 : ℝ)) (249607762669/250000000000 : ℝ) (998431050679/1000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-122649913182203/78111938046012500 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem smallUpper_branchB : Bounds (branchB (209/2500000 : ℝ)) (249607762669/250000000000 : ℝ) (998431050679/1000000000000 : ℝ) := by
  have hE := smallUpper_exponent
  have hlo := Real.exp_le_exp.mpr (neg_le_neg hE.2)
  have hhi := Real.exp_le_exp.mpr (neg_le_neg hE.1)
  have he : branchB (209/2500000 : ℝ)=Real.exp (-(2*(209/2500000 : ℝ)*branchLog (209/2500000 : ℝ)/(1-(209/2500000 : ℝ))^2)) := by unfold branchB; congr 1; ring
  rw [←he] at hlo hhi
  have hbl := smallUpper_exp_lower.1
  have hbu := smallUpper_exp_upper.2
  constructor <;> linarith

theorem smallUpper_trial_gap :
    0< balancedPenalty (branchMu (209/2500000 : ℝ)/3) (branchA (209/2500000 : ℝ)) (branchB (209/2500000 : ℝ))-constantPenalty (branchMu (209/2500000 : ℝ)/3) (5307/20000 : ℝ) := by
  have hL : Bounds (branchLog (209/2500000 : ℝ)) (586841689867/62500000000 : ℝ) (75115736303/8000000000 : ℝ) := by simpa only [branchLog_eq_neg_log] using smallUpper_log
  let v1 : ℝ := (209/2500000 : ℝ)*(branchB (209/2500000 : ℝ))
  have h1 : Bounds v1 (6521/78125000 : ℝ) (834689/10000000000 : ℝ) := by
    exact (Bounds.refl (209/2500000 : ℝ)).mul_corners smallUpper_branchB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v2 : ℝ := v1+(branchB (209/2500000 : ℝ))
  have h2 : Bounds v2 (4992572597/5000000000 : ℝ) (2496286299/2500000000 : ℝ) := by
    exact (h1.add smallUpper_branchB).weaken (by norm_num) (by norm_num)
  let v3 : ℝ := v2/(2 : ℝ)
  have h3 : Bounds v3 (4992572597/10000000000 : ℝ) (2496286299/5000000000 : ℝ) := by
    exact (h2.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v4 : ℝ := (2 : ℝ)*(branchLog (209/2500000 : ℝ))
  have h4 : Bounds v4 (187789340757/10000000000 : ℝ) (93894670379/5000000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hL (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v5 : ℝ := (1 : ℝ)-(209/2500000 : ℝ)
  have h5 : Bounds v5 (2499791/2500000 : ℝ) (2499791/2500000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (209/2500000 : ℝ))).weaken (by norm_num) (by norm_num)
  let v6 : ℝ := v5*v5
  have h6 : Bounds v6 (9998328069/10000000000 : ℝ) (999832807/1000000000 : ℝ) := by
    exact h5.mul_corners h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v7 : ℝ := (branchB (209/2500000 : ℝ))*(branchB (209/2500000 : ℝ))
  have h7 : Bounds v7 (9968645629/10000000000 : ℝ) (996864563/1000000000 : ℝ) := by
    exact smallUpper_branchB.mul_corners smallUpper_branchB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v8 : ℝ := v6*v7
  have h8 : Bounds v8 (498348947/500000000 : ℝ) (9966978943/10000000000 : ℝ) := by
    exact h6.mul_corners h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v9 : ℝ := v4/v8
  have h9 : Bounds v9 (18841149543/1000000000 : ℝ) (2943929617/156250000 : ℝ) := by
    exact (h4.div_pos h8 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v10 : ℝ := v1*v1
  have h10 : Bounds v10 (69/10000000000 : ℝ) (7/1000000000 : ℝ) := by
    exact h1.mul_corners h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v11 : ℝ := v10*v1
  have h11 : Bounds v11 (0 : ℝ) (1/10000000000 : ℝ) := by
    exact h10.mul_corners h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v12 : ℝ := (3 : ℝ)*v1
  have h12 : Bounds v12 (19563/78125000 : ℝ) (2504067/10000000000 : ℝ) := by
    exact (Bounds.refl (3 : ℝ)).mul_corners h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v13 : ℝ := (branchB (209/2500000 : ℝ))*(branchB (209/2500000 : ℝ))
  have h13 : Bounds v13 (9968645629/10000000000 : ℝ) (996864563/1000000000 : ℝ) := by
    exact smallUpper_branchB.mul_corners smallUpper_branchB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v14 : ℝ := v12*v13
  have h14 : Bounds v14 (624053/2500000000 : ℝ) (312027/1250000000 : ℝ) := by
    exact h12.mul_corners h13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v15 : ℝ := v11+v14
  have h15 : Bounds v15 (624053/2500000000 : ℝ) (2496217/10000000000 : ℝ) := by
    exact (h11.add h14).weaken (by norm_num) (by norm_num)
  let v16 : ℝ := v15/(4 : ℝ)
  have h16 : Bounds v16 (624053/10000000000 : ℝ) (124811/2000000000 : ℝ) := by
    exact (h15.div_pos (Bounds.refl (4 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v17 : ℝ := (5307/20000 : ℝ)*(-Real.log (5307/20000 : ℝ))
  have h17 : Bounds v17 (3520413229/10000000000 : ℝ) (352041323/1000000000 : ℝ) := by
    exact (Bounds.refl (5307/20000 : ℝ)).mul_corners smallUpper_trial_log (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v18 : ℝ := (5307/20000 : ℝ)+v17
  have h18 : Bounds v18 (6173913229/10000000000 : ℝ) (617391323/1000000000 : ℝ) := by
    exact ((Bounds.refl (5307/20000 : ℝ)).add h17).weaken (by norm_num) (by norm_num)
  let v19 : ℝ := v18-v3
  have h19 : Bounds v19 (1181340631/10000000000 : ℝ) (1181340633/10000000000 : ℝ) := by
    exact (h18.sub h3).weaken (by norm_num) (by norm_num)
  let v20 : ℝ := (2 : ℝ)*v9
  have h20 : Bounds v20 (18841149543/500000000 : ℝ) (2943929617/78125000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v21 : ℝ := v20*v16
  have h21 : Bounds v21 (23515751/10000000000 : ℝ) (5878957/2500000000 : ℝ) := by
    exact h20.mul_corners h16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v22 : ℝ := v21/(3 : ℝ)
  have h22 : Bounds v22 (7838583/10000000000 : ℝ) (783861/1000000000 : ℝ) := by
    exact (h21.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v23 : ℝ := v19-v22
  have h23 : Bounds v23 (1173502021/10000000000 : ℝ) (23470041/200000000 : ℝ) := by
    exact (h19.sub h22).weaken (by norm_num) (by norm_num)
  let v24 : ℝ := (5307/20000 : ℝ)*(5307/20000 : ℝ)
  have h24 : Bounds v24 (28164249/400000000 : ℝ) (28164249/400000000 : ℝ) := by
    exact (Bounds.refl (5307/20000 : ℝ)).mul_corners (Bounds.refl (5307/20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v25 : ℝ := v24*(5307/20000 : ℝ)
  have h25 : Bounds v25 (93417293/5000000000 : ℝ) (186834587/10000000000 : ℝ) := by
    exact h24.mul_corners (Bounds.refl (5307/20000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v26 : ℝ := v9*v25
  have h26 : Bounds v26 (1760089187/5000000000 : ℝ) (704035679/2000000000 : ℝ) := by
    exact h9.mul_corners h25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v27 : ℝ := v26/(3 : ℝ)
  have h27 : Bounds v27 (1173392791/10000000000 : ℝ) (1173392799/10000000000 : ℝ) := by
    exact (h26.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v28 : ℝ := v23-v27
  have h28 : Bounds v28 (54611/5000000000 : ℝ) (109259/10000000000 : ℝ) := by
    exact (h23.sub h27).weaken (by norm_num) (by norm_num)
  have hv := h28
  have hel := balancedEL_multiplier_cost (branch_balancedEL (z := (209/2500000 : ℝ)) (by norm_num) (by norm_num))
  have he : balancedPenalty (branchMu (209/2500000 : ℝ)/3) (branchA (209/2500000 : ℝ)) (branchB (209/2500000 : ℝ))-constantPenalty (branchMu (209/2500000 : ℝ)/3) (5307/20000 : ℝ) = v28 := by
    dsimp only [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28]
    unfold balancedPenalty constantPenalty entropy
    rw [show balancedCost (branchA (209/2500000 : ℝ)) (branchB (209/2500000 : ℝ))=1-(branchA (209/2500000 : ℝ)+branchB (209/2500000 : ℝ))/2-branchMu (209/2500000 : ℝ)*balancedTriangle (branchA (209/2500000 : ℝ)) (branchB (209/2500000 : ℝ)) by linarith [hel]]
    unfold branchA branchMu balancedTriangle
    ring
  rw [he]
  exact lt_of_lt_of_le (by norm_num) hv.1

theorem penalizedGap_smallUpper_pos : 0<penalizedGap smallParameterUpper := by
  have hz : smallParameterUpper∈Ioo (0:ℝ) 1 := by norm_num [smallParameterUpper]
  have hγ : 0<branchMu smallParameterUpper/3 := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)
  have ht := constantPenalty_min hγ (by norm_num : (5307/20000 : ℝ)∈Icc (0:ℝ) 1)
  rw [penalizedGap_eq hz.1]
  have hg := smallUpper_trial_gap
  norm_num only [smallParameterUpper] at ht ⊢
  linarith

theorem penalizedCrossing_lt_smallUpper : penalizedCrossing<smallParameterUpper := by
  rcases lt_trichotomy penalizedCrossing smallParameterUpper with h | h | h
  · exact h
  · have hh := penalizedGap_smallUpper_pos
    rw [←h,penalizedCrossing_spec.2] at hh
    linarith
  · have hh := penalizedGap_neg_before ⟨by norm_num [smallParameterUpper],h⟩
    linarith [penalizedGap_smallUpper_pos]

end SparseLowerTail.Section07

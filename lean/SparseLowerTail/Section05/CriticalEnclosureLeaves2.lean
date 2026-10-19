import SparseLowerTail.Section05.CriticalEnclosureBounds

/-! Exact one-variable FB1 enclosure leaves. Log Taylor and rational cuberoot
witnesses are checked by the kernel; no numerical evaluator result is assumed. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Section02 Section04 Numerics
set_option maxHeartbeats 800000
set_option maxRecDepth 5000

private theorem enclosureLog_2_0 : Bounds (Real.log (5461/16000:ℝ)) (-10749567991/10000000000:ℝ) (-1074956799/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (2539/8000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5461/8000:ℝ)=1*Real.log 2+Real.log (5461/16000:ℝ) := by
    rw [show (5461/8000:ℝ)=(2:ℝ)^1*(5461/16000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_0 {m : ℝ} (hm : m∈Icc (3301/10000:ℝ) (5461/16000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (747699553/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_0 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5461/16000:ℝ)*(-10749567991/10000000000:ℝ)-(5461/16000:ℝ)+1+
      (((3301/10000:ℝ)-1-(-1074956799/1000000000:ℝ))/(1-(3301/10000:ℝ))^2)*(747699553/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_1 : Bounds (Real.log (14101/40000:ℝ)) (-10426337373/10000000000:ℝ) (-2606584343/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (5899/20000:ℝ)) (by norm_num) 22
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (14101/20000:ℝ)=1*Real.log 2+Real.log (14101/40000:ℝ) := by
    rw [show (14101/20000:ℝ)=(2:ℝ)^1*(14101/40000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_1 {m : ℝ} (hm : m∈Icc (5461/16000:ℝ) (14101/40000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (3125886851/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_1 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (14101/40000:ℝ)*(-10426337373/10000000000:ℝ)-(14101/40000:ℝ)+1+
      (((5461/16000:ℝ)-1-(-2606584343/2500000000:ℝ))/(1-(5461/16000:ℝ))^2)*(3125886851/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_2 : Bounds (Real.log (29099/80000:ℝ)) (-5056614127/5000000000:ℝ) (-10113228253/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (10901/40000:ℝ)) (by norm_num) 21
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (29099/40000:ℝ)=1*Real.log 2+Real.log (29099/80000:ℝ) := by
    rw [show (29099/40000:ℝ)=(2:ℝ)^1*(29099/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_2 {m : ℝ} (hm : m∈Icc (14101/40000:ℝ) (29099/80000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (814578749/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_2 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (29099/80000:ℝ)*(-5056614127/5000000000:ℝ)-(29099/80000:ℝ)+1+
      (((14101/40000:ℝ)-1-(-10113228253/10000000000:ℝ))/(1-(14101/40000:ℝ))^2)*(814578749/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_3 : Bounds (Real.log (7499/20000:ℝ)) (-9809625953/10000000000:ℝ) (-306550811/312500000:ℝ) := by
  have hh := log_taylor_bounds (x := (2501/10000:ℝ)) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (7499/10000:ℝ)=1*Real.log 2+Real.log (7499/20000:ℝ) := by
    rw [show (7499/10000:ℝ)=(2:ℝ)^1*(7499/20000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_3 {m : ℝ} (hm : m∈Icc (29099/80000:ℝ) (7499/20000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (3388511157/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_3 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (7499/20000:ℝ)*(-9809625953/10000000000:ℝ)-(7499/20000:ℝ)+1+
      (((29099/80000:ℝ)-1-(-306550811/312500000:ℝ))/(1-(29099/80000:ℝ))^2)*(3388511157/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_4 : Bounds (Real.log (30893/80000:ℝ)) (-9514970137/10000000000:ℝ) (-1189371267/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (9107/40000:ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (30893/40000:ℝ)=1*Real.log 2+Real.log (30893/80000:ℝ) := by
    rw [show (30893/40000:ℝ)=(2:ℝ)^1*(30893/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_4 {m : ℝ} (hm : m∈Icc (7499/20000:ℝ) (30893/80000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1758407397/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_4 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (30893/80000:ℝ)*(-9514970137/10000000000:ℝ)-(30893/80000:ℝ)+1+
      (((7499/20000:ℝ)-1-(-1189371267/1250000000:ℝ))/(1-(7499/20000:ℝ))^2)*(1758407397/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_5 : Bounds (Real.log (62683/160000:ℝ)) (-1171354421/1250000000:ℝ) (-9370835367/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (17317/80000:ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (62683/80000:ℝ)=1*Real.log 2+Real.log (62683/160000:ℝ) := by
    rw [show (62683/80000:ℝ)=(2:ℝ)^1*(62683/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_5 {m : ℝ} (hm : m∈Icc (30893/80000:ℝ) (62683/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (3643498911/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_5 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (62683/160000:ℝ)*(-1171354421/1250000000:ℝ)-(62683/160000:ℝ)+1+
      (((30893/80000:ℝ)-1-(-9370835367/10000000000:ℝ))/(1-(30893/80000:ℝ))^2)*(3643498911/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_6 : Bounds (Real.log (3179/8000:ℝ)) (-4614374299/5000000000:ℝ) (-9228748597/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (821/4000:ℝ)) (by norm_num) 17
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (3179/4000:ℝ)=1*Real.log 2+Real.log (3179/8000:ℝ) := by
    rw [show (3179/4000:ℝ)=(2:ℝ)^1*(3179/8000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_6 {m : ℝ} (hm : m∈Icc (62683/160000:ℝ) (3179/8000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (3706304799/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_6 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (3179/8000:ℝ)*(-4614374299/5000000000:ℝ)-(3179/8000:ℝ)+1+
      (((62683/160000:ℝ)-1-(-9228748597/10000000000:ℝ))/(1-(62683/160000:ℝ))^2)*(3706304799/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_7 : Bounds (Real.log (64477/160000:ℝ)) (-4544326221/5000000000:ℝ) (-9088652441/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (15523/80000:ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (64477/80000:ℝ)=1*Real.log 2+Real.log (64477/160000:ℝ) := by
    rw [show (64477/80000:ℝ)=(2:ℝ)^1*(64477/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_7 {m : ℝ} (hm : m∈Icc (3179/8000:ℝ) (64477/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (3768785941/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_7 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (64477/160000:ℝ)*(-4544326221/5000000000:ℝ)-(64477/160000:ℝ)+1+
      (((3179/8000:ℝ)-1-(-9088652441/10000000000:ℝ))/(1-(3179/8000:ℝ))^2)*(3768785941/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_8 : Bounds (Real.log (32687/80000:ℝ)) (-4475245947/5000000000:ℝ) (-8950491893/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (7313/40000:ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (32687/40000:ℝ)=1*Real.log 2+Real.log (32687/80000:ℝ) := by
    rw [show (32687/40000:ℝ)=(2:ℝ)^1*(32687/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_8 {m : ℝ} (hm : m∈Icc (64477/160000:ℝ) (32687/80000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (3830964111/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_8 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (32687/80000:ℝ)*(-4475245947/5000000000:ℝ)-(32687/80000:ℝ)+1+
      (((64477/160000:ℝ)-1-(-8950491893/10000000000:ℝ))/(1-(64477/160000:ℝ))^2)*(3830964111/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_9 : Bounds (Real.log (66271/160000:ℝ)) (-1762842839/2000000000:ℝ) (-4407107097/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (13729/80000:ℝ)) (by norm_num) 15
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (66271/80000:ℝ)=1*Real.log 2+Real.log (66271/160000:ℝ) := by
    rw [show (66271/80000:ℝ)=(2:ℝ)^1*(66271/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_9 {m : ℝ} (hm : m∈Icc (32687/80000:ℝ) (66271/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (3892859179/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_9 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (66271/160000:ℝ)*(-1762842839/2000000000:ℝ)-(66271/160000:ℝ)+1+
      (((32687/80000:ℝ)-1-(-4407107097/5000000000:ℝ))/(1-(32687/80000:ℝ))^2)*(3892859179/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_10 : Bounds (Real.log (2099/5000:ℝ)) (-2169942179/2500000000:ℝ) (-1735953743/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (401/2500:ℝ)) (by norm_num) 15
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2099/2500:ℝ)=1*Real.log 2+Real.log (2099/5000:ℝ) := by
    rw [show (2099/2500:ℝ)=(2:ℝ)^1*(2099/5000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_10 {m : ℝ} (hm : m∈Icc (66271/160000:ℝ) (2099/5000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1977244659/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_10 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2099/5000:ℝ)*(-2169942179/2500000000:ℝ)-(2099/5000:ℝ)+1+
      (((66271/160000:ℝ)-1-(-1735953743/2000000000:ℝ))/(1-(66271/160000:ℝ))^2)*(1977244659/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_11 : Bounds (Real.log (13613/32000:ℝ)) (-8547106843/10000000000:ℝ) (-4273553421/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (2387/16000:ℝ)) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (13613/16000:ℝ)=1*Real.log 2+Real.log (13613/32000:ℝ) := by
    rw [show (13613/16000:ℝ)=(2:ℝ)^1*(13613/32000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_11 {m : ℝ} (hm : m∈Icc (2099/5000:ℝ) (13613/32000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2007935591/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_11 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (13613/32000:ℝ)*(-8547106843/10000000000:ℝ)-(13613/32000:ℝ)+1+
      (((2099/5000:ℝ)-1-(-4273553421/5000000000:ℝ))/(1-(2099/5000:ℝ))^2)*(2007935591/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_12 : Bounds (Real.log (137027/320000:ℝ)) (-8481430091/10000000000:ℝ) (-848143009/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (22973/160000:ℝ)) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (137027/160000:ℝ)=1*Real.log 2+Real.log (137027/320000:ℝ) := by
    rw [show (137027/160000:ℝ)=(2:ℝ)^1*(137027/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_12 {m : ℝ} (hm : m∈Icc (13613/32000:ℝ) (137027/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4077020069/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_12 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (137027/320000:ℝ)*(-8481430091/10000000000:ℝ)-(137027/320000:ℝ)+1+
      (((13613/32000:ℝ)-1-(-848143009/1000000000:ℝ))/(1-(13613/32000:ℝ))^2)*(4077020069/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_13 : Bounds (Real.log (34481/80000:ℝ)) (-841618187/1000000000:ℝ) (-8416181869/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (5519/40000:ℝ)) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (34481/40000:ℝ)=1*Real.log 2+Real.log (34481/80000:ℝ) := by
    rw [show (34481/40000:ℝ)=(2:ℝ)^1*(34481/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_13 {m : ℝ} (hm : m∈Icc (137027/320000:ℝ) (34481/80000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1026877897/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_13 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (34481/80000:ℝ)*(-841618187/1000000000:ℝ)-(34481/80000:ℝ)+1+
      (((137027/320000:ℝ)-1-(-8416181869/10000000000:ℝ))/(1-(137027/320000:ℝ))^2)*(1026877897/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_14 : Bounds (Real.log (138821/320000:ℝ)) (-521959789/625000000:ℝ) (-8351356623/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (21179/160000:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (138821/160000:ℝ)=1*Real.log 2+Real.log (138821/320000:ℝ) := by
    rw [show (138821/160000:ℝ)=(2:ℝ)^1*(138821/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_14 {m : ℝ} (hm : m∈Icc (34481/80000:ℝ) (138821/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1034487513/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_14 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (138821/320000:ℝ)*(-521959789/625000000:ℝ)-(138821/320000:ℝ)+1+
      (((34481/80000:ℝ)-1-(-8351356623/10000000000:ℝ))/(1-(34481/80000:ℝ))^2)*(1034487513/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_15 : Bounds (Real.log (69859/160000:ℝ)) (-1035868613/1250000000:ℝ) (-8286948903/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (10141/80000:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (69859/80000:ℝ)=1*Real.log 2+Real.log (69859/160000:ℝ) := by
    rw [show (69859/80000:ℝ)=(2:ℝ)^1*(69859/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_15 {m : ℝ} (hm : m∈Icc (138821/320000:ℝ) (69859/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4168337049/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_15 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (69859/160000:ℝ)*(-1035868613/1250000000:ℝ)-(69859/160000:ℝ)+1+
      (((138821/320000:ℝ)-1-(-8286948903/10000000000:ℝ))/(1-(138821/320000:ℝ))^2)*(4168337049/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_16 : Bounds (Real.log (28123/64000:ℝ)) (-1644590673/2000000000:ℝ) (-2055738341/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3877/32000:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (28123/32000:ℝ)=1*Real.log 2+Real.log (28123/64000:ℝ) := by
    rw [show (28123/32000:ℝ)=(2:ℝ)^1*(28123/64000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_16 {m : ℝ} (hm : m∈Icc (69859/160000:ℝ) (28123/64000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (839734821/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_16 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (28123/64000:ℝ)*(-1644590673/2000000000:ℝ)-(28123/64000:ℝ)+1+
      (((69859/160000:ℝ)-1-(-2055738341/2500000000:ℝ))/(1-(69859/160000:ℝ))^2)*(839734821/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_17 : Bounds (Real.log (17689/40000:ℝ)) (-8159364767/10000000000:ℝ) (-4079682383/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (2311/20000:ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (17689/20000:ℝ)=1*Real.log 2+Real.log (17689/40000:ℝ) := by
    rw [show (17689/20000:ℝ)=(2:ℝ)^1*(17689/40000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_17 {m : ℝ} (hm : m∈Icc (28123/64000:ℝ) (17689/40000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (33038771/78125000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_17 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (17689/40000:ℝ)*(-8159364767/10000000000:ℝ)-(17689/40000:ℝ)+1+
      (((28123/64000:ℝ)-1-(-4079682383/5000000000:ℝ))/(1-(28123/64000:ℝ))^2)*(33038771/78125000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_18 : Bounds (Real.log (142409/320000:ℝ)) (-4048088983/5000000000:ℝ) (-1619235593/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (17591/160000:ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (142409/160000:ℝ)=1*Real.log 2+Real.log (142409/320000:ℝ) := by
    rw [show (142409/160000:ℝ)=(2:ℝ)^1*(142409/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_18 {m : ℝ} (hm : m∈Icc (17689/40000:ℝ) (142409/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (266200263/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_18 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (142409/320000:ℝ)*(-4048088983/5000000000:ℝ)-(142409/320000:ℝ)+1+
      (((17689/40000:ℝ)-1-(-1619235593/2000000000:ℝ))/(1-(17689/40000:ℝ))^2)*(266200263/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_19 : Bounds (Real.log (71653/160000:ℝ)) (-8033387917/10000000000:ℝ) (-2008346979/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (8347/80000:ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (71653/80000:ℝ)=1*Real.log 2+Real.log (71653/160000:ℝ) := by
    rw [show (71653/80000:ℝ)=(2:ℝ)^1*(71653/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_19 {m : ℝ} (hm : m∈Icc (142409/320000:ℝ) (71653/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4289400023/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_19 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (71653/160000:ℝ)*(-8033387917/10000000000:ℝ)-(71653/160000:ℝ)+1+
      (((142409/320000:ℝ)-1-(-2008346979/2500000000:ℝ))/(1-(142409/320000:ℝ))^2)*(4289400023/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_20 : Bounds (Real.log (144203/320000:ℝ)) (-1992747417/2500000000:ℝ) (-7970989667/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (15797/160000:ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (144203/160000:ℝ)=1*Real.log 2+Real.log (144203/320000:ℝ) := by
    rw [show (144203/160000:ℝ)=(2:ℝ)^1*(144203/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_20 {m : ℝ} (hm : m∈Icc (71653/160000:ℝ) (144203/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4319551439/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_20 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (144203/320000:ℝ)*(-1992747417/2500000000:ℝ)-(144203/320000:ℝ)+1+
      (((71653/160000:ℝ)-1-(-7970989667/10000000000:ℝ))/(1-(71653/160000:ℝ))^2)*(4319551439/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_21 : Bounds (Real.log (1451/3200:ℝ)) (-197724459/250000000:ℝ) (-7908978359/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (149/1600:ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1451/1600:ℝ)=1*Real.log 2+Real.log (1451/3200:ℝ) := by
    rw [show (1451/1600:ℝ)=(2:ℝ)^1*(1451/3200:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_21 {m : ℝ} (hm : m∈Icc (144203/320000:ℝ) (1451/3200:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1087414929/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_21 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1451/3200:ℝ)*(-197724459/250000000:ℝ)-(1451/3200:ℝ)+1+
      (((144203/320000:ℝ)-1-(-7908978359/10000000000:ℝ))/(1-(144203/320000:ℝ))^2)*(1087414929/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_22 : Bounds (Real.log (145997/320000:ℝ)) (-7847349223/10000000000:ℝ) (-3923674611/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (14003/160000:ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (145997/160000:ℝ)=1*Real.log 2+Real.log (145997/320000:ℝ) := by
    rw [show (145997/160000:ℝ)=(2:ℝ)^1*(145997/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_22 {m : ℝ} (hm : m∈Icc (1451/3200:ℝ) (145997/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (273732879/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_22 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (145997/320000:ℝ)*(-7847349223/10000000000:ℝ)-(145997/320000:ℝ)+1+
      (((1451/3200:ℝ)-1-(-3923674611/5000000000:ℝ))/(1-(1451/3200:ℝ))^2)*(273732879/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_23 : Bounds (Real.log (292891/640000:ℝ)) (-7816676503/10000000000:ℝ) (-3908338251/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (27109/320000:ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (292891/320000:ℝ)=1*Real.log 2+Real.log (292891/640000:ℝ) := by
    rw [show (292891/320000:ℝ)=(2:ℝ)^1*(292891/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_23 {m : ℝ} (hm : m∈Icc (145997/320000:ℝ) (292891/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1102437913/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_23 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (292891/640000:ℝ)*(-7816676503/10000000000:ℝ)-(292891/640000:ℝ)+1+
      (((145997/320000:ℝ)-1-(-3908338251/5000000000:ℝ))/(1-(145997/320000:ℝ))^2)*(1102437913/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_24 : Bounds (Real.log (73447/160000:ℝ)) (-973262197/1250000000:ℝ) (-311443903/400000000:ℝ) := by
  have hh := log_taylor_bounds (x := (6553/80000:ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (73447/80000:ℝ)=1*Real.log 2+Real.log (73447/160000:ℝ) := by
    rw [show (73447/80000:ℝ)=(2:ℝ)^1*(73447/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_24 {m : ℝ} (hm : m∈Icc (292891/640000:ℝ) (73447/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2212374757/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_24 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (73447/160000:ℝ)*(-973262197/1250000000:ℝ)-(73447/160000:ℝ)+1+
      (((292891/640000:ℝ)-1-(-311443903/400000000:ℝ))/(1-(292891/640000:ℝ))^2)*(2212374757/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_25 : Bounds (Real.log (58937/128000:ℝ)) (-242362871/312500000:ℝ) (-7755611871/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (5063/64000:ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (58937/64000:ℝ)=1*Real.log 2+Real.log (58937/128000:ℝ) := by
    rw [show (58937/64000:ℝ)=(2:ℝ)^1*(58937/128000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_25 {m : ℝ} (hm : m∈Icc (73447/160000:ℝ) (58937/128000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1109934401/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_25 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (58937/128000:ℝ)*(-242362871/312500000:ℝ)-(58937/128000:ℝ)+1+
      (((73447/160000:ℝ)-1-(-7755611871/10000000000:ℝ))/(1-(73447/160000:ℝ))^2)*(1109934401/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_26 : Bounds (Real.log (147791/320000:ℝ)) (-7725218823/10000000000:ℝ) (-3862609411/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (12209/160000:ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (147791/160000:ℝ)=1*Real.log 2+Real.log (147791/320000:ℝ) := by
    rw [show (147791/160000:ℝ)=(2:ℝ)^1*(147791/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_26 {m : ℝ} (hm : m∈Icc (58937/128000:ℝ) (147791/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2227358029/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_26 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (147791/320000:ℝ)*(-7725218823/10000000000:ℝ)-(147791/320000:ℝ)+1+
      (((58937/128000:ℝ)-1-(-3862609411/5000000000:ℝ))/(1-(58937/128000:ℝ))^2)*(2227358029/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_27 : Bounds (Real.log (296479/640000:ℝ)) (-1923729467/2500000000:ℝ) (-7694917867/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (23521/320000:ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (296479/320000:ℝ)=1*Real.log 2+Real.log (296479/640000:ℝ) := by
    rw [show (296479/320000:ℝ)=(2:ℝ)^1*(296479/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_27 {m : ℝ} (hm : m∈Icc (147791/320000:ℝ) (296479/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2234842503/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_27 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (296479/640000:ℝ)*(-1923729467/2500000000:ℝ)-(296479/640000:ℝ)+1+
      (((147791/320000:ℝ)-1-(-7694917867/10000000000:ℝ))/(1-(147791/320000:ℝ))^2)*(2234842503/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_28 : Bounds (Real.log (9293/20000:ℝ)) (-153294169/200000000:ℝ) (-7664708449/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (707/10000:ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (9293/10000:ℝ)=1*Real.log 2+Real.log (9293/20000:ℝ) := by
    rw [show (9293/10000:ℝ)=(2:ℝ)^1*(9293/20000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_28 {m : ℝ} (hm : m∈Icc (296479/640000:ℝ) (9293/20000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4484644579/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_28 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (9293/20000:ℝ)*(-153294169/200000000:ℝ)-(9293/20000:ℝ)+1+
      (((296479/640000:ℝ)-1-(-7664708449/10000000000:ℝ))/(1-(296479/640000:ℝ))^2)*(4484644579/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_29 : Bounds (Real.log (298273/640000:ℝ)) (-7634590019/10000000000:ℝ) (-3817295009/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (21727/320000:ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (298273/320000:ℝ)=1*Real.log 2+Real.log (298273/640000:ℝ) := by
    rw [show (298273/320000:ℝ)=(2:ℝ)^1*(298273/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_29 {m : ℝ} (hm : m∈Icc (9293/20000:ℝ) (298273/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (899918981/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_29 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (298273/640000:ℝ)*(-7634590019/10000000000:ℝ)-(298273/640000:ℝ)+1+
      (((9293/20000:ℝ)-1-(-3817295009/5000000000:ℝ))/(1-(9293/20000:ℝ))^2)*(899918981/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_30 : Bounds (Real.log (29917/64000:ℝ)) (-7604562027/10000000000:ℝ) (-3802281013/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (2083/32000:ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (29917/32000:ℝ)=1*Real.log 2+Real.log (29917/64000:ℝ) := by
    rw [show (29917/32000:ℝ)=(2:ℝ)^1*(29917/64000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_30 {m : ℝ} (hm : m∈Icc (298273/640000:ℝ) (29917/64000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4514536107/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_30 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (29917/64000:ℝ)*(-7604562027/10000000000:ℝ)-(29917/64000:ℝ)+1+
      (((298273/640000:ℝ)-1-(-3802281013/5000000000:ℝ))/(1-(298273/640000:ℝ))^2)*(4514536107/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_31 : Bounds (Real.log (300067/640000:ℝ)) (-3787311967/5000000000:ℝ) (-1893655983/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (19933/320000:ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (300067/320000:ℝ)=1*Real.log 2+Real.log (300067/640000:ℝ) := by
    rw [show (300067/320000:ℝ)=(2:ℝ)^1*(300067/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_31 {m : ℝ} (hm : m∈Icc (29917/64000:ℝ) (300067/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (452946831/1000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_31 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (300067/640000:ℝ)*(-3787311967/5000000000:ℝ)-(300067/640000:ℝ)+1+
      (((29917/64000:ℝ)-1-(-1893655983/2500000000:ℝ))/(1-(29917/64000:ℝ))^2)*(452946831/1000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_32 : Bounds (Real.log (75241/160000:ℝ)) (-7544775201/10000000000:ℝ) (-9430969/12500000:ℝ) := by
  have hh := log_taylor_bounds (x := (4759/80000:ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (75241/80000:ℝ)=1*Real.log 2+Real.log (75241/160000:ℝ) := by
    rw [show (75241/80000:ℝ)=(2:ℝ)^1*(75241/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_32 {m : ℝ} (hm : m∈Icc (300067/640000:ℝ) (75241/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2272195817/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_32 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (75241/160000:ℝ)*(-7544775201/10000000000:ℝ)-(75241/160000:ℝ)+1+
      (((300067/640000:ℝ)-1-(-9430969/12500000:ℝ))/(1-(300067/640000:ℝ))^2)*(2272195817/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_33 : Bounds (Real.log (301861/640000:ℝ)) (-7515015299/10000000000:ℝ) (-3757507649/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (18139/320000:ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (301861/320000:ℝ)=1*Real.log 2+Real.log (301861/640000:ℝ) := by
    rw [show (301861/320000:ℝ)=(2:ℝ)^1*(301861/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_33 {m : ℝ} (hm : m∈Icc (75241/160000:ℝ) (301861/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1139826549/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_33 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (301861/640000:ℝ)*(-7515015299/10000000000:ℝ)-(301861/640000:ℝ)+1+
      (((75241/160000:ℝ)-1-(-3757507649/5000000000:ℝ))/(1-(75241/160000:ℝ))^2)*(1139826549/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_34 : Bounds (Real.log (151379/320000:ℝ)) (-7485343699/10000000000:ℝ) (-3742671849/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (8621/160000:ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (151379/160000:ℝ)=1*Real.log 2+Real.log (151379/320000:ℝ) := by
    rw [show (151379/160000:ℝ)=(2:ℝ)^1*(151379/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_34 {m : ℝ} (hm : m∈Icc (301861/640000:ℝ) (151379/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1143553029/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_34 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (151379/320000:ℝ)*(-7485343699/10000000000:ℝ)-(151379/320000:ℝ)+1+
      (((301861/640000:ℝ)-1-(-3742671849/5000000000:ℝ))/(1-(301861/640000:ℝ))^2)*(1143553029/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_35 : Bounds (Real.log (60731/128000:ℝ)) (-7455759879/10000000000:ℝ) (-3727879939/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3269/64000:ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (60731/64000:ℝ)=1*Real.log 2+Real.log (60731/128000:ℝ) := by
    rw [show (60731/64000:ℝ)=(2:ℝ)^1*(60731/128000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_35 {m : ℝ} (hm : m∈Icc (151379/320000:ℝ) (60731/128000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (917821901/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_35 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (60731/128000:ℝ)*(-7455759879/10000000000:ℝ)-(60731/128000:ℝ)+1+
      (((151379/320000:ℝ)-1-(-3727879939/5000000000:ℝ))/(1-(151379/320000:ℝ))^2)*(917821901/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_36 : Bounds (Real.log (38069/80000:ℝ)) (-7426263321/10000000000:ℝ) (-185656583/250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (1931/40000:ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (38069/40000:ℝ)=1*Real.log 2+Real.log (38069/80000:ℝ) := by
    rw [show (38069/40000:ℝ)=(2:ℝ)^1*(38069/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_36 {m : ℝ} (hm : m∈Icc (60731/128000:ℝ) (38069/80000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2301999239/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_36 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (38069/80000:ℝ)*(-7426263321/10000000000:ℝ)-(38069/80000:ℝ)+1+
      (((60731/128000:ℝ)-1-(-185656583/250000000:ℝ))/(1-(60731/128000:ℝ))^2)*(2301999239/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_37 : Bounds (Real.log (305449/640000:ℝ)) (-924606689/1250000000:ℝ) (-7396853511/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (14551/320000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (305449/320000:ℝ)=1*Real.log 2+Real.log (305449/640000:ℝ) := by
    rw [show (305449/320000:ℝ)=(2:ℝ)^1*(305449/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_37 {m : ℝ} (hm : m∈Icc (38069/80000:ℝ) (305449/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (923775829/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_37 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (305449/640000:ℝ)*(-924606689/1250000000:ℝ)-(305449/640000:ℝ)+1+
      (((38069/80000:ℝ)-1-(-7396853511/10000000000:ℝ))/(1-(38069/80000:ℝ))^2)*(923775829/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_38 : Bounds (Real.log (122359/256000:ℝ)) (-7382180979/10000000000:ℝ) (-3691090489/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (5641/128000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (122359/128000:ℝ)=1*Real.log 2+Real.log (122359/256000:ℝ) := by
    rw [show (122359/128000:ℝ)=(2:ℝ)^1*(122359/256000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_38 {m : ℝ} (hm : m∈Icc (305449/640000:ℝ) (122359/256000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (926750323/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_38 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (122359/256000:ℝ)*(-7382180979/10000000000:ℝ)-(122359/256000:ℝ)+1+
      (((305449/640000:ℝ)-1-(-3691090489/5000000000:ℝ))/(1-(305449/640000:ℝ))^2)*(926750323/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_39 : Bounds (Real.log (153173/320000:ℝ)) (-7367529943/10000000000:ℝ) (-3683764971/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (6827/160000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (153173/160000:ℝ)=1*Real.log 2+Real.log (153173/320000:ℝ) := by
    rw [show (153173/160000:ℝ)=(2:ℝ)^1*(153173/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_39 {m : ℝ} (hm : m∈Icc (122359/256000:ℝ) (153173/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4641184809/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_39 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (153173/320000:ℝ)*(-7367529943/10000000000:ℝ)-(153173/320000:ℝ)+1+
      (((122359/256000:ℝ)-1-(-3683764971/5000000000:ℝ))/(1-(122359/256000:ℝ))^2)*(4641184809/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_40 : Bounds (Real.log (613589/1280000:ℝ)) (-7352900341/10000000000:ℝ) (-367645017/500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (26411/640000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (613589/640000:ℝ)=1*Real.log 2+Real.log (613589/1280000:ℝ) := by
    rw [show (613589/640000:ℝ)=(2:ℝ)^1*(613589/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_40 {m : ℝ} (hm : m∈Icc (153173/320000:ℝ) (613589/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2324307997/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_40 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (613589/1280000:ℝ)*(-7352900341/10000000000:ℝ)-(613589/1280000:ℝ)+1+
      (((153173/320000:ℝ)-1-(-367645017/500000000:ℝ))/(1-(153173/320000:ℝ))^2)*(2324307997/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_41 : Bounds (Real.log (307243/640000:ℝ)) (-733829211/1000000000:ℝ) (-7338292109/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (12757/320000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (307243/320000:ℝ)=1*Real.log 2+Real.log (307243/640000:ℝ) := by
    rw [show (307243/320000:ℝ)=(2:ℝ)^1*(307243/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_41 {m : ℝ} (hm : m∈Icc (613589/1280000:ℝ) (307243/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4656045183/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_41 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (307243/640000:ℝ)*(-733829211/1000000000:ℝ)-(307243/640000:ℝ)+1+
      (((613589/1280000:ℝ)-1-(-7338292109/10000000000:ℝ))/(1-(613589/1280000:ℝ))^2)*(4656045183/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_42 : Bounds (Real.log (615383/1280000:ℝ)) (-1830926297/2500000000:ℝ) (-7323705187/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (24617/640000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (615383/640000:ℝ)=1*Real.log 2+Real.log (615383/1280000:ℝ) := by
    rw [show (615383/640000:ℝ)=(2:ℝ)^1*(615383/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_42 {m : ℝ} (hm : m∈Icc (307243/640000:ℝ) (615383/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1165868097/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_42 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (615383/1280000:ℝ)*(-1830926297/2500000000:ℝ)-(615383/1280000:ℝ)+1+
      (((307243/640000:ℝ)-1-(-7323705187/10000000000:ℝ))/(1-(307243/640000:ℝ))^2)*(1165868097/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_43 : Bounds (Real.log (15407/32000:ℝ)) (-7309139513/10000000000:ℝ) (-7309139511/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (593/16000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (15407/16000:ℝ)=1*Real.log 2+Real.log (15407/32000:ℝ) := by
    rw [show (15407/16000:ℝ)=(2:ℝ)^1*(15407/32000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_43 {m : ℝ} (hm : m∈Icc (615383/1280000:ℝ) (15407/32000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4670897623/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_43 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (15407/32000:ℝ)*(-7309139513/10000000000:ℝ)-(15407/32000:ℝ)+1+
      (((615383/1280000:ℝ)-1-(-7309139511/10000000000:ℝ))/(1-(615383/1280000:ℝ))^2)*(4670897623/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_44 : Bounds (Real.log (617177/1280000:ℝ)) (-3647297511/5000000000:ℝ) (-7294595021/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (22823/640000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (617177/640000:ℝ)=1*Real.log 2+Real.log (617177/1280000:ℝ) := by
    rw [show (617177/640000:ℝ)=(2:ℝ)^1*(617177/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_44 {m : ℝ} (hm : m∈Icc (15407/32000:ℝ) (617177/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4678320901/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_44 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (617177/1280000:ℝ)*(-3647297511/5000000000:ℝ)-(617177/1280000:ℝ)+1+
      (((15407/32000:ℝ)-1-(-7294595021/10000000000:ℝ))/(1-(15407/32000:ℝ))^2)*(4678320901/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_45 : Bounds (Real.log (309037/640000:ℝ)) (-910008957/1250000000:ℝ) (-1456014331/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (10963/320000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (309037/320000:ℝ)=1*Real.log 2+Real.log (309037/640000:ℝ) := by
    rw [show (309037/320000:ℝ)=(2:ℝ)^1*(309037/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_45 {m : ℝ} (hm : m∈Icc (617177/1280000:ℝ) (309037/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4685742233/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_45 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (309037/640000:ℝ)*(-910008957/1250000000:ℝ)-(309037/640000:ℝ)+1+
      (((617177/1280000:ℝ)-1-(-1456014331/2000000000:ℝ))/(1-(617177/1280000:ℝ))^2)*(4685742233/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_46 : Bounds (Real.log (618971/1280000:ℝ)) (-7265569351/10000000000:ℝ) (-145311387/200000000:ℝ) := by
  have hh := log_taylor_bounds (x := (21029/640000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (618971/640000:ℝ)=1*Real.log 2+Real.log (618971/1280000:ℝ) := by
    rw [show (618971/640000:ℝ)=(2:ℝ)^1*(618971/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_46 {m : ℝ} (hm : m∈Icc (309037/640000:ℝ) (618971/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4693161633/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_46 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (618971/1280000:ℝ)*(-7265569351/10000000000:ℝ)-(618971/1280000:ℝ)+1+
      (((309037/640000:ℝ)-1-(-145311387/200000000:ℝ))/(1-(309037/640000:ℝ))^2)*(4693161633/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_47 : Bounds (Real.log (154967/320000:ℝ)) (-453193003/625000000:ℝ) (-7251088047/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (5033/160000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (154967/160000:ℝ)=1*Real.log 2+Real.log (154967/320000:ℝ) := by
    rw [show (154967/160000:ℝ)=(2:ℝ)^1*(154967/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_47 {m : ℝ} (hm : m∈Icc (618971/1280000:ℝ) (154967/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4700579113/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_47 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (154967/320000:ℝ)*(-453193003/625000000:ℝ)-(154967/320000:ℝ)+1+
      (((618971/1280000:ℝ)-1-(-7251088047/10000000000:ℝ))/(1-(618971/1280000:ℝ))^2)*(4700579113/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_48 : Bounds (Real.log (124153/256000:ℝ)) (-3618313843/5000000000:ℝ) (-1809156921/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3847/128000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (124153/128000:ℝ)=1*Real.log 2+Real.log (124153/256000:ℝ) := by
    rw [show (124153/128000:ℝ)=(2:ℝ)^1*(124153/256000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_48 {m : ℝ} (hm : m∈Icc (154967/320000:ℝ) (124153/256000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (941598937/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_48 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (124153/256000:ℝ)*(-3618313843/5000000000:ℝ)-(124153/256000:ℝ)+1+
      (((154967/320000:ℝ)-1-(-1809156921/2500000000:ℝ))/(1-(154967/320000:ℝ))^2)*(941598937/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_49 : Bounds (Real.log (310831/640000:ℝ)) (-7222188203/10000000000:ℝ) (-3611094101/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (9169/320000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (310831/320000:ℝ)=1*Real.log 2+Real.log (310831/640000:ℝ) := by
    rw [show (310831/320000:ℝ)=(2:ℝ)^1*(310831/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_49 {m : ℝ} (hm : m∈Icc (124153/256000:ℝ) (310831/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2357704181/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_49 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (310831/640000:ℝ)*(-7222188203/10000000000:ℝ)-(310831/640000:ℝ)+1+
      (((124153/256000:ℝ)-1-(-3611094101/5000000000:ℝ))/(1-(124153/256000:ℝ))^2)*(2357704181/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_50 : Bounds (Real.log (622559/1280000:ℝ)) (-360388477/500000000:ℝ) (-7207769539/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (17441/640000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (622559/640000:ℝ)=1*Real.log 2+Real.log (622559/1280000:ℝ) := by
    rw [show (622559/640000:ℝ)=(2:ℝ)^1*(622559/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_50 {m : ℝ} (hm : m∈Icc (310831/640000:ℝ) (622559/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (944564031/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_50 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (622559/1280000:ℝ)*(-360388477/500000000:ℝ)-(622559/1280000:ℝ)+1+
      (((310831/640000:ℝ)-1-(-7207769539/10000000000:ℝ))/(1-(310831/640000:ℝ))^2)*(944564031/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_51 : Bounds (Real.log (19483/40000:ℝ)) (-7193371637/10000000000:ℝ) (-1798342909/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (517/20000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (19483/20000:ℝ)=1*Real.log 2+Real.log (19483/40000:ℝ) := by
    rw [show (19483/20000:ℝ)=(2:ℝ)^1*(19483/40000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_51 {m : ℝ} (hm : m∈Icc (622559/1280000:ℝ) (19483/40000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4730230077/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_51 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (19483/40000:ℝ)*(-7193371637/10000000000:ℝ)-(19483/40000:ℝ)+1+
      (((622559/1280000:ℝ)-1-(-1798342909/2500000000:ℝ))/(1-(622559/1280000:ℝ))^2)*(4730230077/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_52 : Bounds (Real.log (624353/1280000:ℝ)) (-3589497217/5000000000:ℝ) (-7178994433/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (15647/640000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (624353/640000:ℝ)=1*Real.log 2+Real.log (624353/1280000:ℝ) := by
    rw [show (624353/640000:ℝ)=(2:ℝ)^1*(624353/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_52 {m : ℝ} (hm : m∈Icc (19483/40000:ℝ) (624353/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (236881907/500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_52 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (624353/1280000:ℝ)*(-3589497217/5000000000:ℝ)-(624353/1280000:ℝ)+1+
      (((19483/40000:ℝ)-1-(-7178994433/10000000000:ℝ))/(1-(19483/40000:ℝ))^2)*(236881907/500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_53 : Bounds (Real.log (2501/5120:ℝ)) (-447789867/625000000:ℝ) (-7164637871/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (59/2560:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2501/2560:ℝ)=1*Real.log 2+Real.log (2501/5120:ℝ) := by
    rw [show (2501/2560:ℝ)=(2:ℝ)^1*(2501/5120:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_53 {m : ℝ} (hm : m∈Icc (624353/1280000:ℝ) (2501/5120:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (949008871/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_53 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2501/5120:ℝ)*(-447789867/625000000:ℝ)-(2501/5120:ℝ)+1+
      (((624353/1280000:ℝ)-1-(-7164637871/10000000000:ℝ))/(1-(624353/1280000:ℝ))^2)*(949008871/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_54 : Bounds (Real.log (626147/1280000:ℝ)) (-7150301891/10000000000:ℝ) (-715030189/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (13853/640000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (626147/640000:ℝ)=1*Real.log 2+Real.log (626147/1280000:ℝ) := by
    rw [show (626147/640000:ℝ)=(2:ℝ)^1*(626147/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_54 {m : ℝ} (hm : m∈Icc (2501/5120:ℝ) (626147/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (950489747/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_54 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (626147/1280000:ℝ)*(-7150301891/10000000000:ℝ)-(626147/1280000:ℝ)+1+
      (((2501/5120:ℝ)-1-(-715030189/1000000000:ℝ))/(1-(2501/5120:ℝ))^2)*(950489747/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_55 : Bounds (Real.log (156761/320000:ℝ)) (-3567993217/5000000000:ℝ) (-7135986433/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3239/160000:ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (156761/160000:ℝ)=1*Real.log 2+Real.log (156761/320000:ℝ) := by
    rw [show (156761/160000:ℝ)=(2:ℝ)^1*(156761/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_55 {m : ℝ} (hm : m∈Icc (626147/1280000:ℝ) (156761/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (475985129/1000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_55 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (156761/320000:ℝ)*(-3567993217/5000000000:ℝ)-(156761/320000:ℝ)+1+
      (((626147/1280000:ℝ)-1-(-7135986433/10000000000:ℝ))/(1-(626147/1280000:ℝ))^2)*(475985129/1000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_56 : Bounds (Real.log (627941/1280000:ℝ)) (-89021143/125000000:ℝ) (-7121691439/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (12059/640000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (627941/640000:ℝ)=1*Real.log 2+Real.log (627941/1280000:ℝ) := by
    rw [show (627941/640000:ℝ)=(2:ℝ)^1*(627941/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_56 {m : ℝ} (hm : m∈Icc (156761/320000:ℝ) (627941/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4767252033/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_56 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (627941/1280000:ℝ)*(-89021143/125000000:ℝ)-(627941/1280000:ℝ)+1+
      (((156761/320000:ℝ)-1-(-7121691439/10000000000:ℝ))/(1-(156761/320000:ℝ))^2)*(4767252033/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_57 : Bounds (Real.log (314419/640000:ℝ)) (-7107416851/10000000000:ℝ) (-142148337/200000000:ℝ) := by
  have hh := log_taylor_bounds (x := (5581/320000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (314419/320000:ℝ)=1*Real.log 2+Real.log (314419/640000:ℝ) := by
    rw [show (314419/320000:ℝ)=(2:ℝ)^1*(314419/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_57 {m : ℝ} (hm : m∈Icc (627941/1280000:ℝ) (314419/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2387325487/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_57 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (314419/640000:ℝ)*(-7107416851/10000000000:ℝ)-(314419/640000:ℝ)+1+
      (((627941/1280000:ℝ)-1-(-142148337/200000000:ℝ))/(1-(627941/1280000:ℝ))^2)*(2387325487/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_58 : Bounds (Real.log (125947/256000:ℝ)) (-709316261/1000000000:ℝ) (-7093162609/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (2053/128000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (125947/128000:ℝ)=1*Real.log 2+Real.log (125947/256000:ℝ) := by
    rw [show (125947/128000:ℝ)=(2:ℝ)^1*(125947/256000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_58 {m : ℝ} (hm : m∈Icc (314419/640000:ℝ) (125947/256000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2391024063/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_58 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (125947/256000:ℝ)*(-709316261/1000000000:ℝ)-(125947/256000:ℝ)+1+
      (((314419/640000:ℝ)-1-(-7093162609/10000000000:ℝ))/(1-(314419/640000:ℝ))^2)*(2391024063/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_59 : Bounds (Real.log (78829/160000:ℝ)) (-3539464329/5000000000:ℝ) (-7078928657/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (1171/80000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (78829/80000:ℝ)=1*Real.log 2+Real.log (78829/160000:ℝ) := by
    rw [show (78829/80000:ℝ)=(2:ℝ)^1*(78829/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_59 {m : ℝ} (hm : m∈Icc (125947/256000:ℝ) (78829/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4789443499/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_59 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (78829/160000:ℝ)*(-3539464329/5000000000:ℝ)-(78829/160000:ℝ)+1+
      (((125947/256000:ℝ)-1-(-7078928657/10000000000:ℝ))/(1-(125947/256000:ℝ))^2)*(4789443499/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_60 : Bounds (Real.log (1262161/2560000:ℝ)) (-7071819273/10000000000:ℝ) (-883977409/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (17839/1280000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1262161/1280000:ℝ)=1*Real.log 2+Real.log (1262161/2560000:ℝ) := by
    rw [show (1262161/1280000:ℝ)=(2:ℝ)^1*(1262161/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_60 {m : ℝ} (hm : m∈Icc (78829/160000:ℝ) (1262161/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (959367421/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_60 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1262161/2560000:ℝ)*(-7071819273/10000000000:ℝ)-(1262161/2560000:ℝ)+1+
      (((78829/160000:ℝ)-1-(-883977409/1250000000:ℝ))/(1-(78829/160000:ℝ))^2)*(959367421/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_61 : Bounds (Real.log (631529/1280000:ℝ)) (-3532357469/5000000000:ℝ) (-7064714937/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (8471/640000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (631529/640000:ℝ)=1*Real.log 2+Real.log (631529/1280000:ℝ) := by
    rw [show (631529/640000:ℝ)=(2:ℝ)^1*(631529/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_61 {m : ℝ} (hm : m∈Icc (1262161/2560000:ℝ) (631529/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4800533249/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_61 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (631529/1280000:ℝ)*(-3532357469/5000000000:ℝ)-(631529/1280000:ℝ)+1+
      (((1262161/2560000:ℝ)-1-(-7064714937/10000000000:ℝ))/(1-(1262161/2560000:ℝ))^2)*(4800533249/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_62 : Bounds (Real.log (252791/512000:ℝ)) (-7057615647/10000000000:ℝ) (-3528807823/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3209/256000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (252791/256000:ℝ)=1*Real.log 2+Real.log (252791/512000:ℝ) := by
    rw [show (252791/256000:ℝ)=(2:ℝ)^1*(252791/512000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_62 {m : ℝ} (hm : m∈Icc (631529/1280000:ℝ) (252791/512000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2402114477/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_62 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (252791/512000:ℝ)*(-7057615647/10000000000:ℝ)-(252791/512000:ℝ)+1+
      (((631529/1280000:ℝ)-1-(-3528807823/5000000000:ℝ))/(1-(631529/1280000:ℝ))^2)*(2402114477/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_63 : Bounds (Real.log (316213/640000:ℝ)) (-7050521393/10000000000:ℝ) (-440657587/625000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3787/320000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (316213/320000:ℝ)=1*Real.log 2+Real.log (316213/640000:ℝ) := by
    rw [show (316213/320000:ℝ)=(2:ℝ)^1*(316213/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_63 {m : ℝ} (hm : m∈Icc (252791/512000:ℝ) (316213/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (9390477/19531250:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_63 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (316213/640000:ℝ)*(-7050521393/10000000000:ℝ)-(316213/640000:ℝ)+1+
      (((252791/512000:ℝ)-1-(-440657587/625000000:ℝ))/(1-(252791/512000:ℝ))^2)*(9390477/19531250:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_64 : Bounds (Real.log (1265749/2560000:ℝ)) (-7043432167/10000000000:ℝ) (-3521716083/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (14251/1280000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1265749/1280000:ℝ)=1*Real.log 2+Real.log (1265749/2560000:ℝ) := by
    rw [show (1265749/1280000:ℝ)=(2:ℝ)^1*(1265749/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_64 {m : ℝ} (hm : m∈Icc (316213/640000:ℝ) (1265749/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4811619059/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_64 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1265749/2560000:ℝ)*(-7043432167/10000000000:ℝ)-(1265749/2560000:ℝ)+1+
      (((316213/640000:ℝ)-1-(-3521716083/5000000000:ℝ))/(1-(316213/640000:ℝ))^2)*(4811619059/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_65 : Bounds (Real.log (633323/1280000:ℝ)) (-1759086991/2500000000:ℝ) (-7036347963/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (6677/640000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (633323/640000:ℝ)=1*Real.log 2+Real.log (633323/1280000:ℝ) := by
    rw [show (633323/640000:ℝ)=(2:ℝ)^1*(633323/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_65 {m : ℝ} (hm : m∈Icc (1265749/2560000:ℝ) (633323/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (240765673/500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_65 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (633323/1280000:ℝ)*(-1759086991/2500000000:ℝ)-(633323/1280000:ℝ)+1+
      (((1265749/2560000:ℝ)-1-(-7036347963/10000000000:ℝ))/(1-(1265749/2560000:ℝ))^2)*(240765673/500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_66 : Bounds (Real.log (1267543/2560000:ℝ)) (-878658597/1250000000:ℝ) (-281170751/400000000:ℝ) := by
  have hh := log_taylor_bounds (x := (12457/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1267543/1280000:ℝ)=1*Real.log 2+Real.log (1267543/2560000:ℝ) := by
    rw [show (1267543/1280000:ℝ)=(2:ℝ)^1*(1267543/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_66 {m : ℝ} (hm : m∈Icc (633323/1280000:ℝ) (1267543/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4819007429/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_66 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1267543/2560000:ℝ)*(-878658597/1250000000:ℝ)-(1267543/2560000:ℝ)+1+
      (((633323/1280000:ℝ)-1-(-281170751/400000000:ℝ))/(1-(633323/1280000:ℝ))^2)*(4819007429/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_67 : Bounds (Real.log (31711/64000:ℝ)) (-1755548649/2500000000:ℝ) (-1404438919/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (289/32000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (31711/32000:ℝ)=1*Real.log 2+Real.log (31711/64000:ℝ) := by
    rw [show (31711/32000:ℝ)=(2:ℝ)^1*(31711/64000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_67 {m : ℝ} (hm : m∈Icc (1267543/2560000:ℝ) (31711/64000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2411350483/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_67 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (31711/64000:ℝ)*(-1755548649/2500000000:ℝ)-(31711/64000:ℝ)+1+
      (((1267543/2560000:ℝ)-1-(-1404438919/2000000000:ℝ))/(1-(1267543/2560000:ℝ))^2)*(2411350483/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_68 : Bounds (Real.log (1269337/2560000:ℝ)) (-876890677/1250000000:ℝ) (-1403025083/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (10663/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1269337/1280000:ℝ)=1*Real.log 2+Real.log (1269337/2560000:ℝ) := by
    rw [show (1269337/1280000:ℝ)=(2:ℝ)^1*(1269337/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_68 {m : ℝ} (hm : m∈Icc (31711/64000:ℝ) (1269337/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (193055763/400000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_68 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1269337/2560000:ℝ)*(-876890677/1250000000:ℝ)-(1269337/2560000:ℝ)+1+
      (((31711/64000:ℝ)-1-(-1403025083/2000000000:ℝ))/(1-(31711/64000:ℝ))^2)*(193055763/400000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_69 : Bounds (Real.log (635117/1280000:ℝ)) (-7008061231/10000000000:ℝ) (-700806123/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (4883/640000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (635117/640000:ℝ)=1*Real.log 2+Real.log (635117/1280000:ℝ) := by
    rw [show (635117/640000:ℝ)=(2:ℝ)^1*(635117/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_69 {m : ℝ} (hm : m∈Icc (1269337/2560000:ℝ) (635117/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (966017351/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_69 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (635117/1280000:ℝ)*(-7008061231/10000000000:ℝ)-(635117/1280000:ℝ)+1+
      (((1269337/2560000:ℝ)-1-(-700806123/1000000000:ℝ))/(1-(1269337/2560000:ℝ))^2)*(966017351/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_70 : Bounds (Real.log (1271131/2560000:ℝ)) (-437562627/625000000:ℝ) (-7001002031/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (8869/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1271131/1280000:ℝ)=1*Real.log 2+Real.log (1271131/2560000:ℝ) := by
    rw [show (1271131/1280000:ℝ)=(2:ℝ)^1*(1271131/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_70 {m : ℝ} (hm : m∈Icc (635117/1280000:ℝ) (1271131/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (75527797/156250000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_70 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1271131/2560000:ℝ)*(-437562627/625000000:ℝ)-(1271131/2560000:ℝ)+1+
      (((635117/1280000:ℝ)-1-(-7001002031/10000000000:ℝ))/(1-(635117/1280000:ℝ))^2)*(75527797/156250000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_71 : Bounds (Real.log (318007/640000:ℝ)) (-6993947813/10000000000:ℝ) (-1748486953/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (1993/320000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (318007/320000:ℝ)=1*Real.log 2+Real.log (318007/640000:ℝ) := by
    rw [show (318007/320000:ℝ)=(2:ℝ)^1*(318007/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_71 {m : ℝ} (hm : m∈Icc (1271131/2560000:ℝ) (318007/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1209367709/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_71 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (318007/640000:ℝ)*(-6993947813/10000000000:ℝ)-(318007/640000:ℝ)+1+
      (((1271131/2560000:ℝ)-1-(-1748486953/2500000000:ℝ))/(1-(1271131/2560000:ℝ))^2)*(1209367709/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_72 : Bounds (Real.log (50917/102400:ℝ)) (-3493449283/5000000000:ℝ) (-1397379713/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (283/51200:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (50917/51200:ℝ)=1*Real.log 2+Real.log (50917/102400:ℝ) := by
    rw [show (50917/51200:ℝ)=(2:ℝ)^1*(50917/102400:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_72 {m : ℝ} (hm : m∈Icc (318007/640000:ℝ) (50917/102400:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1891079/3906250:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_72 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (50917/102400:ℝ)*(-3493449283/5000000000:ℝ)-(50917/102400:ℝ)+1+
      (((318007/640000:ℝ)-1-(-1397379713/2000000000:ℝ))/(1-(318007/640000:ℝ))^2)*(1891079/3906250:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_73 : Bounds (Real.log (636911/1280000:ℝ)) (-3489927143/5000000000:ℝ) (-1395970857/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3089/640000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (636911/640000:ℝ)=1*Real.log 2+Real.log (636911/1280000:ℝ) := by
    rw [show (636911/640000:ℝ)=(2:ℝ)^1*(636911/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_73 {m : ℝ} (hm : m∈Icc (50917/102400:ℝ) (636911/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (242242661/500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_73 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (636911/1280000:ℝ)*(-3489927143/5000000000:ℝ)-(636911/1280000:ℝ)+1+
      (((50917/102400:ℝ)-1-(-1395970857/2000000000:ℝ))/(1-(50917/102400:ℝ))^2)*(242242661/500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_74 : Bounds (Real.log (1274719/2560000:ℝ)) (-1743203741/2500000000:ℝ) (-6972814963/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (5281/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1274719/1280000:ℝ)=1*Real.log 2+Real.log (1274719/2560000:ℝ) := by
    rw [show (1274719/1280000:ℝ)=(2:ℝ)^1*(1274719/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_74 {m : ℝ} (hm : m∈Icc (636911/1280000:ℝ) (1274719/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4848543779/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_74 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1274719/2560000:ℝ)*(-1743203741/2500000000:ℝ)-(1274719/2560000:ℝ)+1+
      (((636911/1280000:ℝ)-1-(-6972814963/10000000000:ℝ))/(1-(636911/1280000:ℝ))^2)*(4848543779/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_75 : Bounds (Real.log (39863/80000:ℝ)) (-6965780593/10000000000:ℝ) (-435361287/625000000:ℝ) := by
  have hh := log_taylor_bounds (x := (137/40000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (39863/40000:ℝ)=1*Real.log 2+Real.log (39863/80000:ℝ) := by
    rw [show (39863/40000:ℝ)=(2:ℝ)^1*(39863/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_75 {m : ℝ} (hm : m∈Icc (1274719/2560000:ℝ) (39863/80000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2426116959/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_75 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (39863/80000:ℝ)*(-6965780593/10000000000:ℝ)-(39863/80000:ℝ)+1+
      (((1274719/2560000:ℝ)-1-(-435361287/625000000:ℝ))/(1-(1274719/2560000:ℝ))^2)*(2426116959/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_76 : Bounds (Real.log (1276513/2560000:ℝ)) (-108730487/156250000:ℝ) (-6958751167/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (3487/1280000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1276513/1280000:ℝ)=1*Real.log 2+Real.log (1276513/2560000:ℝ) := by
    rw [show (1276513/1280000:ℝ)=(2:ℝ)^1*(1276513/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_76 {m : ℝ} (hm : m∈Icc (39863/80000:ℝ) (1276513/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4855923637/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_76 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1276513/2560000:ℝ)*(-108730487/156250000:ℝ)-(1276513/2560000:ℝ)+1+
      (((39863/80000:ℝ)-1-(-6958751167/10000000000:ℝ))/(1-(39863/80000:ℝ))^2)*(4855923637/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_77 : Bounds (Real.log (127741/256000:ℝ)) (-173793167/250000000:ℝ) (-6951726679/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (259/128000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (127741/128000:ℝ)=1*Real.log 2+Real.log (127741/256000:ℝ) := by
    rw [show (127741/128000:ℝ)=(2:ℝ)^1*(127741/256000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_77 {m : ℝ} (hm : m∈Icc (1276513/2560000:ℝ) (127741/256000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4859612939/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_77 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (127741/256000:ℝ)*(-173793167/250000000:ℝ)-(127741/256000:ℝ)+1+
      (((1276513/2560000:ℝ)-1-(-6951726679/10000000000:ℝ))/(1-(1276513/2560000:ℝ))^2)*(4859612939/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_78 : Bounds (Real.log (1278307/2560000:ℝ)) (-6944707123/10000000000:ℝ) (-3472353561/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (1693/1280000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1278307/1280000:ℝ)=1*Real.log 2+Real.log (1278307/2560000:ℝ) := by
    rw [show (1278307/1280000:ℝ)=(2:ℝ)^1*(1278307/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_78 {m : ℝ} (hm : m∈Icc (127741/256000:ℝ) (1278307/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (194532073/400000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_78 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1278307/2560000:ℝ)*(-6944707123/10000000000:ℝ)-(1278307/2560000:ℝ)+1+
      (((127741/256000:ℝ)-1-(-3472353561/5000000000:ℝ))/(1-(127741/256000:ℝ))^2)*(194532073/400000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_79 : Bounds (Real.log (319801/640000:ℝ)) (-6937692491/10000000000:ℝ) (-693769249/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (199/320000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (319801/320000:ℝ)=1*Real.log 2+Real.log (319801/640000:ℝ) := by
    rw [show (319801/320000:ℝ)=(2:ℝ)^1*(319801/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_79 {m : ℝ} (hm : m∈Icc (1278307/2560000:ℝ) (319801/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (973398059/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_79 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (319801/640000:ℝ)*(-6937692491/10000000000:ℝ)-(319801/640000:ℝ)+1+
      (((1278307/2560000:ℝ)-1-(-693769249/1000000000:ℝ))/(1-(1278307/2560000:ℝ))^2)*(973398059/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_80 : Bounds (Real.log (1280101/2560000:ℝ)) (-277227311/400000000:ℝ) (-3465341387/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-101/1280000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1280101/1280000:ℝ)=1*Real.log 2+Real.log (1280101/2560000:ℝ) := by
    rw [show (1280101/1280000:ℝ)=(2:ℝ)^1*(1280101/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_80 {m : ℝ} (hm : m∈Icc (319801/640000:ℝ) (1280101/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (304417397/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_80 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1280101/2560000:ℝ)*(-277227311/400000000:ℝ)-(1280101/2560000:ℝ)+1+
      (((319801/640000:ℝ)-1-(-3465341387/5000000000:ℝ))/(1-(319801/640000:ℝ))^2)*(304417397/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_81 : Bounds (Real.log (640499/1280000:ℝ)) (-6923677969/10000000000:ℝ) (-432729873/625000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-499/640000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (640499/640000:ℝ)=1*Real.log 2+Real.log (640499/1280000:ℝ) := by
    rw [show (640499/640000:ℝ)=(2:ℝ)^1*(640499/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_81 {m : ℝ} (hm : m∈Icc (1280101/2560000:ℝ) (640499/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1218591499/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_81 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (640499/1280000:ℝ)*(-6923677969/10000000000:ℝ)-(640499/1280000:ℝ)+1+
      (((1280101/2560000:ℝ)-1-(-432729873/625000000:ℝ))/(1-(1280101/2560000:ℝ))^2)*(1218591499/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_82 : Bounds (Real.log (256379/512000:ℝ)) (-6916678067/10000000000:ℝ) (-3458339033/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-379/256000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (256379/256000:ℝ)=1*Real.log 2+Real.log (256379/512000:ℝ) := by
    rw [show (256379/256000:ℝ)=(2:ℝ)^1*(256379/512000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_82 {m : ℝ} (hm : m∈Icc (640499/1280000:ℝ) (256379/512000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4878053229/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_82 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (256379/512000:ℝ)*(-6916678067/10000000000:ℝ)-(256379/512000:ℝ)+1+
      (((640499/1280000:ℝ)-1-(-3458339033/5000000000:ℝ))/(1-(640499/1280000:ℝ))^2)*(4878053229/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_83 : Bounds (Real.log (160349/320000:ℝ)) (-6909683061/10000000000:ℝ) (-345484153/500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-349/160000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (160349/160000:ℝ)=1*Real.log 2+Real.log (160349/320000:ℝ) := by
    rw [show (160349/160000:ℝ)=(2:ℝ)^1*(160349/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_83 {m : ℝ} (hm : m∈Icc (256379/512000:ℝ) (160349/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1220435013/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_83 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (160349/320000:ℝ)*(-6909683061/10000000000:ℝ)-(160349/320000:ℝ)+1+
      (((256379/512000:ℝ)-1-(-345484153/500000000:ℝ))/(1-(256379/512000:ℝ))^2)*(1220435013/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_84 : Bounds (Real.log (1283689/2560000:ℝ)) (-431418309/625000000:ℝ) (-6902692943/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-3689/1280000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1283689/1280000:ℝ)=1*Real.log 2+Real.log (1283689/2560000:ℝ) := by
    rw [show (1283689/1280000:ℝ)=(2:ℝ)^1*(1283689/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_84 {m : ℝ} (hm : m∈Icc (160349/320000:ℝ) (1283689/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2442713233/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_84 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1283689/2560000:ℝ)*(-431418309/625000000:ℝ)-(1283689/2560000:ℝ)+1+
      (((160349/320000:ℝ)-1-(-6902692943/10000000000:ℝ))/(1-(160349/320000:ℝ))^2)*(2442713233/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_85 : Bounds (Real.log (642293/1280000:ℝ)) (-6895707711/10000000000:ℝ) (-689570771/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-2293/640000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (642293/640000:ℝ)=1*Real.log 2+Real.log (642293/1280000:ℝ) := by
    rw [show (642293/640000:ℝ)=(2:ℝ)^1*(642293/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_85 {m : ℝ} (hm : m∈Icc (1283689/2560000:ℝ) (642293/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (611139059/1250000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_85 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (642293/1280000:ℝ)*(-6895707711/10000000000:ℝ)-(642293/1280000:ℝ)+1+
      (((1283689/2560000:ℝ)-1-(-689570771/1000000000:ℝ))/(1-(1283689/2560000:ℝ))^2)*(611139059/1250000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_86 : Bounds (Real.log (2570069/5120000:ℝ)) (-6892216923/10000000000:ℝ) (-3446108461/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-10069/2560000:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2570069/2560000:ℝ)=1*Real.log 2+Real.log (2570069/5120000:ℝ) := by
    rw [show (2570069/2560000:ℝ)=(2:ℝ)^1*(2570069/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_86 {m : ℝ} (hm : m∈Icc (642293/1280000:ℝ) (2570069/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (611599759/1250000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_86 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2570069/5120000:ℝ)*(-6892216923/10000000000:ℝ)-(2570069/5120000:ℝ)+1+
      (((642293/1280000:ℝ)-1-(-3446108461/5000000000:ℝ))/(1-(642293/1280000:ℝ))^2)*(611599759/1250000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_87 : Bounds (Real.log (1285483/2560000:ℝ)) (-6888727353/10000000000:ℝ) (-861090919/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-5483/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1285483/1280000:ℝ)=1*Real.log 2+Real.log (1285483/2560000:ℝ) := by
    rw [show (1285483/1280000:ℝ)=(2:ℝ)^1*(1285483/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_87 {m : ℝ} (hm : m∈Icc (2570069/5120000:ℝ) (1285483/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (61183009/125000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_87 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1285483/2560000:ℝ)*(-6888727353/10000000000:ℝ)-(1285483/2560000:ℝ)+1+
      (((2570069/5120000:ℝ)-1-(-861090919/1250000000:ℝ))/(1-(2570069/5120000:ℝ))^2)*(61183009/125000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_88 : Bounds (Real.log (2571863/5120000:ℝ)) (-6885239001/10000000000:ℝ) (-6885239/10000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-11863/2560000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2571863/2560000:ℝ)=1*Real.log 2+Real.log (2571863/5120000:ℝ) := by
    rw [show (2571863/2560000:ℝ)=(2:ℝ)^1*(2571863/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_88 {m : ℝ} (hm : m∈Icc (1285483/2560000:ℝ) (2571863/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4896483267/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_88 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2571863/5120000:ℝ)*(-6885239001/10000000000:ℝ)-(2571863/5120000:ℝ)+1+
      (((1285483/2560000:ℝ)-1-(-6885239/10000000:ℝ))/(1-(1285483/2560000:ℝ))^2)*(4896483267/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_89 : Bounds (Real.log (64319/128000:ℝ)) (-1376350373/2000000000:ℝ) (-860218983/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-319/64000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (64319/64000:ℝ)=1*Real.log 2+Real.log (64319/128000:ℝ) := by
    rw [show (64319/64000:ℝ)=(2:ℝ)^1*(64319/128000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_89 {m : ℝ} (hm : m∈Icc (2571863/5120000:ℝ) (64319/128000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4898325713/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_89 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (64319/128000:ℝ)*(-1376350373/2000000000:ℝ)-(64319/128000:ℝ)+1+
      (((2571863/5120000:ℝ)-1-(-860218983/1250000000:ℝ))/(1-(2571863/5120000:ℝ))^2)*(4898325713/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_90 : Bounds (Real.log (2573657/5120000:ℝ)) (-859783243/1250000000:ℝ) (-6878265943/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-13657/2560000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2573657/2560000:ℝ)=1*Real.log 2+Real.log (2573657/5120000:ℝ) := by
    rw [show (2573657/2560000:ℝ)=(2:ℝ)^1*(2573657/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_90 {m : ℝ} (hm : m∈Icc (64319/128000:ℝ) (2573657/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4900168059/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_90 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2573657/5120000:ℝ)*(-859783243/1250000000:ℝ)-(2573657/5120000:ℝ)+1+
      (((64319/128000:ℝ)-1-(-6878265943/10000000000:ℝ))/(1-(64319/128000:ℝ))^2)*(4900168059/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_91 : Bounds (Real.log (1287277/2560000:ℝ)) (-6874781239/10000000000:ℝ) (-3437390619/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-7277/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1287277/1280000:ℝ)=1*Real.log 2+Real.log (1287277/2560000:ℝ) := by
    rw [show (1287277/1280000:ℝ)=(2:ℝ)^1*(1287277/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_91 {m : ℝ} (hm : m∈Icc (2573657/5120000:ℝ) (1287277/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4902010303/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_91 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1287277/2560000:ℝ)*(-6874781239/10000000000:ℝ)-(1287277/2560000:ℝ)+1+
      (((2573657/5120000:ℝ)-1-(-3437390619/5000000000:ℝ))/(1-(2573657/5120000:ℝ))^2)*(4902010303/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_92 : Bounds (Real.log (2575451/5120000:ℝ)) (-6871297747/10000000000:ℝ) (-3435648873/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-15451/2560000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2575451/2560000:ℝ)=1*Real.log 2+Real.log (2575451/5120000:ℝ) := by
    rw [show (2575451/2560000:ℝ)=(2:ℝ)^1*(2575451/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_92 {m : ℝ} (hm : m∈Icc (1287277/2560000:ℝ) (2575451/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (153245389/312500000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_92 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2575451/5120000:ℝ)*(-6871297747/10000000000:ℝ)-(2575451/5120000:ℝ)+1+
      (((1287277/2560000:ℝ)-1-(-3435648873/5000000000:ℝ))/(1-(1287277/2560000:ℝ))^2)*(153245389/312500000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_93 : Bounds (Real.log (644087/1280000:ℝ)) (-1716953867/2500000000:ℝ) (-6867815467/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-4087/640000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (644087/640000:ℝ)=1*Real.log 2+Real.log (644087/1280000:ℝ) := by
    rw [show (644087/640000:ℝ)=(2:ℝ)^1*(644087/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_93 {m : ℝ} (hm : m∈Icc (2575451/5120000:ℝ) (644087/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4905694491/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_93 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (644087/1280000:ℝ)*(-1716953867/2500000000:ℝ)-(644087/1280000:ℝ)+1+
      (((2575451/5120000:ℝ)-1-(-6867815467/10000000000:ℝ))/(1-(2575451/5120000:ℝ))^2)*(4905694491/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_94 : Bounds (Real.log (515449/1024000:ℝ)) (-3432167201/5000000000:ℝ) (-6864334401/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-3449/512000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (515449/512000:ℝ)=1*Real.log 2+Real.log (515449/1024000:ℝ) := by
    rw [show (515449/512000:ℝ)=(2:ℝ)^1*(515449/1024000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_94 {m : ℝ} (hm : m∈Icc (644087/1280000:ℝ) (515449/1024000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (981507287/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_94 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (515449/1024000:ℝ)*(-3432167201/5000000000:ℝ)-(515449/1024000:ℝ)+1+
      (((644087/1280000:ℝ)-1-(-6864334401/10000000000:ℝ))/(1-(644087/1280000:ℝ))^2)*(981507287/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_95 : Bounds (Real.log (1289071/2560000:ℝ)) (-3430427273/5000000000:ℝ) (-1372170909/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-9071/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1289071/1280000:ℝ)=1*Real.log 2+Real.log (1289071/2560000:ℝ) := by
    rw [show (1289071/1280000:ℝ)=(2:ℝ)^1*(1289071/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_95 {m : ℝ} (hm : m∈Icc (515449/1024000:ℝ) (1289071/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4909378279/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_95 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1289071/2560000:ℝ)*(-3430427273/5000000000:ℝ)-(1289071/2560000:ℝ)+1+
      (((515449/1024000:ℝ)-1-(-1372170909/2000000000:ℝ))/(1-(515449/1024000:ℝ))^2)*(4909378279/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_96 : Bounds (Real.log (2579039/5120000:ℝ)) (-3428687951/5000000000:ℝ) (-6857375901/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-19039/2560000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2579039/2560000:ℝ)=1*Real.log 2+Real.log (2579039/5120000:ℝ) := by
    rw [show (2579039/2560000:ℝ)=(2:ℝ)^1*(2579039/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_96 {m : ℝ} (hm : m∈Icc (1289071/2560000:ℝ) (2579039/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2455610011/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_96 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2579039/5120000:ℝ)*(-3428687951/5000000000:ℝ)-(2579039/5120000:ℝ)+1+
      (((1289071/2560000:ℝ)-1-(-6857375901/10000000000:ℝ))/(1-(1289071/2560000:ℝ))^2)*(2455610011/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_97 : Bounds (Real.log (80623/160000:ℝ)) (-6853898467/10000000000:ℝ) (-3426949233/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-623/80000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (80623/80000:ℝ)=1*Real.log 2+Real.log (80623/160000:ℝ) := by
    rw [show (80623/80000:ℝ)=(2:ℝ)^1*(80623/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_97 {m : ℝ} (hm : m∈Icc (2579039/5120000:ℝ) (80623/160000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2456530833/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_97 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (80623/160000:ℝ)*(-6853898467/10000000000:ℝ)-(80623/160000:ℝ)+1+
      (((2579039/5120000:ℝ)-1-(-3426949233/5000000000:ℝ))/(1-(2579039/5120000:ℝ))^2)*(2456530833/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_98 : Bounds (Real.log (2580833/5120000:ℝ)) (-6850422241/10000000000:ℝ) (-42815139/62500000:ℝ) := by
  have hh := log_taylor_bounds (x := (-20833/2560000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2580833/2560000:ℝ)=1*Real.log 2+Real.log (2580833/5120000:ℝ) := by
    rw [show (2580833/2560000:ℝ)=(2:ℝ)^1*(2580833/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_98 {m : ℝ} (hm : m∈Icc (80623/160000:ℝ) (2580833/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4914903211/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_98 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2580833/5120000:ℝ)*(-6850422241/10000000000:ℝ)-(2580833/5120000:ℝ)+1+
      (((80623/160000:ℝ)-1-(-42815139/62500000:ℝ))/(1-(80623/160000:ℝ))^2)*(4914903211/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_99 : Bounds (Real.log (258173/512000:ℝ)) (-3423473611/5000000000:ℝ) (-6846947221/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-2173/256000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (258173/256000:ℝ)=1*Real.log 2+Real.log (258173/512000:ℝ) := by
    rw [show (258173/256000:ℝ)=(2:ℝ)^1*(258173/512000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_99 {m : ℝ} (hm : m∈Icc (2580833/5120000:ℝ) (258173/512000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (307296541/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_99 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (258173/512000:ℝ)*(-3423473611/5000000000:ℝ)-(258173/512000:ℝ)+1+
      (((2580833/5120000:ℝ)-1-(-6846947221/10000000000:ℝ))/(1-(2580833/5120000:ℝ))^2)*(307296541/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_100 : Bounds (Real.log (2582627/5120000:ℝ)) (-6843473411/10000000000:ℝ) (-684347341/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-22627/2560000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2582627/2560000:ℝ)=1*Real.log 2+Real.log (2582627/5120000:ℝ) := by
    rw [show (2582627/2560000:ℝ)=(2:ℝ)^1*(2582627/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_100 {m : ℝ} (hm : m∈Icc (258173/512000:ℝ) (2582627/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2459293001/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_100 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2582627/5120000:ℝ)*(-6843473411/10000000000:ℝ)-(2582627/5120000:ℝ)+1+
      (((258173/512000:ℝ)-1-(-684347341/1000000000:ℝ))/(1-(258173/512000:ℝ))^2)*(2459293001/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_101 : Bounds (Real.log (645881/1280000:ℝ)) (-6840000807/10000000000:ℝ) (-3420000403/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-5881/640000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (645881/640000:ℝ)=1*Real.log 2+Real.log (645881/1280000:ℝ) := by
    rw [show (645881/640000:ℝ)=(2:ℝ)^1*(645881/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_101 {m : ℝ} (hm : m∈Icc (2582627/5120000:ℝ) (645881/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4920427249/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_101 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (645881/1280000:ℝ)*(-6840000807/10000000000:ℝ)-(645881/1280000:ℝ)+1+
      (((2582627/5120000:ℝ)-1-(-3420000403/5000000000:ℝ))/(1-(2582627/5120000:ℝ))^2)*(4920427249/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_102 : Bounds (Real.log (2584421/5120000:ℝ)) (-26705193/39062500:ℝ) (-6836529407/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-24421/2560000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2584421/2560000:ℝ)=1*Real.log 2+Real.log (2584421/5120000:ℝ) := by
    rw [show (2584421/2560000:ℝ)=(2:ℝ)^1*(2584421/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_102 {m : ℝ} (hm : m∈Icc (645881/1280000:ℝ) (2584421/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1230567099/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_102 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2584421/5120000:ℝ)*(-26705193/39062500:ℝ)-(2584421/5120000:ℝ)+1+
      (((645881/1280000:ℝ)-1-(-6836529407/10000000000:ℝ))/(1-(645881/1280000:ℝ))^2)*(1230567099/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_103 : Bounds (Real.log (1292659/2560000:ℝ)) (-6833059213/10000000000:ℝ) (-1708264803/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-12659/1280000:ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1292659/1280000:ℝ)=1*Real.log 2+Real.log (1292659/2560000:ℝ) := by
    rw [show (1292659/1280000:ℝ)=(2:ℝ)^1*(1292659/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_103 {m : ℝ} (hm : m∈Icc (2584421/5120000:ℝ) (1292659/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (984821889/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_103 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1292659/2560000:ℝ)*(-6833059213/10000000000:ℝ)-(1292659/2560000:ℝ)+1+
      (((2584421/5120000:ℝ)-1-(-1708264803/2500000000:ℝ))/(1-(2584421/5120000:ℝ))^2)*(984821889/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_104 : Bounds (Real.log (517243/1024000:ℝ)) (-3414795111/5000000000:ℝ) (-6829590221/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-5243/512000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (517243/512000:ℝ)=1*Real.log 2+Real.log (517243/1024000:ℝ) := by
    rw [show (517243/512000:ℝ)=(2:ℝ)^1*(517243/1024000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_104 {m : ℝ} (hm : m∈Icc (1292659/2560000:ℝ) (517243/1024000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (985190079/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_104 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (517243/1024000:ℝ)*(-3414795111/5000000000:ℝ)-(517243/1024000:ℝ)+1+
      (((1292659/2560000:ℝ)-1-(-6829590221/10000000000:ℝ))/(1-(1292659/2560000:ℝ))^2)*(985190079/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_105 : Bounds (Real.log (323389/640000:ℝ)) (-3413061217/5000000000:ℝ) (-6826122433/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-3389/320000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (323389/320000:ℝ)=1*Real.log 2+Real.log (323389/640000:ℝ) := by
    rw [show (323389/320000:ℝ)=(2:ℝ)^1*(323389/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_105 {m : ℝ} (hm : m∈Icc (517243/1024000:ℝ) (323389/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4927791247/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_105 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (323389/640000:ℝ)*(-3413061217/5000000000:ℝ)-(323389/640000:ℝ)+1+
      (((517243/1024000:ℝ)-1-(-6826122433/10000000000:ℝ))/(1-(517243/1024000:ℝ))^2)*(4927791247/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_106 : Bounds (Real.log (2588009/5120000:ℝ)) (-6822655849/10000000000:ℝ) (-852831981/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-28009/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2588009/2560000:ℝ)=1*Real.log 2+Real.log (2588009/5120000:ℝ) := by
    rw [show (2588009/2560000:ℝ)=(2:ℝ)^1*(2588009/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_106 {m : ℝ} (hm : m∈Icc (323389/640000:ℝ) (2588009/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4929632001/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_106 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2588009/5120000:ℝ)*(-6822655849/10000000000:ℝ)-(2588009/5120000:ℝ)+1+
      (((323389/640000:ℝ)-1-(-852831981/1250000000:ℝ))/(1-(323389/640000:ℝ))^2)*(4929632001/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_107 : Bounds (Real.log (1294453/2560000:ℝ)) (-106549851/156250000:ℝ) (-6819190463/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-14453/1280000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1294453/1280000:ℝ)=1*Real.log 2+Real.log (1294453/2560000:ℝ) := by
    rw [show (1294453/1280000:ℝ)=(2:ℝ)^1*(1294453/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_107 {m : ℝ} (hm : m∈Icc (2588009/5120000:ℝ) (1294453/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (308217041/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_107 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1294453/2560000:ℝ)*(-106549851/156250000:ℝ)-(1294453/2560000:ℝ)+1+
      (((2588009/5120000:ℝ)-1-(-6819190463/10000000000:ℝ))/(1-(2588009/5120000:ℝ))^2)*(308217041/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_108 : Bounds (Real.log (2589803/5120000:ℝ)) (-6815726281/10000000000:ℝ) (-170393157/250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-29803/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2589803/2560000:ℝ)=1*Real.log 2+Real.log (2589803/5120000:ℝ) := by
    rw [show (2589803/2560000:ℝ)=(2:ℝ)^1*(2589803/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_108 {m : ℝ} (hm : m∈Icc (1294453/2560000:ℝ) (2589803/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4933313213/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_108 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2589803/5120000:ℝ)*(-6815726281/10000000000:ℝ)-(2589803/5120000:ℝ)+1+
      (((1294453/2560000:ℝ)-1-(-170393157/250000000:ℝ))/(1-(1294453/2560000:ℝ))^2)*(4933313213/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_109 : Bounds (Real.log (25907/51200:ℝ)) (-53220807/78125000:ℝ) (-1362452659/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-307/25600:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (25907/25600:ℝ)=1*Real.log 2+Real.log (25907/51200:ℝ) := by
    rw [show (25907/25600:ℝ)=(2:ℝ)^1*(25907/51200:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_109 {m : ℝ} (hm : m∈Icc (2589803/5120000:ℝ) (25907/51200:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (616894209/1250000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_109 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (25907/51200:ℝ)*(-53220807/78125000:ℝ)-(25907/51200:ℝ)+1+
      (((2589803/5120000:ℝ)-1-(-1362452659/2000000000:ℝ))/(1-(2589803/5120000:ℝ))^2)*(616894209/1250000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_110 : Bounds (Real.log (2591597/5120000:ℝ)) (-6808801511/10000000000:ℝ) (-680880151/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-31597/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2591597/2560000:ℝ)=1*Real.log 2+Real.log (2591597/5120000:ℝ) := by
    rw [show (2591597/2560000:ℝ)=(2:ℝ)^1*(2591597/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_110 {m : ℝ} (hm : m∈Icc (25907/51200:ℝ) (2591597/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2468497017/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_110 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2591597/5120000:ℝ)*(-6808801511/10000000000:ℝ)-(2591597/5120000:ℝ)+1+
      (((25907/51200:ℝ)-1-(-680880151/1000000000:ℝ))/(1-(25907/51200:ℝ))^2)*(2468497017/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_111 : Bounds (Real.log (1296247/2560000:ℝ)) (-1701335231/2500000000:ℝ) (-6805340923/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-16247/1280000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1296247/1280000:ℝ)=1*Real.log 2+Real.log (1296247/2560000:ℝ) := by
    rw [show (1296247/1280000:ℝ)=(2:ℝ)^1*(1296247/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_111 {m : ℝ} (hm : m∈Icc (2591597/5120000:ℝ) (1296247/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2469417149/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_111 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1296247/2560000:ℝ)*(-1701335231/2500000000:ℝ)-(1296247/2560000:ℝ)+1+
      (((2591597/5120000:ℝ)-1-(-6805340923/10000000000:ℝ))/(1-(2591597/5120000:ℝ))^2)*(2469417149/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_112 : Bounds (Real.log (2593391/5120000:ℝ)) (-6801881533/10000000000:ℝ) (-1700470383/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-33391/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2593391/2560000:ℝ)=1*Real.log 2+Real.log (2593391/5120000:ℝ) := by
    rw [show (2593391/2560000:ℝ)=(2:ℝ)^1*(2593391/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_112 {m : ℝ} (hm : m∈Icc (1296247/2560000:ℝ) (2593391/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (154396077/312500000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_112 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2593391/5120000:ℝ)*(-6801881533/10000000000:ℝ)-(2593391/5120000:ℝ)+1+
      (((1296247/2560000:ℝ)-1-(-1700470383/2500000000:ℝ))/(1-(1296247/2560000:ℝ))^2)*(154396077/312500000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_113 : Bounds (Real.log (162143/320000:ℝ)) (-6798423339/10000000000:ℝ) (-3399211669/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-2143/160000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (162143/160000:ℝ)=1*Real.log 2+Real.log (162143/320000:ℝ) := by
    rw [show (162143/160000:ℝ)=(2:ℝ)^1*(162143/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_113 {m : ℝ} (hm : m∈Icc (2593391/5120000:ℝ) (162143/320000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4942514533/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_113 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (162143/320000:ℝ)*(-6798423339/10000000000:ℝ)-(162143/320000:ℝ)+1+
      (((2593391/5120000:ℝ)-1-(-3399211669/5000000000:ℝ))/(1-(2593391/5120000:ℝ))^2)*(4942514533/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_114 : Bounds (Real.log (519037/1024000:ℝ)) (-6794966341/10000000000:ℝ) (-339748317/500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-7037/512000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (519037/512000:ℝ)=1*Real.log 2+Real.log (519037/1024000:ℝ) := by
    rw [show (519037/512000:ℝ)=(2:ℝ)^1*(519037/1024000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_114 {m : ℝ} (hm : m∈Icc (162143/320000:ℝ) (519037/1024000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (988870901/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_114 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (519037/1024000:ℝ)*(-6794966341/10000000000:ℝ)-(519037/1024000:ℝ)+1+
      (((162143/320000:ℝ)-1-(-339748317/500000000:ℝ))/(1-(162143/320000:ℝ))^2)*(988870901/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_115 : Bounds (Real.log (1298041/2560000:ℝ)) (-6791510537/10000000000:ℝ) (-848938817/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-18041/1280000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1298041/1280000:ℝ)=1*Real.log 2+Real.log (1298041/2560000:ℝ) := by
    rw [show (1298041/1280000:ℝ)=(2:ℝ)^1*(1298041/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_115 {m : ℝ} (hm : m∈Icc (519037/1024000:ℝ) (1298041/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (247309719/500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_115 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1298041/2560000:ℝ)*(-6791510537/10000000000:ℝ)-(1298041/2560000:ℝ)+1+
      (((519037/1024000:ℝ)-1-(-848938817/1250000000:ℝ))/(1-(519037/1024000:ℝ))^2)*(247309719/500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_116 : Bounds (Real.log (2596979/5120000:ℝ)) (-6788055927/10000000000:ℝ) (-3394027963/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-36979/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2596979/2560000:ℝ)=1*Real.log 2+Real.log (2596979/5120000:ℝ) := by
    rw [show (2596979/2560000:ℝ)=(2:ℝ)^1*(2596979/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_116 {m : ℝ} (hm : m∈Icc (1298041/2560000:ℝ) (2596979/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2474017079/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_116 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2596979/5120000:ℝ)*(-6788055927/10000000000:ℝ)-(2596979/5120000:ℝ)+1+
      (((1298041/2560000:ℝ)-1-(-3394027963/5000000000:ℝ))/(1-(1298041/2560000:ℝ))^2)*(2474017079/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_117 : Bounds (Real.log (649469/1280000:ℝ)) (-678460251/1000000000:ℝ) (-6784602509/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-9469/640000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (649469/640000:ℝ)=1*Real.log 2+Real.log (649469/1280000:ℝ) := by
    rw [show (649469/640000:ℝ)=(2:ℝ)^1*(649469/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_117 {m : ℝ} (hm : m∈Icc (2596979/5120000:ℝ) (649469/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4949873839/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_117 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (649469/1280000:ℝ)*(-678460251/1000000000:ℝ)-(649469/1280000:ℝ)+1+
      (((2596979/5120000:ℝ)-1-(-6784602509/10000000000:ℝ))/(1-(2596979/5120000:ℝ))^2)*(4949873839/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_118 : Bounds (Real.log (2598773/5120000:ℝ)) (-1356230057/2000000000:ℝ) (-1695287571/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-38773/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2598773/2560000:ℝ)=1*Real.log 2+Real.log (2598773/5120000:ℝ) := by
    rw [show (2598773/2560000:ℝ)=(2:ℝ)^1*(2598773/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_118 {m : ℝ} (hm : m∈Icc (649469/1280000:ℝ) (2598773/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (309482089/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_118 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2598773/5120000:ℝ)*(-1356230057/2000000000:ℝ)-(2598773/5120000:ℝ)+1+
      (((649469/1280000:ℝ)-1-(-1695287571/2500000000:ℝ))/(1-(649469/1280000:ℝ))^2)*(309482089/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_119 : Bounds (Real.log (5198443/10240000:ℝ)) (-338971231/500000000:ℝ) (-6779424619/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-78443/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5198443/5120000:ℝ)=1*Real.log 2+Real.log (5198443/10240000:ℝ) := by
    rw [show (5198443/5120000:ℝ)=(2:ℝ)^1*(5198443/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_119 {m : ℝ} (hm : m∈Icc (2598773/5120000:ℝ) (5198443/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (309597057/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_119 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5198443/10240000:ℝ)*(-338971231/500000000:ℝ)-(5198443/10240000:ℝ)+1+
      (((2598773/5120000:ℝ)-1-(-6779424619/10000000000:ℝ))/(1-(2598773/5120000:ℝ))^2)*(309597057/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_120 : Bounds (Real.log (259967/512000:ℝ)) (-1694424813/2500000000:ℝ) (-6777699251/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-3967/256000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (259967/256000:ℝ)=1*Real.log 2+Real.log (259967/512000:ℝ) := by
    rw [show (259967/256000:ℝ)=(2:ℝ)^1*(259967/512000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_120 {m : ℝ} (hm : m∈Icc (5198443/10240000:ℝ) (259967/512000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (247723631/500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_120 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (259967/512000:ℝ)*(-1694424813/2500000000:ℝ)-(259967/512000:ℝ)+1+
      (((5198443/10240000:ℝ)-1-(-6777699251/10000000000:ℝ))/(1-(5198443/10240000:ℝ))^2)*(247723631/500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_121 : Bounds (Real.log (5200237/10240000:ℝ)) (-3387987091/5000000000:ℝ) (-6775974181/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-80237/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5200237/5120000:ℝ)=1*Real.log 2+Real.log (5200237/10240000:ℝ) := by
    rw [show (5200237/5120000:ℝ)=(2:ℝ)^1*(5200237/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_121 {m : ℝ} (hm : m∈Icc (259967/512000:ℝ) (5200237/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (309712019/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_121 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5200237/10240000:ℝ)*(-3387987091/5000000000:ℝ)-(5200237/10240000:ℝ)+1+
      (((259967/512000:ℝ)-1-(-6775974181/10000000000:ℝ))/(1-(259967/512000:ℝ))^2)*(309712019/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_122 : Bounds (Real.log (2600567/5120000:ℝ)) (-6774249409/10000000000:ℝ) (-105847647/156250000:ℝ) := by
  have hh := log_taylor_bounds (x := (-40567/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2600567/2560000:ℝ)=1*Real.log 2+Real.log (2600567/5120000:ℝ) := by
    rw [show (2600567/2560000:ℝ)=(2:ℝ)^1*(2600567/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_122 {m : ℝ} (hm : m∈Icc (5200237/10240000:ℝ) (2600567/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1239077991/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_122 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2600567/5120000:ℝ)*(-6774249409/10000000000:ℝ)-(2600567/5120000:ℝ)+1+
      (((5200237/10240000:ℝ)-1-(-105847647/156250000:ℝ))/(1-(5200237/10240000:ℝ))^2)*(1239077991/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_123 : Bounds (Real.log (5202031/10240000:ℝ)) (-3386262467/5000000000:ℝ) (-6772524933/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-82031/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5202031/5120000:ℝ)=1*Real.log 2+Real.log (5202031/10240000:ℝ) := by
    rw [show (5202031/5120000:ℝ)=(2:ℝ)^1*(5202031/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_123 {m : ℝ} (hm : m∈Icc (2600567/5120000:ℝ) (5202031/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (12393079/25000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_123 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5202031/10240000:ℝ)*(-3386262467/5000000000:ℝ)-(5202031/10240000:ℝ)+1+
      (((2600567/5120000:ℝ)-1-(-6772524933/10000000000:ℝ))/(1-(2600567/5120000:ℝ))^2)*(12393079/25000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_124 : Bounds (Real.log (325183/640000:ℝ)) (-1692700189/2500000000:ℝ) (-1354160151/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-5183/320000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (325183/320000:ℝ)=1*Real.log 2+Real.log (325183/640000:ℝ) := by
    rw [show (325183/320000:ℝ)=(2:ℝ)^1*(325183/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_124 {m : ℝ} (hm : m∈Icc (5202031/10240000:ℝ) (325183/640000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4958151211/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_124 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (325183/640000:ℝ)*(-1692700189/2500000000:ℝ)-(325183/640000:ℝ)+1+
      (((5202031/10240000:ℝ)-1-(-1354160151/2000000000:ℝ))/(1-(5202031/10240000:ℝ))^2)*(4958151211/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_125 : Bounds (Real.log (208153/409600:ℝ)) (-1692269219/2500000000:ℝ) (-10830523/16000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-3353/204800:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (208153/204800:ℝ)=1*Real.log 2+Real.log (208153/409600:ℝ) := by
    rw [show (208153/204800:ℝ)=(2:ℝ)^1*(208153/409600:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_125 {m : ℝ} (hm : m∈Icc (325183/640000:ℝ) (208153/409600:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4959070799/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_125 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (208153/409600:ℝ)*(-1692269219/2500000000:ℝ)-(208153/409600:ℝ)+1+
      (((325183/640000:ℝ)-1-(-10830523/16000000:ℝ))/(1-(325183/640000:ℝ))^2)*(4959070799/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_126 : Bounds (Real.log (2602361/5120000:ℝ)) (-1691838323/2500000000:ℝ) (-6767353291/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-42361/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2602361/2560000:ℝ)=1*Real.log 2+Real.log (2602361/5120000:ℝ) := by
    rw [show (2602361/2560000:ℝ)=(2:ℝ)^1*(2602361/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_126 {m : ℝ} (hm : m∈Icc (208153/409600:ℝ) (2602361/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4959990363/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_126 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2602361/5120000:ℝ)*(-1691838323/2500000000:ℝ)-(2602361/5120000:ℝ)+1+
      (((208153/409600:ℝ)-1-(-6767353291/10000000000:ℝ))/(1-(208153/409600:ℝ))^2)*(4959990363/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_127 : Bounds (Real.log (5205619/10240000:ℝ)) (-3382815003/5000000000:ℝ) (-1353126001/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-85619/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5205619/5120000:ℝ)=1*Real.log 2+Real.log (5205619/10240000:ℝ) := by
    rw [show (5205619/5120000:ℝ)=(2:ℝ)^1*(5205619/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_127 {m : ℝ} (hm : m∈Icc (2602361/5120000:ℝ) (5205619/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4960909903/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_127 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5205619/10240000:ℝ)*(-3382815003/5000000000:ℝ)-(5205619/10240000:ℝ)+1+
      (((2602361/5120000:ℝ)-1-(-1353126001/2000000000:ℝ))/(1-(2602361/5120000:ℝ))^2)*(4960909903/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_128 : Bounds (Real.log (1301629/2560000:ℝ)) (-845488377/1250000000:ℝ) (-1352781403/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-21629/1280000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1301629/1280000:ℝ)=1*Real.log 2+Real.log (1301629/2560000:ℝ) := by
    rw [show (1301629/1280000:ℝ)=(2:ℝ)^1*(1301629/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_128 {m : ℝ} (hm : m∈Icc (5205619/10240000:ℝ) (1301629/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4961829419/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_128 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1301629/2560000:ℝ)*(-845488377/1250000000:ℝ)-(1301629/2560000:ℝ)+1+
      (((5205619/10240000:ℝ)-1-(-1352781403/2000000000:ℝ))/(1-(5205619/10240000:ℝ))^2)*(4961829419/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_129 : Bounds (Real.log (5207413/10240000:ℝ)) (-6762184323/10000000000:ℝ) (-3381092161/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-87413/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5207413/5120000:ℝ)=1*Real.log 2+Real.log (5207413/10240000:ℝ) := by
    rw [show (5207413/5120000:ℝ)=(2:ℝ)^1*(5207413/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_129 {m : ℝ} (hm : m∈Icc (1301629/2560000:ℝ) (5207413/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4962748911/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_129 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5207413/10240000:ℝ)*(-6762184323/10000000000:ℝ)-(5207413/10240000:ℝ)+1+
      (((1301629/2560000:ℝ)-1-(-3381092161/5000000000:ℝ))/(1-(1301629/2560000:ℝ))^2)*(4962748911/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_130 : Bounds (Real.log (520831/1024000:ℝ)) (-6760461927/10000000000:ℝ) (-3380230963/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-8831/512000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (520831/512000:ℝ)=1*Real.log 2+Real.log (520831/1024000:ℝ) := by
    rw [show (520831/512000:ℝ)=(2:ℝ)^1*(520831/1024000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_130 {m : ℝ} (hm : m∈Icc (5207413/10240000:ℝ) (520831/1024000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (248183419/500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_130 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (520831/1024000:ℝ)*(-6760461927/10000000000:ℝ)-(520831/1024000:ℝ)+1+
      (((5207413/10240000:ℝ)-1-(-3380230963/5000000000:ℝ))/(1-(5207413/10240000:ℝ))^2)*(248183419/500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_131 : Bounds (Real.log (5209207/10240000:ℝ)) (-1689684957/2500000000:ℝ) (-6758739827/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-89207/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5209207/5120000:ℝ)=1*Real.log 2+Real.log (5209207/10240000:ℝ) := by
    rw [show (5209207/5120000:ℝ)=(2:ℝ)^1*(5209207/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_131 {m : ℝ} (hm : m∈Icc (520831/1024000:ℝ) (5209207/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (310286739/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_131 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5209207/10240000:ℝ)*(-1689684957/2500000000:ℝ)-(5209207/10240000:ℝ)+1+
      (((520831/1024000:ℝ)-1-(-6758739827/10000000000:ℝ))/(1-(520831/1024000:ℝ))^2)*(310286739/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_132 : Bounds (Real.log (651263/1280000:ℝ)) (-270280721/400000000:ℝ) (-844627253/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-11263/640000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (651263/640000:ℝ)=1*Real.log 2+Real.log (651263/1280000:ℝ) := by
    rw [show (651263/640000:ℝ)=(2:ℝ)^1*(651263/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_132 {m : ℝ} (hm : m∈Icc (5209207/10240000:ℝ) (651263/1280000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (993101449/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_132 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (651263/1280000:ℝ)*(-270280721/400000000:ℝ)-(651263/1280000:ℝ)+1+
      (((5209207/10240000:ℝ)-1-(-844627253/1250000000:ℝ))/(1-(5209207/10240000:ℝ))^2)*(993101449/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_133 : Bounds (Real.log (5211001/10240000:ℝ)) (-3377648259/5000000000:ℝ) (-6755296517/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-91001/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5211001/5120000:ℝ)=1*Real.log 2+Real.log (5211001/10240000:ℝ) := by
    rw [show (5211001/5120000:ℝ)=(2:ℝ)^1*(5211001/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_133 {m : ℝ} (hm : m∈Icc (651263/1280000:ℝ) (5211001/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4966426641/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_133 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5211001/10240000:ℝ)*(-3377648259/5000000000:ℝ)-(5211001/10240000:ℝ)+1+
      (((651263/1280000:ℝ)-1-(-6755296517/10000000000:ℝ))/(1-(651263/1280000:ℝ))^2)*(4966426641/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_134 : Bounds (Real.log (2605949/5120000:ℝ)) (-1688393827/2500000000:ℝ) (-6753575307/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-45949/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2605949/2560000:ℝ)=1*Real.log 2+Real.log (2605949/5120000:ℝ) := by
    rw [show (2605949/2560000:ℝ)=(2:ℝ)^1*(2605949/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_134 {m : ℝ} (hm : m∈Icc (5211001/10240000:ℝ) (2605949/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2483673007/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_134 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2605949/5120000:ℝ)*(-1688393827/2500000000:ℝ)-(2605949/5120000:ℝ)+1+
      (((5211001/10240000:ℝ)-1-(-6753575307/10000000000:ℝ))/(1-(5211001/10240000:ℝ))^2)*(2483673007/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_135 : Bounds (Real.log (1042559/2048000:ℝ)) (-3375927197/5000000000:ℝ) (-6751854393/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-18559/1024000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1042559/1024000:ℝ)=1*Real.log 2+Real.log (1042559/2048000:ℝ) := by
    rw [show (1042559/1024000:ℝ)=(2:ℝ)^1*(1042559/2048000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_135 {m : ℝ} (hm : m∈Icc (2605949/5120000:ℝ) (1042559/2048000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4968265363/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_135 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1042559/2048000:ℝ)*(-3375927197/5000000000:ℝ)-(1042559/2048000:ℝ)+1+
      (((2605949/5120000:ℝ)-1-(-6751854393/10000000000:ℝ))/(1-(2605949/5120000:ℝ))^2)*(4968265363/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_136 : Bounds (Real.log (1303423/2560000:ℝ)) (-421883361/625000000:ℝ) (-270005351/400000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-23423/1280000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1303423/1280000:ℝ)=1*Real.log 2+Real.log (1303423/2560000:ℝ) := by
    rw [show (1303423/1280000:ℝ)=(2:ℝ)^1*(1303423/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_136 {m : ℝ} (hm : m∈Icc (1042559/2048000:ℝ) (1303423/2560000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (4969184689/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_136 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1303423/2560000:ℝ)*(-421883361/625000000:ℝ)-(1303423/2560000:ℝ)+1+
      (((1042559/2048000:ℝ)-1-(-270005351/400000000:ℝ))/(1-(1042559/2048000:ℝ))^2)*(4969184689/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_137 : Bounds (Real.log (5214589/10240000:ℝ)) (-3374206727/5000000000:ℝ) (-6748413453/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-94589/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5214589/5120000:ℝ)=1*Real.log 2+Real.log (5214589/10240000:ℝ) := by
    rw [show (5214589/5120000:ℝ)=(2:ℝ)^1*(5214589/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_137 {m : ℝ} (hm : m∈Icc (1303423/2560000:ℝ) (5214589/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (497010399/1000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_137 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5214589/10240000:ℝ)*(-3374206727/5000000000:ℝ)-(5214589/10240000:ℝ)+1+
      (((1303423/2560000:ℝ)-1-(-6748413453/10000000000:ℝ))/(1-(1303423/2560000:ℝ))^2)*(497010399/1000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_138 : Bounds (Real.log (2607743/5120000:ℝ)) (-1686673357/2500000000:ℝ) (-6746693427/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-47743/2560000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2607743/2560000:ℝ)=1*Real.log 2+Real.log (2607743/5120000:ℝ) := by
    rw [show (2607743/2560000:ℝ)=(2:ℝ)^1*(2607743/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_138 {m : ℝ} (hm : m∈Icc (5214589/10240000:ℝ) (2607743/5120000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1242755817/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_138 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (2607743/5120000:ℝ)*(-1686673357/2500000000:ℝ)-(2607743/5120000:ℝ)+1+
      (((5214589/10240000:ℝ)-1-(-6746693427/10000000000:ℝ))/(1-(5214589/10240000:ℝ))^2)*(1242755817/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_139 : Bounds (Real.log (5216383/10240000:ℝ)) (-3372486849/5000000000:ℝ) (-6744973697/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-96383/5120000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5216383/5120000:ℝ)=1*Real.log 2+Real.log (5216383/10240000:ℝ) := by
    rw [show (5216383/5120000:ℝ)=(2:ℝ)^1*(5216383/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_139 {m : ℝ} (hm : m∈Icc (2607743/5120000:ℝ) (5216383/10240000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2485971261/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_139 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (5216383/10240000:ℝ)*(-3372486849/5000000000:ℝ)-(5216383/10240000:ℝ)+1+
      (((2607743/5120000:ℝ)-1-(-6744973697/10000000000:ℝ))/(1-(2607743/5120000:ℝ))^2)*(2485971261/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_2_140 : Bounds (Real.log (1019/2000:ℝ)) (-842906783/1250000000:ℝ) (-6743254263/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-19/1000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1019/1000:ℝ)=1*Real.log 2+Real.log (1019/2000:ℝ) := by
    rw [show (1019/1000:ℝ)=(2:ℝ)^1*(1019/2000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_2_140 {m : ℝ} (hm : m∈Icc (5216383/10240000:ℝ) (1019/2000:ℝ)) :
    (671/2000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (621607719/1250000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_2_140 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (671/2000:ℝ)< (1019/2000:ℝ)*(-842906783/1250000000:ℝ)-(1019/2000:ℝ)+1+
      (((5216383/10240000:ℝ)-1-(-6743254263/10000000000:ℝ))/(1-(5216383/10240000:ℝ))^2)*(621607719/1250000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

end SparseLowerTail.Section05.CoverGeometry

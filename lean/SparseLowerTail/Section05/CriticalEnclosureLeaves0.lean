import SparseLowerTail.Section05.CriticalEnclosureBounds

/-! Exact one-variable FB1 enclosure leaves. Log Taylor and rational cuberoot
witnesses are checked by the kernel; no numerical evaluator result is assumed. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Section02 Section04 Numerics
set_option maxHeartbeats 800000
set_option maxRecDepth 5000

private theorem enclosureLog_0_0 : Bounds (Real.log (2183/10000:ℝ)) (-3043770031/2000000000:ℝ) (-7609425077/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (317/2500:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (2183/2500:ℝ)=2*Real.log 2+Real.log (2183/10000:ℝ) := by
    rw [show (2183/2500:ℝ)=(2:ℝ)^2*(2183/10000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_0_0 {m : ℝ} (hm : m∈Icc (1091/5000:ℝ) (2183/10000:ℝ)) :
    (4627799/10000000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1054150071/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_0_0 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (4627799/10000000:ℝ)< (2183/10000:ℝ)*(-3043770031/2000000000:ℝ)-(2183/10000:ℝ)+1+
      (((1091/5000:ℝ)-1-(-7609425077/5000000000:ℝ))/(1-(1091/5000:ℝ))^2)*(1054150071/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_0_1 : Bounds (Real.log (273/1250:ℝ)) (-950891897/625000000:ℝ) (-15214270351/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (79/625:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (546/625:ℝ)=2*Real.log 2+Real.log (273/1250:ℝ) := by
    rw [show (546/625:ℝ)=(2:ℝ)^2*(273/1250:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_0_1 {m : ℝ} (hm : m∈Icc (2183/10000:ℝ) (273/1250:ℝ)) :
    (4627799/10000000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (529209633/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_0_1 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (4627799/10000000:ℝ)< (273/1250:ℝ)*(-950891897/625000000:ℝ)-(273/1250:ℝ)+1+
      (((2183/10000:ℝ)-1-(-15214270351/10000000000:ℝ))/(1-(2183/10000:ℝ))^2)*(529209633/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_0_2 : Bounds (Real.log (4369/20000:ℝ)) (-3802995309/2500000000:ℝ) (-3042396247/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (631/5000:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (4369/5000:ℝ)=2*Real.log 2+Real.log (4369/20000:ℝ) := by
    rw [show (4369/5000:ℝ)=(2:ℝ)^2*(4369/20000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_0_2 {m : ℝ} (hm : m∈Icc (273/1250:ℝ) (4369/20000:ℝ)) :
    (4627799/10000000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (531329081/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_0_2 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (4627799/10000000:ℝ)< (4369/20000:ℝ)*(-3802995309/2500000000:ℝ)-(4369/20000:ℝ)+1+
      (((273/1250:ℝ)-1-(-3042396247/2000000000:ℝ))/(1-(273/1250:ℝ))^2)*(531329081/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_0_3 : Bounds (Real.log (437/2000:ℝ)) (-3041938529/2000000000:ℝ) (-3802423161/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (63/500:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (437/500:ℝ)=2*Real.log 2+Real.log (437/2000:ℝ) := by
    rw [show (437/500:ℝ)=(2:ℝ)^2*(437/2000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_0_3 {m : ℝ} (hm : m∈Icc (4369/20000:ℝ) (437/2000:ℝ)) :
    (4627799/10000000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (33273951/312500000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_0_3 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (4627799/10000000:ℝ)< (437/2000:ℝ)*(-3041938529/2000000000:ℝ)-(437/2000:ℝ)+1+
      (((4369/20000:ℝ)-1-(-3802423161/2500000000:ℝ))/(1-(4369/20000:ℝ))^2)*(33273951/312500000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_0_4 : Bounds (Real.log (4371/20000:ℝ)) (-15207404577/10000000000:ℝ) (-475231393/312500000:ℝ) := by
  have hh := log_taylor_bounds (x := (629/5000:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (4371/5000:ℝ)=2*Real.log 2+Real.log (4371/20000:ℝ) := by
    rw [show (4371/5000:ℝ)=(2:ℝ)^2*(4371/20000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_0_4 {m : ℝ} (hm : m∈Icc (437/2000:ℝ) (4371/20000:ℝ)) :
    (4627799/10000000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (533433673/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_0_4 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (4627799/10000000:ℝ)< (4371/20000:ℝ)*(-15207404577/10000000000:ℝ)-(4371/20000:ℝ)+1+
      (((437/2000:ℝ)-1-(-475231393/312500000:ℝ))/(1-(437/2000:ℝ))^2)*(533433673/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_0_5 : Bounds (Real.log (1093/5000:ℝ)) (-15205117033/10000000000:ℝ) (-1900639629/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (157/1250:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1093/1250:ℝ)=2*Real.log 2+Real.log (1093/5000:ℝ) := by
    rw [show (1093/1250:ℝ)=(2:ℝ)^2*(1093/5000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_0_5 {m : ℝ} (hm : m∈Icc (4371/20000:ℝ) (1093/5000:ℝ)) :
    (4627799/10000000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1068960973/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_0_5 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (4627799/10000000:ℝ)< (1093/5000:ℝ)*(-15205117033/10000000000:ℝ)-(1093/5000:ℝ)+1+
      (((4371/20000:ℝ)-1-(-1900639629/1250000000:ℝ))/(1-(4371/20000:ℝ))^2)*(1068960973/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

end SparseLowerTail.Section05.CoverGeometry

import SparseLowerTail.Section05.CriticalEnclosureBounds

/-! Exact one-variable FB1 enclosure leaves. Log Taylor and rational cuberoot
witnesses are checked by the kernel; no numerical evaluator result is assumed. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Section02 Section04 Numerics
set_option maxHeartbeats 800000
set_option maxRecDepth 5000

private theorem enclosureLog_1_0 : Bounds (Real.log (18603/80000:ℝ)) (-14587037767/10000000000:ℝ) (-7293518883/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (1397/20000:ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (18603/20000:ℝ)=2*Real.log 2+Real.log (18603/80000:ℝ) := by
    rw [show (18603/20000:ℝ)=(2:ℝ)^2*(18603/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_0 {m : ℝ} (hm : m∈Icc (1093/5000:ℝ) (18603/80000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (133880923/1250000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_0 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (18603/80000:ℝ)*(-14587037767/10000000000:ℝ)-(18603/80000:ℝ)+1+
      (((1093/5000:ℝ)-1-(-7293518883/5000000000:ℝ))/(1-(1093/5000:ℝ))^2)*(133880923/1250000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_1 : Bounds (Real.log (9859/40000:ℝ)) (-7002473553/5000000000:ℝ) (-2800989421/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (141/10000:ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (9859/10000:ℝ)=2*Real.log 2+Real.log (9859/40000:ℝ) := by
    rw [show (9859/10000:ℝ)=(2:ℝ)^2*(9859/40000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_1 {m : ℝ} (hm : m∈Icc (18603/80000:ℝ) (9859/40000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1497297883/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_1 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (9859/40000:ℝ)*(-7002473553/5000000000:ℝ)-(9859/40000:ℝ)+1+
      (((18603/80000:ℝ)-1-(-2800989421/2000000000:ℝ))/(1-(18603/80000:ℝ))^2)*(1497297883/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_2 : Bounds (Real.log (20833/80000:ℝ)) (-3363720917/2500000000:ℝ) (-13454883667/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-833/20000:ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (20833/20000:ℝ)=2*Real.log 2+Real.log (20833/80000:ℝ) := by
    rw [show (20833/20000:ℝ)=(2:ℝ)^2*(20833/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_2 {m : ℝ} (hm : m∈Icc (9859/40000:ℝ) (20833/80000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1792143851/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_2 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (20833/80000:ℝ)*(-3363720917/2500000000:ℝ)-(20833/80000:ℝ)+1+
      (((9859/40000:ℝ)-1-(-13454883667/10000000000:ℝ))/(1-(9859/40000:ℝ))^2)*(1792143851/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_3 : Bounds (Real.log (5487/20000:ℝ)) (-2586701231/2000000000:ℝ) (-6466753077/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-487/5000:ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (5487/5000:ℝ)=2*Real.log 2+Real.log (5487/20000:ℝ) := by
    rw [show (5487/5000:ℝ)=(2:ℝ)^2*(5487/20000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_3 {m : ℝ} (hm : m∈Icc (20833/80000:ℝ) (5487/20000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (203620891/1000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_3 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (5487/20000:ℝ)*(-2586701231/2000000000:ℝ)-(5487/20000:ℝ)+1+
      (((20833/80000:ℝ)-1-(-6466753077/5000000000:ℝ))/(1-(20833/80000:ℝ))^2)*(203620891/1000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_4 : Bounds (Real.log (45011/160000:ℝ)) (-12682669109/10000000000:ℝ) (-3170667277/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-5011/40000:ℝ)) (by norm_num) 13
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (45011/40000:ℝ)=2*Real.log 2+Real.log (45011/160000:ℝ) := by
    rw [show (45011/40000:ℝ)=(2:ℝ)^2*(45011/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_4 {m : ℝ} (hm : m∈Icc (5487/20000:ℝ) (45011/160000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (45054929/200000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_4 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (45011/160000:ℝ)*(-12682669109/10000000000:ℝ)-(45011/160000:ℝ)+1+
      (((5487/20000:ℝ)-1-(-3170667277/2500000000:ℝ))/(1-(5487/20000:ℝ))^2)*(45054929/200000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_5 : Bounds (Real.log (23063/80000:ℝ)) (-12437970329/10000000000:ℝ) (-1554746291/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-3063/20000:ℝ)) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (23063/20000:ℝ)=2*Real.log 2+Real.log (23063/80000:ℝ) := by
    rw [show (23063/20000:ℝ)=(2:ℝ)^2*(23063/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_5 {m : ℝ} (hm : m∈Icc (45011/160000:ℝ) (23063/80000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2354120807/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_5 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (23063/80000:ℝ)*(-12437970329/10000000000:ℝ)-(23063/80000:ℝ)+1+
      (((45011/160000:ℝ)-1-(-1554746291/1250000000:ℝ))/(1-(45011/160000:ℝ))^2)*(2354120807/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_6 : Bounds (Real.log (47241/160000:ℝ)) (-12199116557/10000000000:ℝ) (-3049779139/2500000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-7241/40000:ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (47241/40000:ℝ)=2*Real.log 2+Real.log (47241/160000:ℝ) := by
    rw [show (47241/40000:ℝ)=(2:ℝ)^2*(47241/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_6 {m : ℝ} (hm : m∈Icc (23063/80000:ℝ) (47241/160000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (98079881/400000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_6 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (47241/160000:ℝ)*(-12199116557/10000000000:ℝ)-(47241/160000:ℝ)+1+
      (((23063/80000:ℝ)-1-(-3049779139/2500000000:ℝ))/(1-(23063/80000:ℝ))^2)*(98079881/400000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_7 : Bounds (Real.log (12089/40000:ℝ)) (-11965835059/10000000000:ℝ) (-5982917529/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-2089/10000:ℝ)) (by norm_num) 17
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (12089/10000:ℝ)=2*Real.log 2+Real.log (12089/40000:ℝ) := by
    rw [show (12089/10000:ℝ)=(2:ℝ)^2*(12089/40000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_7 {m : ℝ} (hm : m∈Icc (47241/160000:ℝ) (12089/40000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (636737737/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_7 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (12089/40000:ℝ)*(-11965835059/10000000000:ℝ)-(12089/40000:ℝ)+1+
      (((47241/160000:ℝ)-1-(-5982917529/5000000000:ℝ))/(1-(47241/160000:ℝ))^2)*(636737737/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_8 : Bounds (Real.log (97827/320000:ℝ)) (-11851203833/10000000000:ℝ) (-1481400479/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-17827/80000:ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (97827/80000:ℝ)=2*Real.log 2+Real.log (97827/320000:ℝ) := by
    rw [show (97827/80000:ℝ)=(2:ℝ)^2*(97827/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_8 {m : ℝ} (hm : m∈Icc (12089/40000:ℝ) (97827/320000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2639431011/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_8 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (97827/320000:ℝ)*(-11851203833/10000000000:ℝ)-(97827/320000:ℝ)+1+
      (((12089/40000:ℝ)-1-(-1481400479/1250000000:ℝ))/(1-(12089/40000:ℝ))^2)*(2639431011/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_9 : Bounds (Real.log (49471/160000:ℝ)) (-146723397/125000000:ℝ) (-11737871759/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-9471/40000:ℝ)) (by norm_num) 19
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (49471/40000:ℝ)=2*Real.log 2+Real.log (49471/160000:ℝ) := by
    rw [show (49471/40000:ℝ)=(2:ℝ)^2*(49471/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_9 {m : ℝ} (hm : m∈Icc (97827/320000:ℝ) (49471/160000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1342428759/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_9 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (49471/160000:ℝ)*(-146723397/125000000:ℝ)-(49471/160000:ℝ)+1+
      (((97827/320000:ℝ)-1-(-11737871759/10000000000:ℝ))/(1-(97827/320000:ℝ))^2)*(1342428759/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_10 : Bounds (Real.log (100057/320000:ℝ)) (-5812904861/5000000000:ℝ) (-11625809721/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-20057/80000:ℝ)) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (100057/80000:ℝ)=2*Real.log 2+Real.log (100057/320000:ℝ) := by
    rw [show (100057/80000:ℝ)=(2:ℝ)^2*(100057/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_10 {m : ℝ} (hm : m∈Icc (49471/160000:ℝ) (100057/320000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (109191731/400000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_10 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (100057/320000:ℝ)*(-5812904861/5000000000:ℝ)-(100057/320000:ℝ)+1+
      (((49471/160000:ℝ)-1-(-11625809721/10000000000:ℝ))/(1-(49471/160000:ℝ))^2)*(109191731/400000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_11 : Bounds (Real.log (25293/80000:ℝ)) (-11514989571/10000000000:ℝ) (-1151498957/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-5293/20000:ℝ)) (by norm_num) 21
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (25293/20000:ℝ)=2*Real.log 2+Real.log (25293/80000:ℝ) := by
    rw [show (25293/20000:ℝ)=(2:ℝ)^2*(25293/80000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_11 {m : ℝ} (hm : m∈Icc (100057/320000:ℝ) (25293/80000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (554854447/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_11 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (25293/80000:ℝ)*(-11514989571/10000000000:ℝ)-(25293/80000:ℝ)+1+
      (((100057/320000:ℝ)-1-(-1151498957/1000000000:ℝ))/(1-(100057/320000:ℝ))^2)*(554854447/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_12 : Bounds (Real.log (203459/640000:ℝ)) (-573001833/500000000:ℝ) (-11460036659/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-43459/160000:ℝ)) (by norm_num) 21
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (203459/160000:ℝ)=2*Real.log 2+Real.log (203459/640000:ℝ) := by
    rw [show (203459/160000:ℝ)=(2:ℝ)^2*(203459/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_12 {m : ℝ} (hm : m∈Icc (25293/80000:ℝ) (203459/640000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2818325127/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_12 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (203459/640000:ℝ)*(-573001833/500000000:ℝ)-(203459/640000:ℝ)+1+
      (((25293/80000:ℝ)-1-(-11460036659/10000000000:ℝ))/(1-(25293/80000:ℝ))^2)*(2818325127/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_13 : Bounds (Real.log (102287/320000:ℝ)) (-5702692041/5000000000:ℝ) (-11405384081/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-22287/80000:ℝ)) (by norm_num) 21
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (102287/80000:ℝ)=2*Real.log 2+Real.log (102287/320000:ℝ) := by
    rw [show (102287/80000:ℝ)=(2:ℝ)^2*(102287/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_13 {m : ℝ} (hm : m∈Icc (203459/640000:ℝ) (102287/320000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2840200617/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_13 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (102287/320000:ℝ)*(-5702692041/5000000000:ℝ)-(102287/320000:ℝ)+1+
      (((203459/640000:ℝ)-1-(-11405384081/10000000000:ℝ))/(1-(203459/640000:ℝ))^2)*(2840200617/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_14 : Bounds (Real.log (205689/640000:ℝ)) (-11351028571/10000000000:ℝ) (-1135102857/1000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-45689/160000:ℝ)) (by norm_num) 22
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (205689/160000:ℝ)=2*Real.log 2+Real.log (205689/640000:ℝ) := by
    rw [show (205689/160000:ℝ)=(2:ℝ)^2*(205689/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_14 {m : ℝ} (hm : m∈Icc (102287/320000:ℝ) (205689/640000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (57239597/200000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_14 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (205689/640000:ℝ)*(-11351028571/10000000000:ℝ)-(205689/640000:ℝ)+1+
      (((102287/320000:ℝ)-1-(-1135102857/1000000000:ℝ))/(1-(102287/320000:ℝ))^2)*(57239597/200000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_15 : Bounds (Real.log (51701/160000:ℝ)) (-2824241729/2500000000:ℝ) (-2259393383/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-11701/40000:ℝ)) (by norm_num) 22
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (51701/40000:ℝ)=2*Real.log 2+Real.log (51701/160000:ℝ) := by
    rw [show (51701/40000:ℝ)=(2:ℝ)^2*(51701/160000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_15 {m : ℝ} (hm : m∈Icc (205689/640000:ℝ) (51701/160000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (115346637/400000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_15 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (51701/160000:ℝ)*(-2824241729/2500000000:ℝ)-(51701/160000:ℝ)+1+
      (((205689/640000:ℝ)-1-(-2259393383/2000000000:ℝ))/(1-(205689/640000:ℝ))^2)*(115346637/400000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_16 : Bounds (Real.log (414723/1280000:ℝ)) (-2254009059/2000000000:ℝ) (-5635022647/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-94723/320000:ℝ)) (by norm_num) 22
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (414723/320000:ℝ)=2*Real.log 2+Real.log (414723/1280000:ℝ) := by
    rw [show (414723/320000:ℝ)=(2:ℝ)^2*(414723/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_16 {m : ℝ} (hm : m∈Icc (51701/160000:ℝ) (414723/1280000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (726315451/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_16 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (414723/1280000:ℝ)*(-2254009059/2000000000:ℝ)-(414723/1280000:ℝ)+1+
      (((51701/160000:ℝ)-1-(-5635022647/5000000000:ℝ))/(1-(51701/160000:ℝ))^2)*(726315451/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_17 : Bounds (Real.log (207919/640000:ℝ)) (-2810798989/2500000000:ℝ) (-2248639191/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-47919/160000:ℝ)) (by norm_num) 23
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (207919/160000:ℝ)=2*Real.log 2+Real.log (207919/640000:ℝ) := by
    rw [show (207919/160000:ℝ)=(2:ℝ)^2*(207919/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_17 {m : ℝ} (hm : m∈Icc (414723/1280000:ℝ) (207919/640000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2916026811/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_17 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (207919/640000:ℝ)*(-2810798989/2500000000:ℝ)-(207919/640000:ℝ)+1+
      (((414723/1280000:ℝ)-1-(-2248639191/2000000000:ℝ))/(1-(414723/1280000:ℝ))^2)*(2916026811/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_18 : Bounds (Real.log (416953/1280000:ℝ)) (-11216418513/10000000000:ℝ) (-701026157/625000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-96953/320000:ℝ)) (by norm_num) 23
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (416953/320000:ℝ)=2*Real.log 2+Real.log (416953/1280000:ℝ) := by
    rw [show (416953/320000:ℝ)=(2:ℝ)^2*(416953/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_18 {m : ℝ} (hm : m∈Icc (207919/640000:ℝ) (416953/1280000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2926770321/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_18 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (416953/1280000:ℝ)*(-11216418513/10000000000:ℝ)-(416953/1280000:ℝ)+1+
      (((207919/640000:ℝ)-1-(-701026157/625000000:ℝ))/(1-(207919/640000:ℝ))^2)*(2926770321/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_19 : Bounds (Real.log (104517/320000:ℝ)) (-5594856291/5000000000:ℝ) (-11189712581/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-24517/80000:ℝ)) (by norm_num) 23
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (104517/80000:ℝ)=2*Real.log 2+Real.log (104517/320000:ℝ) := by
    rw [show (104517/80000:ℝ)=(2:ℝ)^2*(104517/320000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_19 {m : ℝ} (hm : m∈Icc (416953/1280000:ℝ) (104517/320000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2937492669/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_19 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (104517/320000:ℝ)*(-5594856291/5000000000:ℝ)-(104517/320000:ℝ)+1+
      (((416953/1280000:ℝ)-1-(-11189712581/10000000000:ℝ))/(1-(416953/1280000:ℝ))^2)*(2937492669/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_20 : Bounds (Real.log (837251/2560000:ℝ)) (-2235277263/2000000000:ℝ) (-5588193157/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-197251/640000:ℝ)) (by norm_num) 23
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (837251/640000:ℝ)=2*Real.log 2+Real.log (837251/2560000:ℝ) := by
    rw [show (837251/640000:ℝ)=(2:ℝ)^2*(837251/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_20 {m : ℝ} (hm : m∈Icc (104517/320000:ℝ) (837251/2560000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2948194183/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_20 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (837251/2560000:ℝ)*(-2235277263/2000000000:ℝ)-(837251/2560000:ℝ)+1+
      (((104517/320000:ℝ)-1-(-5588193157/5000000000:ℝ))/(1-(104517/320000:ℝ))^2)*(2948194183/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_21 : Bounds (Real.log (419183/1280000:ℝ)) (-5581538891/5000000000:ℝ) (-11163077781/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-99183/320000:ℝ)) (by norm_num) 23
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (419183/320000:ℝ)=2*Real.log 2+Real.log (419183/1280000:ℝ) := by
    rw [show (419183/320000:ℝ)=(2:ℝ)^2*(419183/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_21 {m : ℝ} (hm : m∈Icc (837251/2560000:ℝ) (419183/1280000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (738384307/2500000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_21 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (419183/1280000:ℝ)*(-5581538891/5000000000:ℝ)-(419183/1280000:ℝ)+1+
      (((837251/2560000:ℝ)-1-(-11163077781/10000000000:ℝ))/(1-(837251/2560000:ℝ))^2)*(738384307/2500000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_22 : Bounds (Real.log (839481/2560000:ℝ)) (-5574893469/5000000000:ℝ) (-11149786937/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-199481/640000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (839481/640000:ℝ)=2*Real.log 2+Real.log (839481/2560000:ℝ) := by
    rw [show (839481/640000:ℝ)=(2:ℝ)^2*(839481/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_22 {m : ℝ} (hm : m∈Icc (419183/1280000:ℝ) (839481/2560000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (184929699/625000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_22 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (839481/2560000:ℝ)*(-5574893469/5000000000:ℝ)-(839481/2560000:ℝ)+1+
      (((419183/1280000:ℝ)-1-(-11149786937/10000000000:ℝ))/(1-(419183/1280000:ℝ))^2)*(184929699/625000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_23 : Bounds (Real.log (210149/640000:ℝ)) (-2227302747/2000000000:ℝ) (-5568256867/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-50149/160000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (210149/160000:ℝ)=2*Real.log 2+Real.log (210149/640000:ℝ) := by
    rw [show (210149/160000:ℝ)=(2:ℝ)^2*(210149/640000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_23 {m : ℝ} (hm : m∈Icc (839481/2560000:ℝ) (210149/640000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (296420809/1000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_23 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (210149/640000:ℝ)*(-2227302747/2000000000:ℝ)-(210149/640000:ℝ)+1+
      (((839481/2560000:ℝ)-1-(-5568256867/5000000000:ℝ))/(1-(839481/2560000:ℝ))^2)*(296420809/1000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_24 : Bounds (Real.log (841711/2560000:ℝ)) (-5561629063/5000000000:ℝ) (-17797213/16000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-201711/640000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (841711/640000:ℝ)=2*Real.log 2+Real.log (841711/2560000:ℝ) := by
    rw [show (841711/640000:ℝ)=(2:ℝ)^2*(841711/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_24 {m : ℝ} (hm : m∈Icc (210149/640000:ℝ) (841711/2560000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (593907197/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_24 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (841711/2560000:ℝ)*(-5561629063/5000000000:ℝ)-(841711/2560000:ℝ)+1+
      (((210149/640000:ℝ)-1-(-17797213/16000000:ℝ))/(1-(210149/640000:ℝ))^2)*(593907197/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_25 : Bounds (Real.log (1684537/5120000:ℝ)) (-2223327381/2000000000:ℝ) (-1389579613/1250000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-404537/1280000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1684537/1280000:ℝ)=2*Real.log 2+Real.log (1684537/5120000:ℝ) := by
    rw [show (1684537/1280000:ℝ)=(2:ℝ)^2*(1684537/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_25 {m : ℝ} (hm : m∈Icc (841711/2560000:ℝ) (1684537/5120000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2974858907/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_25 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (1684537/5120000:ℝ)*(-2223327381/2000000000:ℝ)-(1684537/5120000:ℝ)+1+
      (((841711/2560000:ℝ)-1-(-1389579613/1250000000:ℝ))/(1-(841711/2560000:ℝ))^2)*(2974858907/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_26 : Bounds (Real.log (421413/1280000:ℝ)) (-2222004013/2000000000:ℝ) (-347188127/312500000:ℝ) := by
  have hh := log_taylor_bounds (x := (-101413/320000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (421413/320000:ℝ)=2*Real.log 2+Real.log (421413/1280000:ℝ) := by
    rw [show (421413/320000:ℝ)=(2:ℝ)^2*(421413/1280000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_26 {m : ℝ} (hm : m∈Icc (1684537/5120000:ℝ) (421413/1280000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (595503703/2000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_26 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (421413/1280000:ℝ)*(-2222004013/2000000000:ℝ)-(421413/1280000:ℝ)+1+
      (((1684537/5120000:ℝ)-1-(-347188127/312500000:ℝ))/(1-(1684537/5120000:ℝ))^2)*(595503703/2000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_27 : Bounds (Real.log (1686767/5120000:ℝ)) (-11103407601/10000000000:ℝ) (-27758519/25000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-406767/1280000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1686767/1280000:ℝ)=2*Real.log 2+Real.log (1686767/5120000:ℝ) := by
    rw [show (1686767/1280000:ℝ)=(2:ℝ)^2*(1686767/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_27 {m : ℝ} (hm : m∈Icc (421413/1280000:ℝ) (1686767/5120000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (1490088447/5000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_27 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (1686767/5120000:ℝ)*(-11103407601/10000000000:ℝ)-(1686767/5120000:ℝ)+1+
      (((421413/1280000:ℝ)-1-(-27758519/25000000:ℝ))/(1-(421413/1280000:ℝ))^2)*(1490088447/5000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_28 : Bounds (Real.log (843941/2560000:ℝ)) (-5548399753/5000000000:ℝ) (-2219359901/2000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-203941/640000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (843941/640000:ℝ)=2*Real.log 2+Real.log (843941/2560000:ℝ) := by
    rw [show (843941/640000:ℝ)=(2:ℝ)^2*(843941/2560000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_28 {m : ℝ} (hm : m∈Icc (1686767/5120000:ℝ) (843941/2560000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2982834049/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_28 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (843941/2560000:ℝ)*(-5548399753/5000000000:ℝ)-(843941/2560000:ℝ)+1+
      (((1686767/5120000:ℝ)-1-(-2219359901/2000000000:ℝ))/(1-(1686767/5120000:ℝ))^2)*(2982834049/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_29 : Bounds (Real.log (1688997/5120000:ℝ)) (-443607831/400000000:ℝ) (-5545097887/5000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-408997/1280000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (1688997/1280000:ℝ)=2*Real.log 2+Real.log (1688997/5120000:ℝ) := by
    rw [show (1688997/1280000:ℝ)=(2:ℝ)^2*(1688997/5120000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_29 {m : ℝ} (hm : m∈Icc (843941/2560000:ℝ) (1688997/5120000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (46648281/156250000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_29 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (1688997/5120000:ℝ)*(-443607831/400000000:ℝ)-(1688997/5120000:ℝ)+1+
      (((843941/2560000:ℝ)-1-(-5545097887/5000000000:ℝ))/(1-(843941/2560000:ℝ))^2)*(46648281/156250000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_30 : Bounds (Real.log (3379109/10240000:ℝ)) (-1385861943/1250000000:ℝ) (-11086895543/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-819109/2560000:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (3379109/2560000:ℝ)=2*Real.log 2+Real.log (3379109/10240000:ℝ) := by
    rw [show (3379109/2560000:ℝ)=(2:ℝ)^2*(3379109/10240000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_30 {m : ℝ} (hm : m∈Icc (1688997/5120000:ℝ) (3379109/10240000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2988144703/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_30 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (3379109/10240000:ℝ)*(-1385861943/1250000000:ℝ)-(3379109/10240000:ℝ)+1+
      (((1688997/5120000:ℝ)-1-(-11086895543/10000000000:ℝ))/(1-(1688997/5120000:ℝ))^2)*(2988144703/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

private theorem enclosureLog_1_31 : Bounds (Real.log (3301/10000:ℝ)) (-5541798201/5000000000:ℝ) (-11083596401/10000000000:ℝ) := by
  have hh := log_taylor_bounds (x := (-801/2500:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ] at hh
  have he : Real.log (3301/2500:ℝ)=2*Real.log 2+Real.log (3301/10000:ℝ) := by
    rw [show (3301/2500:ℝ)=(2:ℝ)^2*(3301/10000:ℝ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hh
  constructor <;> linarith [hh.1,hh.2,log_two_bounds_22.1,log_two_bounds_22.2]

 theorem enclosureLeaf_1_31 {m : ℝ} (hm : m∈Icc (3379109/10240000:ℝ) (3301/10000:ℝ)) :
    (391/1000:ℝ)<criticalFB1 m := by
  have hh := criticalFB1_interval_lower (q := (2989471609/10000000000:ℝ))
    (by norm_num) (by norm_num) hm enclosureLog_1_31 (by norm_num)
    (by norm_num) criticalTriangle_sharp_bounds.2 (by norm_num)
  have hmargin : (391/1000:ℝ)< (3301/10000:ℝ)*(-5541798201/5000000000:ℝ)-(3301/10000:ℝ)+1+
      (((3379109/10240000:ℝ)-1-(-11083596401/10000000000:ℝ))/(1-(3379109/10240000:ℝ))^2)*(2989471609/10000000000:ℝ)^2 := by norm_num
  exact hmargin.trans_le hh

end SparseLowerTail.Section05.CoverGeometry

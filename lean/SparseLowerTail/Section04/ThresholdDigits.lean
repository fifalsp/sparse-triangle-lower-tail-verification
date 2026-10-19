import SparseLowerTail.Section04.ThresholdDefinitions
import SparseLowerTail.Section04.BalancedPhase

/-! Generated proof certificate for manuscript lem:digits.
Regenerate from the lean directory with python3 tools/generate_threshold_digits.py.
All decimal proposals are validated by the Lean kernel using proved Taylor bounds.
-/
noncomputable section
open SparseLowerTail.Numerics
namespace SparseLowerTail.Section04

-- BEGIN GENERATED CERTIFICATES

theorem digit_log_z_lower : Bounds (-Real.log (125346444093/6250000000000 : ℝ)) (39092552863546061293/10000000000000000000 : ℝ) (390925528635460612933/100000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-27690194093/97656250000 : ℝ)) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (125346444093/97656250000 : ℝ) = 6*Real.log 2 + Real.log (125346444093/6250000000000 : ℝ) := by
    rw [show (125346444093/97656250000 : ℝ) = (2:ℝ)^6 * (125346444093/6250000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_log_t_lower : Bounds (-Real.log (14691005826765694401385489941127272357/976562500000000000000000000000000000000 : ℝ)) (104920082358879038149/25000000000000000000 : ℝ) (419680329435516152599/100000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (567783235734305598614510058872727643/15258789062500000000000000000000000000 : ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (14691005826765694401385489941127272357/15258789062500000000000000000000000000 : ℝ) = 6*Real.log 2 + Real.log (14691005826765694401385489941127272357/976562500000000000000000000000000000000 : ℝ) := by
    rw [show (14691005826765694401385489941127272357/15258789062500000000000000000000000000 : ℝ) = (2:ℝ)^6 * (14691005826765694401385489941127272357/976562500000000000000000000000000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_kappa_lower : Bounds (kappa (125346444093/6250000000000 : ℝ)) (1234299349788993911/5000000000000000000 : ℝ) (24685986995779878223/100000000000000000000 : ℝ) := by
  have hc := kappa_cube (z := (125346444093/6250000000000 : ℝ)) (by norm_num)
  constructor
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num

theorem digit_normalized_lower : 0 < normalizedDifference (125346444093/6250000000000 : ℝ) := by
  have h1 : Bounds ((1 : ℝ)+(125346444093/6250000000000 : ℝ)) (6375346444093/6250000000000 : ℝ) (6375346444093/6250000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add (Bounds.refl (125346444093/6250000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h2 : Bounds (((1 : ℝ)+(125346444093/6250000000000 : ℝ))/(2 : ℝ)) (6375346444093/12500000000000 : ℝ) (6375346444093/12500000000000 : ℝ) := by
    exact (h1.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h3 : Bounds ((1 : ℝ)-(125346444093/6250000000000 : ℝ)) (6124653555907/6250000000000 : ℝ) (6124653555907/6250000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (125346444093/6250000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h4 : Bounds ((1 : ℝ)-(125346444093/6250000000000 : ℝ)) (6124653555907/6250000000000 : ℝ) (6124653555907/6250000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (125346444093/6250000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h5 : Bounds (((1 : ℝ)-(125346444093/6250000000000 : ℝ))*((1 : ℝ)-(125346444093/6250000000000 : ℝ))) (960291358205037045109571/1000000000000000000000000 : ℝ) (240072839551259261277393/250000000000000000000000 : ℝ) := by
    exact (h3.mul_nonneg h4 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h6 : Bounds ((2 : ℝ)*(125346444093/6250000000000 : ℝ)) (125346444093/3125000000000 : ℝ) (125346444093/3125000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg (Bounds.refl (125346444093/6250000000000 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h7 : Bounds (((2 : ℝ)*(125346444093/6250000000000 : ℝ))*(-Real.log (125346444093/6250000000000 : ℝ))) (39200899935704987436747/250000000000000000000000 : ℝ) (4900112491963123429631/31250000000000000000000 : ℝ) := by
    exact (h6.mul_nonneg digit_log_z_lower (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h8 : Bounds ((((2 : ℝ)*(125346444093/6250000000000 : ℝ))*(-Real.log (125346444093/6250000000000 : ℝ)))/(((1 : ℝ)-(125346444093/6250000000000 : ℝ))*((1 : ℝ)-(125346444093/6250000000000 : ℝ)))) (40821881401680790194441/250000000000000000000000 : ℝ) (163287525606723160779019/1000000000000000000000000 : ℝ) := by
    exact (h7.div_pos h5 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h9 : Bounds ((((1 : ℝ)+(125346444093/6250000000000 : ℝ))/(2 : ℝ))-(kappa (125346444093/6250000000000 : ℝ))) (26316784556964121777/100000000000000000000 : ℝ) (1315839227848206089/5000000000000000000 : ℝ) := by
    exact (h2.sub digit_kappa_lower).weaken (by norm_num) (by norm_num)
  have h10 : Bounds ((1 : ℝ)+((((2 : ℝ)*(125346444093/6250000000000 : ℝ))*(-Real.log (125346444093/6250000000000 : ℝ)))/(((1 : ℝ)-(125346444093/6250000000000 : ℝ))*((1 : ℝ)-(125346444093/6250000000000 : ℝ))))) (290821881401680790194441/250000000000000000000000 : ℝ) (1163287525606723160779019/1000000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add h8).weaken (by norm_num) (by norm_num)
  have h11 : Bounds (((((1 : ℝ)+(125346444093/6250000000000 : ℝ))/(2 : ℝ))-(kappa (125346444093/6250000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(125346444093/6250000000000 : ℝ))*(-Real.log (125346444093/6250000000000 : ℝ)))/(((1 : ℝ)-(125346444093/6250000000000 : ℝ))*((1 : ℝ)-(125346444093/6250000000000 : ℝ)))))) (2391717749155938862787/7812500000000000000000 : ℝ) (153069935945980087235983/500000000000000000000000 : ℝ) := by
    exact (h9.mul_nonneg h10 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h12 : Bounds ((125346444093/6250000000000 : ℝ)*(-Real.log (125346444093/6250000000000 : ℝ))) (39200899935704987436747/500000000000000000000000 : ℝ) (4900112491963123429631/62500000000000000000000 : ℝ) := by
    exact ((Bounds.refl (125346444093/6250000000000 : ℝ)).mul_nonneg digit_log_z_lower (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h13 : Bounds (((125346444093/6250000000000 : ℝ)*(-Real.log (125346444093/6250000000000 : ℝ)))/(2 : ℝ)) (39200899935704987436747/1000000000000000000000000 : ℝ) (4900112491963123429631/125000000000000000000000 : ℝ) := by
    exact (h12.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h14 : Bounds ((((((1 : ℝ)+(125346444093/6250000000000 : ℝ))/(2 : ℝ))-(kappa (125346444093/6250000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(125346444093/6250000000000 : ℝ))*(-Real.log (125346444093/6250000000000 : ℝ)))/(((1 : ℝ)-(125346444093/6250000000000 : ℝ))*((1 : ℝ)-(125346444093/6250000000000 : ℝ))))))+(((125346444093/6250000000000 : ℝ)*(-Real.log (125346444093/6250000000000 : ℝ)))/(2 : ℝ))) (345340771827665161873483/1000000000000000000000000 : ℝ) (172670385913832580954507/500000000000000000000000 : ℝ) := by
    exact (h11.add h13).weaken (by norm_num) (by norm_num)
  have h15 : Bounds ((kappa (125346444093/6250000000000 : ℝ))*(-Real.log (14691005826765694401385489941127272357/976562500000000000000000000000000000000 : ℝ))) (1036022315482976698238647/1000000000000000000000000 : ℝ) (518011157741488349185979/500000000000000000000000 : ℝ) := by
    exact (digit_kappa_lower.mul_nonneg digit_log_t_lower (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h16 : Bounds (((kappa (125346444093/6250000000000 : ℝ))*(-Real.log (14691005826765694401385489941127272357/976562500000000000000000000000000000000 : ℝ)))/(3 : ℝ)) (172670385913829449706441/500000000000000000000000 : ℝ) (8633519295691472486433/25000000000000000000000 : ℝ) := by
    exact (h15.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h17 : Bounds (((((((1 : ℝ)+(125346444093/6250000000000 : ℝ))/(2 : ℝ))-(kappa (125346444093/6250000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(125346444093/6250000000000 : ℝ))*(-Real.log (125346444093/6250000000000 : ℝ)))/(((1 : ℝ)-(125346444093/6250000000000 : ℝ))*((1 : ℝ)-(125346444093/6250000000000 : ℝ))))))+(((125346444093/6250000000000 : ℝ)*(-Real.log (125346444093/6250000000000 : ℝ)))/(2 : ℝ)))-(((kappa (125346444093/6250000000000 : ℝ))*(-Real.log (14691005826765694401385489941127272357/976562500000000000000000000000000000000 : ℝ)))/(3 : ℝ))) (6262416163/1000000000000000000000000 : ℝ) (1565624033/250000000000000000000000 : ℝ) := by
    exact (h14.sub h16).weaken (by norm_num) (by norm_num)
  have hv := h17
  have he : normalizedDifference (125346444093/6250000000000 : ℝ) = (((((((1 : ℝ)+(125346444093/6250000000000 : ℝ))/(2 : ℝ))-(kappa (125346444093/6250000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(125346444093/6250000000000 : ℝ))*(-Real.log (125346444093/6250000000000 : ℝ)))/(((1 : ℝ)-(125346444093/6250000000000 : ℝ))*((1 : ℝ)-(125346444093/6250000000000 : ℝ))))))+(((125346444093/6250000000000 : ℝ)*(-Real.log (125346444093/6250000000000 : ℝ)))/(2 : ℝ)))-(((kappa (125346444093/6250000000000 : ℝ))*(-Real.log (14691005826765694401385489941127272357/976562500000000000000000000000000000000 : ℝ)))/(3 : ℝ))) := by
    unfold normalizedDifference
    rw [branchLog_eq_neg_log]
    norm_num
  rw [← he] at hv
  unfold Bounds at hv
  linarith

theorem digit_log_z_upper : Bounds (-Real.log (2005543105489/100000000000000 : ℝ)) (3127404229083286009/800000000000000000 : ℝ) (48865691079426343891/12500000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-443043105489/1562500000000 : ℝ)) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (2005543105489/1562500000000 : ℝ) = 6*Real.log 2 + Real.log (2005543105489/100000000000000 : ℝ) := by
    rw [show (2005543105489/1562500000000 : ℝ) = (2:ℝ)^6 * (2005543105489/100000000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_log_t_upper : Bounds (-Real.log (60174359866462296334684410716227224045169/4000000000000000000000000000000000000000000 : ℝ)) (209840164717733138711/50000000000000000000 : ℝ) (16787213177418651097/4000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (2325640133537703665315589283772775954831/62500000000000000000000000000000000000000 : ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (60174359866462296334684410716227224045169/62500000000000000000000000000000000000000 : ℝ) = 6*Real.log 2 + Real.log (60174359866462296334684410716227224045169/4000000000000000000000000000000000000000000 : ℝ) := by
    rw [show (60174359866462296334684410716227224045169/62500000000000000000000000000000000000000 : ℝ) = (2:ℝ)^6 * (60174359866462296334684410716227224045169/4000000000000000000000000000000000000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_kappa_upper : Bounds (kappa (2005543105489/100000000000000 : ℝ)) (617149674894599557/2500000000000000000 : ℝ) (24685986995783982283/100000000000000000000 : ℝ) := by
  have hc := kappa_cube (z := (2005543105489/100000000000000 : ℝ)) (by norm_num)
  constructor
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num

theorem digit_normalized_upper : normalizedDifference (2005543105489/100000000000000 : ℝ) < 0 := by
  have h18 : Bounds ((1 : ℝ)+(2005543105489/100000000000000 : ℝ)) (102005543105489/100000000000000 : ℝ) (102005543105489/100000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add (Bounds.refl (2005543105489/100000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h19 : Bounds (((1 : ℝ)+(2005543105489/100000000000000 : ℝ))/(2 : ℝ)) (102005543105489/200000000000000 : ℝ) (102005543105489/200000000000000 : ℝ) := by
    exact (h18.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h20 : Bounds ((1 : ℝ)-(2005543105489/100000000000000 : ℝ)) (97994456894511/100000000000000 : ℝ) (97994456894511/100000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (2005543105489/100000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h21 : Bounds ((1 : ℝ)-(2005543105489/100000000000000 : ℝ)) (97994456894511/100000000000000 : ℝ) (97994456894511/100000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (2005543105489/100000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h22 : Bounds (((1 : ℝ)-(2005543105489/100000000000000 : ℝ))*((1 : ℝ)-(2005543105489/100000000000000 : ℝ))) (60018209887813590388637/62500000000000000000000 : ℝ) (960291358205017446218193/1000000000000000000000000 : ℝ) := by
    exact (h20.mul_nonneg h21 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h23 : Bounds ((2 : ℝ)*(2005543105489/100000000000000 : ℝ)) (2005543105489/50000000000000 : ℝ) (2005543105489/50000000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg (Bounds.refl (2005543105489/100000000000000 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h24 : Bounds (((2 : ℝ)*(2005543105489/100000000000000 : ℝ))*(-Real.log (2005543105489/100000000000000 : ℝ))) (78401799871439067426433/500000000000000000000000 : ℝ) (15680359974287813485407/100000000000000000000000 : ℝ) := by
    exact (h23.mul_nonneg digit_log_z_upper (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h25 : Bounds ((((2 : ℝ)*(2005543105489/100000000000000 : ℝ))*(-Real.log (2005543105489/100000000000000 : ℝ)))/(((1 : ℝ)-(2005543105489/100000000000000 : ℝ))*((1 : ℝ)-(2005543105489/100000000000000 : ℝ)))) (653150102427148337843/4000000000000000000000 : ℝ) (32657505121357416892401/200000000000000000000000 : ℝ) := by
    exact (h24.div_pos h22 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h26 : Bounds ((((1 : ℝ)+(2005543105489/100000000000000 : ℝ))/(2 : ℝ))-(kappa (2005543105489/100000000000000 : ℝ))) (26316784556960517717/100000000000000000000 : ℝ) (657919613924012943/2500000000000000000 : ℝ) := by
    exact (h19.sub digit_kappa_upper).weaken (by norm_num) (by norm_num)
  have h27 : Bounds ((1 : ℝ)+((((2 : ℝ)*(2005543105489/100000000000000 : ℝ))*(-Real.log (2005543105489/100000000000000 : ℝ)))/(((1 : ℝ)-(2005543105489/100000000000000 : ℝ))*((1 : ℝ)-(2005543105489/100000000000000 : ℝ))))) (4653150102427148337843/4000000000000000000000 : ℝ) (232657505121357416892401/200000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add h25).weaken (by norm_num) (by norm_num)
  have h28 : Bounds (((((1 : ℝ)+(2005543105489/100000000000000 : ℝ))/(2 : ℝ))-(kappa (2005543105489/100000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(2005543105489/100000000000000 : ℝ))*(-Real.log (2005543105489/100000000000000 : ℝ)))/(((1 : ℝ)-(2005543105489/100000000000000 : ℝ))*((1 : ℝ)-(2005543105489/100000000000000 : ℝ)))))) (306139871891935071514273/1000000000000000000000000 : ℝ) (306139871891935071549503/1000000000000000000000000 : ℝ) := by
    exact (h26.mul_nonneg h27 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h29 : Bounds ((2005543105489/100000000000000 : ℝ)*(-Real.log (2005543105489/100000000000000 : ℝ))) (78401799871439067426433/1000000000000000000000000 : ℝ) (15680359974287813485407/200000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (2005543105489/100000000000000 : ℝ)).mul_nonneg digit_log_z_upper (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h30 : Bounds (((2005543105489/100000000000000 : ℝ)*(-Real.log (2005543105489/100000000000000 : ℝ)))/(2 : ℝ)) (612514061495617714269/15625000000000000000000 : ℝ) (19600449967859766856759/500000000000000000000000 : ℝ) := by
    exact (h29.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h31 : Bounds ((((((1 : ℝ)+(2005543105489/100000000000000 : ℝ))/(2 : ℝ))-(kappa (2005543105489/100000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(2005543105489/100000000000000 : ℝ))*(-Real.log (2005543105489/100000000000000 : ℝ)))/(((1 : ℝ)-(2005543105489/100000000000000 : ℝ))*((1 : ℝ)-(2005543105489/100000000000000 : ℝ))))))+(((2005543105489/100000000000000 : ℝ)*(-Real.log (2005543105489/100000000000000 : ℝ)))/(2 : ℝ))) (345340771827654605227489/1000000000000000000000000 : ℝ) (345340771827654605263021/1000000000000000000000000 : ℝ) := by
    exact (h28.add h30).weaken (by norm_num) (by norm_num)
  have h32 : Bounds ((kappa (2005543105489/100000000000000 : ℝ))*(-Real.log (60174359866462296334684410716227224045169/4000000000000000000000000000000000000000000 : ℝ))) (259005578870756453943563/250000000000000000000000 : ℝ) (1036022315483025815907563/1000000000000000000000000 : ℝ) := by
    exact (digit_kappa_upper.mul_nonneg digit_log_t_upper (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h33 : Bounds (((kappa (2005543105489/100000000000000 : ℝ))*(-Real.log (60174359866462296334684410716227224045169/4000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ)) (1381363087310701087699/4000000000000000000000 : ℝ) (86335192956918817992297/250000000000000000000000 : ℝ) := by
    exact (h32.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h34 : Bounds (((((((1 : ℝ)+(2005543105489/100000000000000 : ℝ))/(2 : ℝ))-(kappa (2005543105489/100000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(2005543105489/100000000000000 : ℝ))*(-Real.log (2005543105489/100000000000000 : ℝ)))/(((1 : ℝ)-(2005543105489/100000000000000 : ℝ))*((1 : ℝ)-(2005543105489/100000000000000 : ℝ))))))+(((2005543105489/100000000000000 : ℝ)*(-Real.log (2005543105489/100000000000000 : ℝ)))/(2 : ℝ)))-(((kappa (2005543105489/100000000000000 : ℝ))*(-Real.log (60174359866462296334684410716227224045169/4000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ))) (-20666741699/1000000000000000000000000 : ℝ) (-20666661729/1000000000000000000000000 : ℝ) := by
    exact (h31.sub h33).weaken (by norm_num) (by norm_num)
  have hv := h34
  have he : normalizedDifference (2005543105489/100000000000000 : ℝ) = (((((((1 : ℝ)+(2005543105489/100000000000000 : ℝ))/(2 : ℝ))-(kappa (2005543105489/100000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(2005543105489/100000000000000 : ℝ))*(-Real.log (2005543105489/100000000000000 : ℝ)))/(((1 : ℝ)-(2005543105489/100000000000000 : ℝ))*((1 : ℝ)-(2005543105489/100000000000000 : ℝ))))))+(((2005543105489/100000000000000 : ℝ)*(-Real.log (2005543105489/100000000000000 : ℝ)))/(2 : ℝ)))-(((kappa (2005543105489/100000000000000 : ℝ))*(-Real.log (60174359866462296334684410716227224045169/4000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ))) := by
    unfold normalizedDifference
    rw [branchLog_eq_neg_log]
    norm_num
  rw [← he] at hv
  unfold Bounds at hv
  linarith

theorem digit_D_lower : 0 < branchDifference digitZLower := by
  rw [branchDifference_normalized (by norm_num [digitZLower])]
  apply mul_pos (branchB_pos _)
  convert digit_normalized_lower using 1
  norm_num [digitZLower]

theorem digit_D_upper : branchDifference digitZUpper < 0 := by
  rw [branchDifference_normalized (by norm_num [digitZUpper])]
  apply mul_neg_of_pos_of_neg (branchB_pos _)
  convert digit_normalized_upper using 1
  norm_num [digitZUpper]


/-- The crossing lies strictly inside the printed decimal bracket. -/
theorem transitionParameter_digits : digitZLower < transitionParameter ∧ transitionParameter < digitZUpper := by
  constructor
  · rcases lt_trichotomy digitZLower transitionParameter with hl | he | hr
    · exact hl
    · have h := digit_D_lower
      rw [he, branchDifference_transition] at h
      linarith
    · have h := branchDifference_neg_after_transition ⟨hr, by norm_num [digitZLower]⟩
      linarith [digit_D_lower]
  · rcases lt_trichotomy transitionParameter digitZUpper with hl | he | hr
    · exact hl
    · have h := digit_D_upper
      rw [← he, branchDifference_transition] at h
      linarith
    · have h := branchDifference_pos_before_transition ⟨by norm_num [digitZUpper], hr⟩
      linarith [digit_D_upper]

theorem digit_log_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (branchLog z) (3127404229083286009/800000000000000000 : ℝ) (390925528635460612933/100000000000000000000 : ℝ) := by
  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num [digitZLower]) hz.1
  have hl := Real.log_le_log (show 0 < digitZLower by norm_num [digitZLower]) hz.1
  have hu := Real.log_le_log hz0 hz.2
  have hll := digit_log_z_upper.1
  have hlu := digit_log_z_lower.2
  norm_num [digitZLower, digitZUpper] at hl hu
  rw [branchLog_eq_neg_log]
  constructor <;> linarith

theorem digit_kappa_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (kappa z) (1234299349788993911/5000000000000000000 : ℝ) (24685986995783982283/100000000000000000000 : ℝ) := by
  have hz0 : 0 ≤ z := le_trans (by norm_num [digitZLower]) hz.1
  have hpowlo := pow_le_pow_left₀ (show 0 ≤ digitZLower by norm_num [digitZLower]) hz.1 3
  have hpowhi := pow_le_pow_left₀ hz0 hz.2 3
  have hlo : kappa digitZLower ≤ kappa z := by
    apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [kappa_cube (by norm_num [digitZLower]), kappa_cube hz0]
    nlinarith [hz.1]
  have hhi : kappa z ≤ kappa digitZUpper := by
    apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [kappa_cube hz0, kappa_cube (by norm_num [digitZUpper])]
    nlinarith [hz.2]
  have hkl := digit_kappa_lower.1
  have hku := digit_kappa_upper.2
  norm_num [digitZLower, digitZUpper] at hlo hhi
  constructor <;> linarith

theorem digit_exponent_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (2*z*branchLog z/(1-z)^2) (163287525606702333765547/1000000000000000000000000 : ℝ) (81643762803403955737111/500000000000000000000000 : ℝ) := by
  have hZ : Bounds z (125346444093/6250000000000 : ℝ) (2005543105489/100000000000000 : ℝ) := by
    unfold Bounds
    norm_num [digitZLower, digitZUpper] at hz
    exact hz
  have hL := digit_log_range hz
  have h35 : Bounds ((1 : ℝ)-z) (97994456894511/100000000000000 : ℝ) (6124653555907/6250000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h36 : Bounds ((1 : ℝ)-z) (97994456894511/100000000000000 : ℝ) (6124653555907/6250000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h37 : Bounds (((1 : ℝ)-z)*((1 : ℝ)-z)) (60018209887813590388637/62500000000000000000000 : ℝ) (240072839551259261277393/250000000000000000000000 : ℝ) := by
    exact (h35.mul_nonneg h36 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h38 : Bounds ((2 : ℝ)*z) (125346444093/3125000000000 : ℝ) (2005543105489/50000000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg hZ (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h39 : Bounds (((2 : ℝ)*z)*(branchLog z)) (156803599742799949747139/1000000000000000000000000 : ℝ) (156803599742898134853919/1000000000000000000000000 : ℝ) := by
    exact (h38.mul_nonneg hL (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h40 : Bounds ((((2 : ℝ)*z)*(branchLog z))/(((1 : ℝ)-z)*((1 : ℝ)-z))) (163287525606702333765547/1000000000000000000000000 : ℝ) (81643762803403955737111/500000000000000000000000 : ℝ) := by
    exact (h39.div_pos h37 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  convert h40 using 1
  ring

theorem digit_exp_lower : Bounds (Real.exp (-81643762803403955737111/500000000000000000000000 : ℝ)) (21233673607687572771/25000000000000000000 : ℝ) (84934694430750291087/100000000000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-81643762803403955737111/500000000000000000000000 : ℝ)) (by norm_num) (n := 20) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem digit_exp_upper : Bounds (Real.exp (-163287525606702333765547/1000000000000000000000000 : ℝ)) (16986938886151851659/20000000000000000000 : ℝ) (42467347215379629149/50000000000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-163287525606702333765547/1000000000000000000000000 : ℝ)) (by norm_num) (n := 20) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem digit_branchB_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (branchB z) (21233673607687572771/25000000000000000000 : ℝ) (42467347215379629149/50000000000000000000 : ℝ) := by
  have hE := digit_exponent_range hz
  have hlo := Real.exp_le_exp.mpr (neg_le_neg hE.2)
  have hhi := Real.exp_le_exp.mpr (neg_le_neg hE.1)
  have he : branchB z = Real.exp (-(2*z*branchLog z/(1-z)^2)) := by unfold branchB; congr 1; ring
  rw [← he] at hlo hhi
  have hbl := digit_exp_lower.1
  have hbu := digit_exp_upper.2
  constructor <;> linarith


/-- The four parameter enclosures over the entire printed z bracket. -/
theorem digit_branch_ranges {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) :
    Bounds (branchA z) (1703401908/10^11) (1703401909/10^11) ∧
    Bounds (branchB z) (8493469443/10^10) (8493469444/10^10) ∧
    Bounds (branchMu z) (1128627816/10^8) (1128627817/10^8) ∧
    Bounds (branchRho z) (2096696762/10^10) (2096696763/10^10) := by

  have hZ : Bounds z (125346444093/6250000000000 : ℝ) (2005543105489/100000000000000 : ℝ) := by
    unfold Bounds
    norm_num [digitZLower, digitZUpper] at hz
    exact hz
  have hL := digit_log_range hz
  have hK := digit_kappa_range hz
  have hB := digit_branchB_range hz
  have h41 : Bounds (z*(branchB z)) (8517009541616063857123/500000000000000000000000 : ℝ) (17034019083242419597111/1000000000000000000000000 : ℝ) := by
    exact (hZ.mul_nonneg hB (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h42 : Bounds ((branchB z)*(branchB z)) (360695115902246225640337/500000000000000000000000 : ℝ) (721390231804644776796873/1000000000000000000000000 : ℝ) := by
    exact (hB.mul_nonneg hB (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h43 : Bounds ((1 : ℝ)-z) (97994456894511/100000000000000 : ℝ) (6124653555907/6250000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h44 : Bounds ((1 : ℝ)-z) (97994456894511/100000000000000 : ℝ) (6124653555907/6250000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h45 : Bounds (((1 : ℝ)-z)*((1 : ℝ)-z)) (60018209887813590388637/62500000000000000000000 : ℝ) (240072839551259261277393/250000000000000000000000 : ℝ) := by
    exact (h43.mul_nonneg h44 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h46 : Bounds ((2 : ℝ)*(branchLog z)) (3127404229083286009/400000000000000000 : ℝ) (390925528635460612933/50000000000000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg hL (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h47 : Bounds ((((1 : ℝ)-z)*((1 : ℝ)-z))*((branchB z)*(branchB z))) (692744805495368429592373/1000000000000000000000000 : ℝ) (69274480549552884491801/100000000000000000000000 : ℝ) := by
    exact (h45.mul_nonneg h42 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h48 : Bounds (((2 : ℝ)*(branchLog z))/((((1 : ℝ)-z)*((1 : ℝ)-z))*((branchB z)*(branchB z)))) (11286278165760533764807267/1000000000000000000000000 : ℝ) (5643139082882293406547097/500000000000000000000000 : ℝ) := by
    exact (h46.div_pos h47 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h49 : Bounds ((kappa z)*(branchB z)) (104834838110401966605049/500000000000000000000000 : ℝ) (209669676220860927396601/1000000000000000000000000 : ℝ) := by
    exact (hK.mul_nonneg hB (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h41.weaken (by norm_num) (by norm_num)
  · exact hB.weaken (by norm_num) (by norm_num)
  · have hm := h48.weaken (show (141078477/12500000 : ℝ) ≤ (11286278165760533764807267/1000000000000000000000000 : ℝ) by norm_num) (show (5643139082882293406547097/500000000000000000000000 : ℝ) ≤ (1128627817/100000000 : ℝ) by norm_num)
    convert hm using 1 <;> norm_num [branchMu, pow_two]
  · exact h49.weaken (by norm_num) (by norm_num)


/-- Lemma lem:digits for the exact mathematically defined crossing parameters. -/
theorem transition_digits :
    Bounds (branchA transitionParameter) (1703401908/10^11) (1703401909/10^11) ∧
    Bounds (branchB transitionParameter) (8493469443/10^10) (8493469444/10^10) ∧
    Bounds (branchMu transitionParameter) (1128627816/10^8) (1128627817/10^8) ∧
    Bounds transitionTarget (2096696762/10^10) (2096696763/10^10) := by
  have h := digit_branch_ranges ⟨le_of_lt transitionParameter_digits.1, le_of_lt transitionParameter_digits.2⟩
  rwa [branchRho_transitionParameter] at h

/-- The variationally defined threshold satisfies the printed enclosure. -/
theorem threshold_digits :
    Bounds threshold (2096696762/10^10) (2096696763/10^10) := by
  rw [threshold_eq_transitionTarget]
  exact transition_digits.2.2.2

end SparseLowerTail.Section04

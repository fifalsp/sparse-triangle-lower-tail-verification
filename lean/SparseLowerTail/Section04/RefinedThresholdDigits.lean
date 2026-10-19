import SparseLowerTail.Section04.ThresholdDefinitions
import SparseLowerTail.Section04.BalancedPhase

/-! Generated proof certificate for manuscript lem:digits.
Regenerate from the lean directory with python3 tools/generate_refined_threshold_digits.py.
All decimal proposals are validated by the Lean kernel using proved Taylor bounds.
-/
noncomputable section
open SparseLowerTail.Numerics
namespace SparseLowerTail.Section04.Refined

def digitZLower : ℝ := 5013857763720581/250000000000000000
def digitZUpper : ℝ := 20055431054882327/1000000000000000000

theorem digit_log_z_lower : Bounds (-Real.log (5013857763720581/250000000000000000 : ℝ)) (1954627643177245125241/500000000000000000000 : ℝ) (781851057270898050097/200000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1107607763720581/3906250000000000 : ℝ)) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (5013857763720581/3906250000000000 : ℝ) = 6*Real.log 2 + Real.log (5013857763720581/250000000000000000 : ℝ) := by
    rw [show (5013857763720581/3906250000000000 : ℝ) = (2:ℝ)^6 * (5013857763720581/250000000000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_log_t_lower : Bounds (-Real.log (940224372913113423005546899440324503349268656882941/62500000000000000000000000000000000000000000000000000 : ℝ)) (4196803294355045616067/1000000000000000000000 : ℝ) (419680329435504561607/100000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (36338127086886576994453100559675496650731343117059/976562500000000000000000000000000000000000000000000 : ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (940224372913113423005546899440324503349268656882941/976562500000000000000000000000000000000000000000000 : ℝ) = 6*Real.log 2 + Real.log (940224372913113423005546899440324503349268656882941/62500000000000000000000000000000000000000000000000000 : ℝ) := by
    rw [show (940224372913113423005546899440324503349268656882941/976562500000000000000000000000000000000000000000000 : ℝ) = (2:ℝ)^6 * (940224372913113423005546899440324503349268656882941/62500000000000000000000000000000000000000000000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_kappa_lower : Bounds (kappa (5013857763720581/250000000000000000 : ℝ)) (4937197399156166401/20000000000000000000 : ℝ) (246859869957808320053/1000000000000000000000 : ℝ) := by
  have hc := kappa_cube (z := (5013857763720581/250000000000000000 : ℝ)) (by norm_num)
  constructor
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num

theorem digit_normalized_lower : 0 < normalizedDifference (5013857763720581/250000000000000000 : ℝ) := by
  have h1 : Bounds ((1 : ℝ)+(5013857763720581/250000000000000000 : ℝ)) (255013857763720581/250000000000000000 : ℝ) (255013857763720581/250000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add (Bounds.refl (5013857763720581/250000000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h2 : Bounds (((1 : ℝ)+(5013857763720581/250000000000000000 : ℝ))/(2 : ℝ)) (255013857763720581/500000000000000000 : ℝ) (255013857763720581/500000000000000000 : ℝ) := by
    exact (h1.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h3 : Bounds ((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ)) (244986142236279419/250000000000000000 : ℝ) (244986142236279419/250000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (5013857763720581/250000000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h4 : Bounds ((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ)) (244986142236279419/250000000000000000 : ℝ) (244986142236279419/250000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (5013857763720581/250000000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h5 : Bounds (((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))*((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))) (192058271641006498065443/200000000000000000000000 : ℝ) (60018209887814530645451/62500000000000000000000 : ℝ) := by
    exact (h3.mul_nonneg h4 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h6 : Bounds ((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ)) (5013857763720581/125000000000000000 : ℝ) (5013857763720581/125000000000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg (Bounds.refl (5013857763720581/250000000000000000 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h7 : Bounds (((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ))*(-Real.log (5013857763720581/250000000000000000 : ℝ))) (39200899935708367991567/250000000000000000000000 : ℝ) (15680359974283347196639/100000000000000000000000 : ℝ) := by
    exact (h6.mul_nonneg digit_log_z_lower (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h8 : Bounds ((((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ))*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))*((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ)))) (20410940700842252080299/125000000000000000000000 : ℝ) (4082188140168450416063/25000000000000000000000 : ℝ) := by
    exact (h7.div_pos h5 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h9 : Bounds ((((1 : ℝ)+(5013857763720581/250000000000000000 : ℝ))/(2 : ℝ))-(kappa (5013857763720581/250000000000000000 : ℝ))) (263167845569632841947/1000000000000000000000 : ℝ) (5263356911392656839/20000000000000000000 : ℝ) := by
    exact (h2.sub digit_kappa_lower).weaken (by norm_num) (by norm_num)
  have h10 : Bounds ((1 : ℝ)+((((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ))*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))*((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))))) (145410940700842252080299/125000000000000000000000 : ℝ) (29082188140168450416063/25000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add h8).weaken (by norm_num) (by norm_num)
  have h11 : Bounds (((((1 : ℝ)+(5013857763720581/250000000000000000 : ℝ))/(2 : ℝ))-(kappa (5013857763720581/250000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ))*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))*((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ)))))) (76534967972988585133053/250000000000000000000000 : ℝ) (38267483986494292566967/125000000000000000000000 : ℝ) := by
    exact (h9.mul_nonneg h10 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h12 : Bounds ((5013857763720581/250000000000000000 : ℝ)*(-Real.log (5013857763720581/250000000000000000 : ℝ))) (39200899935708367991567/500000000000000000000000 : ℝ) (15680359974283347196639/200000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (5013857763720581/250000000000000000 : ℝ)).mul_nonneg digit_log_z_lower (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h13 : Bounds (((5013857763720581/250000000000000000 : ℝ)*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(2 : ℝ)) (39200899935708367991567/1000000000000000000000000 : ℝ) (19600449967854183995799/500000000000000000000000 : ℝ) := by
    exact (h12.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h14 : Bounds ((((((1 : ℝ)+(5013857763720581/250000000000000000 : ℝ))/(2 : ℝ))-(kappa (5013857763720581/250000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ))*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))*((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))))))+(((5013857763720581/250000000000000000 : ℝ)*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(2 : ℝ))) (345340771827662708523779/1000000000000000000000000 : ℝ) (172670385913831354263667/500000000000000000000000 : ℝ) := by
    exact (h11.add h13).weaken (by norm_num) (by norm_num)
  have h15 : Bounds ((kappa (5013857763720581/250000000000000000 : ℝ))*(-Real.log (940224372913113423005546899440324503349268656882941/62500000000000000000000000000000000000000000000000000 : ℝ))) (207204463096597622643567/200000000000000000000000 : ℝ) (1036022315482988113231167/1000000000000000000000000 : ℝ) := by
    exact (digit_kappa_lower.mul_nonneg digit_log_t_lower (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h16 : Bounds (((kappa (5013857763720581/250000000000000000 : ℝ))*(-Real.log (940224372913113423005546899440324503349268656882941/62500000000000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ)) (69068154365532540881189/200000000000000000000000 : ℝ) (345340771827662704410389/1000000000000000000000000 : ℝ) := by
    exact (h15.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h17 : Bounds (((((((1 : ℝ)+(5013857763720581/250000000000000000 : ℝ))/(2 : ℝ))-(kappa (5013857763720581/250000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ))*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))*((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))))))+(((5013857763720581/250000000000000000 : ℝ)*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(2 : ℝ)))-(((kappa (5013857763720581/250000000000000000 : ℝ))*(-Real.log (940224372913113423005546899440324503349268656882941/62500000000000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ))) (411339/100000000000000000000000 : ℝ) (4121389/1000000000000000000000000 : ℝ) := by
    exact (h14.sub h16).weaken (by norm_num) (by norm_num)
  have hv := h17
  have he : normalizedDifference (5013857763720581/250000000000000000 : ℝ) = (((((((1 : ℝ)+(5013857763720581/250000000000000000 : ℝ))/(2 : ℝ))-(kappa (5013857763720581/250000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(5013857763720581/250000000000000000 : ℝ))*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))*((1 : ℝ)-(5013857763720581/250000000000000000 : ℝ))))))+(((5013857763720581/250000000000000000 : ℝ)*(-Real.log (5013857763720581/250000000000000000 : ℝ)))/(2 : ℝ)))-(((kappa (5013857763720581/250000000000000000 : ℝ))*(-Real.log (940224372913113423005546899440324503349268656882941/62500000000000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ))) := by
    unfold normalizedDifference
    rw [branchLog_eq_neg_log]
    norm_num
  rw [← he] at hv
  unfold Bounds at hv
  linarith

theorem digit_log_z_upper : Bounds (-Real.log (20055431054882327/1000000000000000000 : ℝ)) (3909255286354490100897/1000000000000000000000 : ℝ) (39092552863544901009/10000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-4430431054882327/15625000000000000 : ℝ)) (by norm_num) 40
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (20055431054882327/15625000000000000 : ℝ) = 6*Real.log 2 + Real.log (20055431054882327/1000000000000000000 : ℝ) := by
    rw [show (20055431054882327/15625000000000000 : ℝ) = (2:ℝ)^6 * (20055431054882327/1000000000000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_log_t_upper : Bounds (-Real.log (60174359866439268075974984397355013700788049911099783/4000000000000000000000000000000000000000000000000000000 : ℝ)) (4196803294355045466441/1000000000000000000000 : ℝ) (1049200823588761366611/250000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (2325640133560731924025015602644986299211950088900217/62500000000000000000000000000000000000000000000000000 : ℝ)) (by norm_num) 18
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (60174359866439268075974984397355013700788049911099783/62500000000000000000000000000000000000000000000000000 : ℝ) = 6*Real.log 2 + Real.log (60174359866439268075974984397355013700788049911099783/4000000000000000000000000000000000000000000000000000000 : ℝ) := by
    rw [show (60174359866439268075974984397355013700788049911099783/62500000000000000000000000000000000000000000000000000 : ℝ) = (2:ℝ)^6 * (60174359866439268075974984397355013700788049911099783/4000000000000000000000000000000000000000000000000000000 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem digit_kappa_upper : Bounds (kappa (20055431054882327/1000000000000000000 : ℝ)) (123429934978904166181/500000000000000000000 : ℝ) (49371973991561666473/200000000000000000000 : ℝ) := by
  have hc := kappa_cube (z := (20055431054882327/1000000000000000000 : ℝ)) (by norm_num)
  constructor
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num
  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hc]
    norm_num

theorem digit_normalized_upper : normalizedDifference (20055431054882327/1000000000000000000 : ℝ) < 0 := by
  have h18 : Bounds ((1 : ℝ)+(20055431054882327/1000000000000000000 : ℝ)) (1020055431054882327/1000000000000000000 : ℝ) (1020055431054882327/1000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add (Bounds.refl (20055431054882327/1000000000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h19 : Bounds (((1 : ℝ)+(20055431054882327/1000000000000000000 : ℝ))/(2 : ℝ)) (1020055431054882327/2000000000000000000 : ℝ) (1020055431054882327/2000000000000000000 : ℝ) := by
    exact (h18.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h20 : Bounds ((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ)) (979944568945117673/1000000000000000000 : ℝ) (979944568945117673/1000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (20055431054882327/1000000000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h21 : Bounds ((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ)) (979944568945117673/1000000000000000000 : ℝ) (979944568945117673/1000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (20055431054882327/1000000000000000000 : ℝ))).weaken (by norm_num) (by norm_num)
  have h22 : Bounds (((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))*((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))) (960291358205032484447547/1000000000000000000000000 : ℝ) (240072839551258121111887/250000000000000000000000 : ℝ) := by
    exact (h20.mul_nonneg h21 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h23 : Bounds ((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ)) (20055431054882327/500000000000000000 : ℝ) (20055431054882327/500000000000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg (Bounds.refl (20055431054882327/1000000000000000000 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h24 : Bounds (((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ))*(-Real.log (20055431054882327/1000000000000000000 : ℝ))) (156803599742833489421817/1000000000000000000000000 : ℝ) (78401799871416744710969/500000000000000000000000 : ℝ) := by
    exact (h23.mul_nonneg digit_log_z_upper (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h25 : Bounds ((((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ))*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))*((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ)))) (32657505121347607163903/200000000000000000000000 : ℝ) (81643762803369017909821/500000000000000000000000 : ℝ) := by
    exact (h24.div_pos h22 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h26 : Bounds ((((1 : ℝ)+(20055431054882327/1000000000000000000 : ℝ))/(2 : ℝ))-(kappa (20055431054882327/1000000000000000000 : ℝ))) (52633569113926566227/200000000000000000000 : ℝ) (131583922784816415569/500000000000000000000 : ℝ) := by
    exact (h19.sub digit_kappa_upper).weaken (by norm_num) (by norm_num)
  have h27 : Bounds ((1 : ℝ)+((((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ))*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))*((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))))) (232657505121347607163903/200000000000000000000000 : ℝ) (581643762803369017909821/500000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add h25).weaken (by norm_num) (by norm_num)
  have h28 : Bounds (((((1 : ℝ)+(20055431054882327/1000000000000000000 : ℝ))/(2 : ℝ))-(kappa (20055431054882327/1000000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ))*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))*((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ)))))) (306139871891954333001549/1000000000000000000000000 : ℝ) (306139871891954333005073/1000000000000000000000000 : ℝ) := by
    exact (h26.mul_nonneg h27 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h29 : Bounds ((20055431054882327/1000000000000000000 : ℝ)*(-Real.log (20055431054882327/1000000000000000000 : ℝ))) (19600449967854186177727/250000000000000000000000 : ℝ) (78401799871416744710969/1000000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (20055431054882327/1000000000000000000 : ℝ)).mul_nonneg digit_log_z_upper (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h30 : Bounds (((20055431054882327/1000000000000000000 : ℝ)*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(2 : ℝ)) (19600449967854186177727/500000000000000000000000 : ℝ) (7840179987141674471097/200000000000000000000000 : ℝ) := by
    exact (h29.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h31 : Bounds ((((((1 : ℝ)+(20055431054882327/1000000000000000000 : ℝ))/(2 : ℝ))-(kappa (20055431054882327/1000000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ))*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))*((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))))))+(((20055431054882327/1000000000000000000 : ℝ)*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(2 : ℝ))) (345340771827662705357003/1000000000000000000000000 : ℝ) (172670385913831352680279/500000000000000000000000 : ℝ) := by
    exact (h28.add h30).weaken (by norm_num) (by norm_num)
  have h32 : Bounds ((kappa (20055431054882327/1000000000000000000 : ℝ))*(-Real.log (60174359866439268075974984397355013700788049911099783/4000000000000000000000000000000000000000000000000000000 : ℝ))) (1036022315482988127952223/1000000000000000000000000 : ℝ) (207204463096597625593111/200000000000000000000000 : ℝ) := by
    exact (digit_kappa_upper.mul_nonneg digit_log_t_upper (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h33 : Bounds (((kappa (20055431054882327/1000000000000000000 : ℝ))*(-Real.log (60174359866439268075974984397355013700788049911099783/4000000000000000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ)) (345340771827662709317407/1000000000000000000000000 : ℝ) (86335192956915677330463/250000000000000000000000 : ℝ) := by
    exact (h32.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h34 : Bounds (((((((1 : ℝ)+(20055431054882327/1000000000000000000 : ℝ))/(2 : ℝ))-(kappa (20055431054882327/1000000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ))*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))*((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))))))+(((20055431054882327/1000000000000000000 : ℝ)*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(2 : ℝ)))-(((kappa (20055431054882327/1000000000000000000 : ℝ))*(-Real.log (60174359866439268075974984397355013700788049911099783/4000000000000000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ))) (-3964849/1000000000000000000000000 : ℝ) (-3956849/1000000000000000000000000 : ℝ) := by
    exact (h31.sub h33).weaken (by norm_num) (by norm_num)
  have hv := h34
  have he : normalizedDifference (20055431054882327/1000000000000000000 : ℝ) = (((((((1 : ℝ)+(20055431054882327/1000000000000000000 : ℝ))/(2 : ℝ))-(kappa (20055431054882327/1000000000000000000 : ℝ)))*((1 : ℝ)+((((2 : ℝ)*(20055431054882327/1000000000000000000 : ℝ))*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))*((1 : ℝ)-(20055431054882327/1000000000000000000 : ℝ))))))+(((20055431054882327/1000000000000000000 : ℝ)*(-Real.log (20055431054882327/1000000000000000000 : ℝ)))/(2 : ℝ)))-(((kappa (20055431054882327/1000000000000000000 : ℝ))*(-Real.log (60174359866439268075974984397355013700788049911099783/4000000000000000000000000000000000000000000000000000000 : ℝ)))/(3 : ℝ))) := by
    unfold normalizedDifference
    rw [branchLog_eq_neg_log]
    norm_num
  rw [← he] at hv
  unfold Bounds at hv
  linarith

theorem digit_D_lower : 0 < branchDifference digitZLower := by
  rw [branchDifference_normalized (by norm_num [digitZLower])]
  apply mul_pos (branchB_pos _)
  convert digit_normalized_lower using 1 <;> norm_num [digitZLower]

theorem digit_D_upper : branchDifference digitZUpper < 0 := by
  rw [branchDifference_normalized (by norm_num [digitZUpper])]
  apply mul_neg_of_pos_of_neg (branchB_pos _)
  convert digit_normalized_upper using 1 <;> norm_num [digitZUpper]


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

theorem digit_log_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (branchLog z) (3909255286354490100897/1000000000000000000000 : ℝ) (781851057270898050097/200000000000000000000 : ℝ) := by
  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num [digitZLower]) hz.1
  have hl := Real.log_le_log (show 0 < digitZLower by norm_num [digitZLower]) hz.1
  have hu := Real.log_le_log hz0 hz.2
  have hll := digit_log_z_upper.1
  have hlu := digit_log_z_lower.2
  norm_num [digitZLower, digitZUpper] at hl hu
  rw [branchLog_eq_neg_log]
  constructor <;> linarith

theorem digit_kappa_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (kappa z) (4937197399156166401/20000000000000000000 : ℝ) (49371973991561666473/200000000000000000000 : ℝ) := by
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

theorem digit_exponent_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (2*z*branchLog z/(1-z)^2) (81643762803369005197153/500000000000000000000000 : ℝ) (10205470350421127629233/62500000000000000000000 : ℝ) := by
  have hZ : Bounds z (5013857763720581/250000000000000000 : ℝ) (20055431054882327/1000000000000000000 : ℝ) := by
    unfold Bounds
    norm_num [digitZLower, digitZUpper] at hz
    exact hz
  have hL := digit_log_range hz
  have h35 : Bounds ((1 : ℝ)-z) (979944568945117673/1000000000000000000 : ℝ) (244986142236279419/250000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h36 : Bounds ((1 : ℝ)-z) (979944568945117673/1000000000000000000 : ℝ) (244986142236279419/250000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h37 : Bounds (((1 : ℝ)-z)*((1 : ℝ)-z)) (960291358205032484447547/1000000000000000000000000 : ℝ) (60018209887814530645451/62500000000000000000000 : ℝ) := by
    exact (h35.mul_nonneg h36 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h38 : Bounds ((2 : ℝ)*z) (5013857763720581/125000000000000000 : ℝ) (20055431054882327/500000000000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg hZ (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h39 : Bounds (((2 : ℝ)*z)*(branchLog z)) (31360719948566693193257/200000000000000000000000 : ℝ) (156803599742833495421921/1000000000000000000000000 : ℝ) := by
    exact (h38.mul_nonneg hL (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h40 : Bounds ((((2 : ℝ)*z)*(branchLog z))/(((1 : ℝ)-z)*((1 : ℝ)-z))) (81643762803369005197153/500000000000000000000000 : ℝ) (10205470350421127629233/62500000000000000000000 : ℝ) := by
    exact (h39.div_pos h37 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  convert h40 using 1
  ring

theorem digit_exp_lower : Bounds (Real.exp (-10205470350421127629233/62500000000000000000000 : ℝ)) (849346944307562254223/1000000000000000000000 : ℝ) (424673472153781127113/500000000000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-10205470350421127629233/62500000000000000000000 : ℝ)) (by norm_num) (n := 20) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem digit_exp_upper : Bounds (Real.exp (-81643762803369005197153/500000000000000000000000 : ℝ)) (6794775554460498249/8000000000000000000 : ℝ) (106168368038445285141/125000000000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-81643762803369005197153/500000000000000000000000 : ℝ)) (by norm_num) (n := 20) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem digit_branchB_range {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (branchB z) (849346944307562254223/1000000000000000000000 : ℝ) (106168368038445285141/125000000000000000000 : ℝ) := by
  have hE := digit_exponent_range hz
  have hlo := Real.exp_le_exp.mpr (neg_le_neg hE.2)
  have hhi := Real.exp_le_exp.mpr (neg_le_neg hE.1)
  have he : branchB z = Real.exp (-(2*z*branchLog z/(1-z)^2)) := by unfold branchB; congr 1; ring
  rw [← he] at hlo hhi
  have hbl := digit_exp_lower.1
  have hbu := digit_exp_upper.2
  constructor <;> linarith

theorem tight_branch_ranges {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) :
    Bounds (branchA z) (17034019083235291753671/1000000000000000000000000 : ℝ) (2129252385404411855163/125000000000000000000000 : ℝ) ∧
    Bounds (branchB z) (849346944307562254223/1000000000000000000000 : ℝ) (106168368038445285141/125000000000000000000 : ℝ) ∧
    Bounds (branchMu z) (282156954144062429294093/25000000000000000000000 : ℝ) (5643139082881249193887473/500000000000000000000000 : ℝ) := by
  have hZ : Bounds z (5013857763720581/250000000000000000 : ℝ) (20055431054882327/1000000000000000000 : ℝ) := by
    unfold Bounds
    norm_num [digitZLower,digitZUpper] at hz
    exact hz
  have hL := digit_log_range hz
  have hB := digit_branchB_range hz
  have h41 : Bounds (z*(branchB z)) (17034019083235291753671/1000000000000000000000000 : ℝ) (2129252385404411855163/125000000000000000000000 : ℝ) := by
    exact (hZ.mul_nonneg hB (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h42 : Bounds ((2 : ℝ)*(branchLog z)) (3909255286354490100897/500000000000000000000 : ℝ) (781851057270898050097/100000000000000000000 : ℝ) := by
    exact ((Bounds.refl (2 : ℝ)).mul_nonneg hL (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h43 : Bounds ((1 : ℝ)-z) (979944568945117673/1000000000000000000 : ℝ) (244986142236279419/250000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h44 : Bounds ((1 : ℝ)-z) (979944568945117673/1000000000000000000 : ℝ) (244986142236279419/250000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  have h45 : Bounds (((1 : ℝ)-z)*((1 : ℝ)-z)) (960291358205032484447547/1000000000000000000000000 : ℝ) (60018209887814530645451/62500000000000000000000 : ℝ) := by
    exact (h43.mul_nonneg h44 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h46 : Bounds ((branchB z)*(branchB z)) (360695115902296628761353/500000000000000000000000 : ℝ) (360695115902296651613033/500000000000000000000000 : ℝ) := by
    exact (hB.mul_nonneg hB (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h47 : Bounds ((((1 : ℝ)-z)*((1 : ℝ)-z))*((branchB z)*(branchB z))) (69274480549547608138721/100000000000000000000000 : ℝ) (692744805495476129517289/1000000000000000000000000 : ℝ) := by
    exact (h45.mul_nonneg h46 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have h48 : Bounds (((2 : ℝ)*(branchLog z))/((((1 : ℝ)-z)*((1 : ℝ)-z))*((branchB z)*(branchB z)))) (282156954144062429294093/25000000000000000000000 : ℝ) (5643139082881249193887473/500000000000000000000000 : ℝ) := by
    exact (h42.div_pos h47 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  refine ⟨?_,hB,?_⟩
  · exact h41
  · convert h48 using 1 <;> norm_num [branchMu,pow_two]

end SparseLowerTail.Section04.Refined

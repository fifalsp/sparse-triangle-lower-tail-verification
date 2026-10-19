import SparseLowerTail.Section04.BipodalAlgebra
import SparseLowerTail.Numerics.Intervals

/-! Exact scalar separation inequality `lem:scalar`. The logarithm enclosures
below use rational Taylor estimates checked in the kernel. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04 Numerics

private theorem scalar_log_03 : Bounds (Real.log (3/10:ℝ)) (-301/250:ℝ) (-1203/1000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/5:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (6/5:ℝ) = 2*Real.log 2+Real.log (3/10:ℝ) := by
    rw [show (6/5:ℝ)=(2:ℝ)^2*(3/10:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_04 : Bounds (Real.log (2/5:ℝ)) (-917/1000:ℝ) (-91/100:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/5:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (4/5:ℝ) = 1*Real.log 2+Real.log (2/5:ℝ) := by
    rw [show (4/5:ℝ)=(2:ℝ)^1*(2/5:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_05 : Bounds (Real.log (1/2:ℝ)) (-694/1000:ℝ) (-69/100:ℝ) := by
  rw [show (1/2:ℝ)=(2:ℝ)⁻¹ by norm_num,Real.log_inv]
  have h := log_two_bounds_22
  constructor <;> linarith [h.1,h.2]

private theorem scalar_log_0775 : Bounds (Real.log (31/40:ℝ)) (-51/200:ℝ) (-1/4:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (9/40:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (31/40:ℝ) = 0*Real.log 2+Real.log (31/40:ℝ) := by
    rw [show (31/40:ℝ)=(2:ℝ)^0*(31/40:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_027 : Bounds (Real.log (27/100:ℝ)) (-131/100:ℝ) (-12927/10000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-2/25:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (27/25:ℝ) = 2*Real.log 2+Real.log (27/100:ℝ) := by
    rw [show (27/25:ℝ)=(2:ℝ)^2*(27/100:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_037 : Bounds (Real.log (37/100:ℝ)) (-1/1:ℝ) (-4929/5000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-12/25:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (37/25:ℝ) = 2*Real.log 2+Real.log (37/100:ℝ) := by
    rw [show (37/25:ℝ)=(2:ℝ)^2*(37/100:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_0645 : Bounds (Real.log (129/200:ℝ)) (-109647/250000:ℝ) (-4371/10000:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-29/100:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (129/100:ℝ) = 1*Real.log 2+Real.log (129/200:ℝ) := by
    rw [show (129/100:ℝ)=(2:ℝ)^1*(129/200:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_0139 : Bounds (Real.log (139/1000:ℝ)) (-99/50:ℝ) (-197/100:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-14/125:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (139/125:ℝ) = 3*Real.log 2+Real.log (139/1000:ℝ) := by
    rw [show (139/125:ℝ)=(2:ℝ)^3*(139/1000:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_0106 : Bounds (Real.log (53/500:ℝ)) (-9/4:ℝ) (-56/25:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (19/125:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (106/125:ℝ) = 3*Real.log 2+Real.log (53/500:ℝ) := by
    rw [show (106/125:ℝ)=(2:ℝ)^3*(53/500:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_0047 : Bounds (Real.log (47/1000:ℝ)) (-153/50:ℝ) (-61/20:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (31/125:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (94/125:ℝ) = 4*Real.log 2+Real.log (47/1000:ℝ) := by
    rw [show (94/125:ℝ)=(2:ℝ)^4*(47/1000:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_004716 : Bounds (Real.log (1179/25000:ℝ)) (-611/200:ℝ) (-1527/500:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (767/3125:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (2358/3125:ℝ) = 4*Real.log 2+Real.log (1179/25000:ℝ) := by
    rw [show (2358/3125:ℝ)=(2:ℝ)^4*(1179/25000:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

private theorem scalar_log_017 : Bounds (Real.log (17/100:ℝ)) (-178/100:ℝ) (-177/100:ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-9/25:ℝ)) (by norm_num) 28
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (34/25:ℝ) = 3*Real.log 2+Real.log (17/100:ℝ) := by
    rw [show (34/25:ℝ)=(2:ℝ)^3*(17/100:ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_22.1
  have h2u := log_two_bounds_22.2
  constructor <;> linarith

theorem antitoneOn_vertexEntropy : AntitoneOn vertexEntropy (Icc 0 1) := by
  intro u hu v hv huv
  have h := strictAntiOn_entropy.antitoneOn hu hv huv
  unfold vertexEntropy entropy at *
  linarith

theorem hasDerivAt_vertexEntropy {u : ℝ} (hu : u≠0) :
    HasDerivAt vertexEntropy (Real.log u-1) u := by
  convert ((hasDerivAt_entropy hu).sub (hasDerivAt_id u)).add_const 1 using 1
  funext x
  unfold vertexEntropy entropy
  simp only [Pi.sub_apply,id_eq]
  ring

private def scalarW (v : ℝ) := -Real.log (v-13/100)/(93/10)
private def scalarG (v : ℝ) := vertexEntropy (scalarW v)+vertexEntropy v

private theorem scalarW_bounds {v : ℝ} (hv : v∈Icc (3/10:ℝ) (31/40)) :
    0<scalarW v ∧ scalarW v<1/5 := by
  have hp : 0<v-13/100 := by linarith [hv.1]
  have h1 : v-13/100<1 := by linarith [hv.2]
  have hneg := Real.log_neg hp h1
  have hlo := Real.log_le_log (by norm_num : (0:ℝ)<17/100)
    (show (17/100:ℝ)≤v-13/100 by linarith [hv.1])
  have hnum := scalar_log_017.1
  unfold scalarW
  constructor
  · exact div_pos (neg_pos.mpr hneg) (by norm_num)
  · rw [div_lt_iff₀ (by norm_num : (0:ℝ)<93/10)]
    linarith

private theorem scalarW_antitone {u v : ℝ} (hu : 13/100<u) (huv : u≤v) :
    scalarW v≤scalarW u := by
  have h := Real.log_le_log (show 0<u-13/100 by linarith)
    (show u-13/100≤v-13/100 by linarith)
  unfold scalarW
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

private theorem hasDerivAt_scalarG {v : ℝ} (hv : v∈Icc (3/10:ℝ) (31/40)) :
    HasDerivAt scalarG (Real.log v-1+
      (1-Real.log (scalarW v))/((93/10)*(v-13/100))) v := by
  have hp : v-13/100≠0 := ne_of_gt (by linarith [hv.1])
  have hw := scalarW_bounds hv
  have hd : HasDerivAt scalarW (-(v-13/100)⁻¹/(93/10)) v := by
    convert (((hasDerivAt_id v).sub_const (13/100)).log hp).neg.div_const (93/10) using 1
    simp
  convert ((hasDerivAt_vertexEntropy hw.1.ne').comp v hd).add
    (hasDerivAt_vertexEntropy (ne_of_gt (by linarith [hv.1]))) using 1
  field_simp
  ring

private theorem scalar_derivative_sign {v lv lw d : ℝ}
    (hd : 0<d) (hden : d≤(93/10)*(v-13/100))
    (hv : Real.log v≤lv) (hw : lw≤Real.log (scalarW v))
    (hlv : lv≤1) (hn : 1-lw<(1-lv)*d) :
    Real.log v-1+(1-Real.log (scalarW v))/((93/10)*(v-13/100))<0 := by
  have hprod := mul_le_mul (show 1-lv≤1-Real.log v by linarith) hden hd.le (by linarith : 0≤1-Real.log v)
  have h : (1-Real.log (scalarW v))/((93/10)*(v-13/100))<1-Real.log v := by
    apply (div_lt_iff₀ (hd.trans_le hden)).mpr
    linarith
  linarith

private theorem scalarW_log_lower {v V w : ℝ} (hv : 13/100<v) (hV : v≤V)
    (hw : 0<w) (hlog : Real.log (V-13/100)≤-(93/10)*w) :
    Real.log w≤Real.log (scalarW v) := by
  apply Real.log_le_log hw
  unfold scalarW
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<93/10)).mpr
  have h := Real.log_le_log (show 0<v-13/100 by linarith)
    (show v-13/100≤V-13/100 by linarith)
  linarith

private theorem scalarG_deriv_neg {v : ℝ} (hv : v∈Icc (3/10:ℝ) (31/40)) :
    deriv scalarG v<0 := by
  rw [(hasDerivAt_scalarG hv).deriv]
  by_cases hv4 : v≤2/5
  · have hlogv := Real.log_le_log (show 0<v by linarith [hv.1]) hv4
    have hlogw := scalarW_log_lower (by linarith [hv.1]) hv4
      (by norm_num : (0:ℝ)<139/1000) (by norm_num; linarith [scalar_log_027.2])
    apply scalar_derivative_sign (lv := -91/100) (lw := -198/100) (d := 1581/1000)
      (by norm_num) (by linarith [hv.1])
      (hlogv.trans scalar_log_04.2) (by linarith [scalar_log_0139.1])
      (by norm_num) (by norm_num)
  · by_cases hv5 : v≤1/2
    · have hlogv := Real.log_le_log (show 0<v by linarith [hv.1]) hv5
      have hlogw := scalarW_log_lower (by linarith [hv.1]) hv5
        (by norm_num : (0:ℝ)<53/500) (by norm_num; linarith [scalar_log_037.2])
      apply scalar_derivative_sign (lv := -69/100) (lw := -225/100) (d := 2511/1000)
        (by norm_num) (by linarith)
        (hlogv.trans scalar_log_05.2) (by linarith [scalar_log_0106.1])
        (by norm_num) (by norm_num)
    · have hlogv := Real.log_le_log (show 0<v by linarith [hv.1]) hv.2
      have hlogw := scalarW_log_lower (by linarith [hv.1]) hv.2
        (by norm_num : (0:ℝ)<47/1000) (by norm_num; linarith [scalar_log_0645.2])
      apply scalar_derivative_sign (lv := -1/4) (lw := -306/100) (d := 3441/1000)
        (by norm_num) (by linarith)
        (hlogv.trans scalar_log_0775.2) (by linarith [scalar_log_0047.1])
        (by norm_num) (by norm_num)

private theorem scalarG_antitone : AntitoneOn scalarG (Icc (3/10:ℝ) (31/40)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro v hv
    exact (hasDerivAt_scalarG hv).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    exact (hasDerivAt_scalarG ⟨hv.1.le,hv.2.le⟩).differentiableAt.differentiableWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    exact (scalarG_deriv_neg ⟨hv.1.le,hv.2.le⟩).le

private theorem scalarG_endpoint : (201/100:ℝ)<scalarG (31/40) := by
  have hw := scalarW_bounds (v := (31/40:ℝ)) (by norm_num)
  have hwu : scalarW (31/40)≤(1179/25000:ℝ) := by
    unfold scalarW
    norm_num
    linarith [scalar_log_0645.1]
  have hk := antitoneOn_vertexEntropy ⟨hw.1.le,by linarith [hw.2]⟩
    (show (1179/25000:ℝ)∈Icc (0:ℝ) 1 by norm_num) hwu
  have h1 := scalar_log_004716.1
  have h2 := scalar_log_0775.1
  unfold scalarG vertexEntropy at *
  norm_num at *
  linarith

/-- Manuscript `lem:scalar`: the larger row-block mean is above 0.775. -/
theorem scalar_exclusion {u v : ℝ} (hu : 0≤u) (huv : u≤v) (hv : v≤1)
    (hk : (vertexEntropy u+vertexEntropy v)/2≤(1005/1000:ℝ))
    (he : v≤Real.exp (-(93/10)*u)+(13/100)) : (775/1000:ℝ)<v := by
  by_contra hbad
  have hv775 : v≤(31/40:ℝ) := by linarith
  have hv03 : (3/10:ℝ)<v := by
    by_contra h
    have hvlo : v≤(3/10:ℝ) := by linarith
    have hku := antitoneOn_vertexEntropy ⟨hu,huv.trans hv⟩
      (show (3/10:ℝ)∈Icc (0:ℝ) 1 by norm_num) (huv.trans hvlo)
    have hkv := antitoneOn_vertexEntropy ⟨hu.trans huv,hv⟩
      (show (3/10:ℝ)∈Icc (0:ℝ) 1 by norm_num) hvlo
    have hlog := scalar_log_03.1
    unfold vertexEntropy at *
    norm_num at *
    linarith
  have hvmem : v∈Icc (3/10:ℝ) (31/40) := ⟨hv03.le,hv775⟩
  have hw := scalarW_bounds hvmem
  have huw : u≤scalarW v := by
    have hlog := Real.log_le_log (show 0<v-13/100 by linarith)
      (show v-13/100≤Real.exp (-(93/10)*u) by linarith)
    rw [Real.log_exp] at hlog
    unfold scalarW
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<93/10)]
    linarith
  have hku := antitoneOn_vertexEntropy ⟨hu,huv.trans hv⟩ ⟨hw.1.le,by linarith [hw.2]⟩ huw
  have hG := scalarG_antitone hvmem (show (31/40:ℝ)∈Icc (3/10:ℝ) (31/40) by norm_num) hv775
  have hend := scalarG_endpoint
  unfold scalarG at hG hend
  linarith

end SparseLowerTail.Section07

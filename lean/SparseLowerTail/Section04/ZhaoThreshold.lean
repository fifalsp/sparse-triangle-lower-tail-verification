import SparseLowerTail.Section04.BalancedPhase

/-! The one-variable maximum formula and equal-cost characterization of the transition. -/
noncomputable section
open Set
namespace SparseLowerTail.Section04

/-- The explicit one-variable function in `prop:zhao`. -/
def zhaoR (z : ℝ) : ℝ := Real.exp (-balancedCost (rayA z) (rayB z)/rayExcess z)

theorem rayCost_pos {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) : 0<balancedCost (rayA z) (rayB z) := by
  have ha := (rayA_pos hz.1).le
  have hb := (rayB_pos hz.1).le
  have hab : rayA z<rayB z := (div_lt_div_iff_of_pos_right (kappa_pos hz.1)).mpr hz.2
  exact (entropy_nonneg (by positivity : 0≤(rayA z+rayB z)/2)).trans_lt
    (entropy_mean_lt_balancedCost ha hb (ne_of_lt hab))

theorem zhaoR_mem_Ioo {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) : zhaoR z∈Ioo (0:ℝ) 1 :=
  ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (rayCost_pos hz)) (rayExcess_pos hz.1 hz.2))⟩

/-- The normalized entropy gap is a positive multiple of a log difference. -/
theorem rayGap_log_zhaoR {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) (r : ℝ) :
    rayGap r z=rayExcess z*(Real.log r-Real.log (zhaoR z)) := by
  rw [zhaoR,Real.log_exp]
  unfold rayGap
  have hA : rayExcess z≠0 := ne_of_gt (rayExcess_pos hz.1 hz.2)
  field_simp
  ring

theorem rayGap_zero_iff_zhaoR {z r : ℝ} (hz : z∈Ioo (0:ℝ) 1) (hr : 0<r) :
    rayGap r z=0 ↔ r=zhaoR z := by
  rw [rayGap_log_zhaoR hz,mul_eq_zero]
  have hA : rayExcess z≠0 := ne_of_gt (rayExcess_pos hz.1 hz.2)
  simp only [hA,false_or,sub_eq_zero]
  exact ⟨Real.log_injOn_pos hr (zhaoR_mem_Ioo hz).1,fun h => congrArg Real.log h⟩

/-- Every value of the explicit function is bounded by the transition target. -/
theorem zhaoR_le_threshold {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) : zhaoR z≤threshold := by
  have hh := (rayGap_at_transition hz).1
  rw [rayGap_log_zhaoR hz] at hh
  have hlog : Real.log (zhaoR z)≤Real.log transitionTarget := by
    have hp := rayExcess_pos hz.1 hz.2
    nlinarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (zhaoR_mem_Ioo hz).1,Real.exp_log transitionTarget_mem_Ioo.1] at he
  rwa [threshold_eq_transitionTarget]

/-- The maximum is attained at exactly the crossing parameter. -/
theorem zhaoR_eq_threshold_iff {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    zhaoR z=threshold ↔ z=transitionParameter := by
  rw [threshold_eq_transitionTarget,← eq_comm (a:=transitionTarget),← rayGap_zero_iff_zhaoR hz transitionTarget_mem_Ioo.1]
  exact (rayGap_at_transition hz).2

/-- The normalized within-block value is strictly below one. -/
theorem rayA_lt_one {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) : rayA z<1 := by
  have hk := kappa_pos hz.1
  have hc := kappa_cube hz.1.le
  have hgap : 0<3*z*(1-z^2) := by
    have hs : z^2<1 := (sq_lt_one_iff_abs_lt_one z).mpr (by rw [abs_of_pos hz.1]; exact hz.2)
    exact mul_pos (mul_pos (by norm_num) hz.1) (sub_pos.mpr hs)
  have hzk : z<kappa z := by
    apply (show Odd (3:ℕ) by decide).strictMono_pow.lt_iff_lt.mp
    nlinarith
  exact (div_lt_one hk).mpr hzk

/-- Equal-cost nonconstant balanced pairs are precisely the explicit R(z) values. -/
theorem zhao_equal_cost_pair_iff {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) :
    (∃ a b : ℝ, a∈Ioo (0:ℝ) r ∧ 0<b ∧ balancedTriangle a b=r^3 ∧ balancedCost a b=entropy r) ↔
      ∃ z∈Ioo (0:ℝ) 1, r=zhaoR z := by
  constructor
  · rintro ⟨a,b,ha,hb,ht,hcost⟩
    have hab : a<b := by
      by_contra h
      have hba : b≤a := le_of_not_gt h
      have hs : b^2≤a^2 := (sq_le_sq₀ hb.le ha.1.le).mpr hba
      have htri : balancedTriangle a b≤a^3 := by unfold balancedTriangle; nlinarith [mul_le_mul_of_nonneg_left hs ha.1.le]
      have har : a^3<r^3 := (show Odd (3:ℕ) by decide).strictMono_pow ha.2
      linarith
    obtain ⟨_hap,hz,hz1,hea,heb⟩ := saturated_pair_ray ha.1.le hab hr.1 ht
    refine ⟨a/b,⟨hz,hz1⟩,(rayGap_zero_iff_zhaoR ⟨hz,hz1⟩ hr.1).mp ?_⟩
    have hh := scaled_ray_cost hz hr.1
    rw [← hea,← heb,hcost] at hh
    have hhzero : r*rayGap r (a/b)=0 := by linarith
    exact (mul_eq_zero.mp hhzero).resolve_left (ne_of_gt hr.1)
  · rintro ⟨z,hz,he⟩
    have hgap := (rayGap_zero_iff_zhaoR hz hr.1).mpr he
    refine ⟨r*rayA z,r*rayB z,⟨mul_pos hr.1 (rayA_pos hz.1),?_⟩,
      mul_pos hr.1 (rayB_pos hz.1),scaled_ray_triangle hz.1 r,?_⟩
    · nlinarith [mul_lt_mul_of_pos_left (rayA_lt_one hz) hr.1]
    · rw [scaled_ray_cost hz.1 hr.1,hgap,mul_zero,add_zero]

/-- The transition is the largest target possessing such an equal-cost nonconstant pair. -/
theorem zhao_largest_target :
    (∃ a b : ℝ, a∈Ioo (0:ℝ) threshold ∧ 0<b ∧ balancedTriangle a b=threshold^3 ∧
      balancedCost a b=entropy threshold) ∧
    ∀ r∈Ioo (0:ℝ) 1, (∃ a b : ℝ, a∈Ioo (0:ℝ) r ∧ 0<b ∧ balancedTriangle a b=r^3 ∧
      balancedCost a b=entropy r) → r≤threshold := by
  have hz : transitionParameter∈Ioo (0:ℝ) 1 :=
    ⟨transitionParameter_mem_Ioo.1,transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2⟩
  refine ⟨(zhao_equal_cost_pair_iff threshold_mem_Ioo).mpr ⟨transitionParameter,hz,
    ((zhaoR_eq_threshold_iff hz).mpr rfl).symm⟩,?_⟩
  intro r hr hp
  obtain ⟨z,hz,he⟩ := (zhao_equal_cost_pair_iff hr).mp hp
  rw [he]
  exact zhaoR_le_threshold hz

end SparseLowerTail.Section04

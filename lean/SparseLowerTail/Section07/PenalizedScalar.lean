import SparseLowerTail.Section07.ExternalReduction
import SparseLowerTail.Section04.BalancedDerivative
import SparseLowerTail.Section04.Rescaling

/-! Scalar stationary reduction for the penalized problem, `lem:stationary`.
Every boundary exclusion and EL equation below is proved from the actual scalar
minimization problem. No KP26 input is needed for these finite-dimensional facts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

theorem hasDerivAt_balancedPenalty_left (γ a b : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun x => balancedPenalty γ x b)
      (Real.log a/2+3*γ*(a^2+b^2)/4) a := by
  unfold balancedPenalty balancedCost balancedTriangle
  convert (((hasDerivAt_entropy ha).add_const (entropy b)).div_const 2).add
    (((((hasDerivAt_id a).pow 3).add
      (((hasDerivAt_id a).const_mul 3).mul_const (b^2))).div_const 4).const_mul γ) using 1
  dsimp only [id]
  ring

theorem hasDerivAt_balancedPenalty_right (γ a b : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun y => balancedPenalty γ a y)
      (Real.log b/2+3*γ*a*b/2) b := by
  unfold balancedPenalty balancedCost balancedTriangle
  convert (((hasDerivAt_entropy hb).const_add (entropy a)).div_const 2).add
    (((((hasDerivAt_id b).pow 2).const_mul (3*a)).const_add (a^3)).div_const 4 |>.const_mul γ)
    using 1
  dsimp only [id]
  ring

private theorem small_entropy_step {γ : ℝ} (hγ : 0 < γ) :
    ∃ δ : ℝ, δ ∈ Ioo (0:ℝ) 1 ∧ Real.log δ = -(4*γ+2) := by
  refine ⟨Real.exp (-(4*γ+2)), ⟨Real.exp_pos _, ?_⟩, Real.log_exp _⟩
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem penalizedMinimizer_pos {γ a b : ℝ} (hγ : 0 < γ)
    (h : IsBalancedPenalizedMinimizer γ a b) : 0 < a ∧ 0 < b := by
  obtain ⟨δ,hδ,hlog⟩ := small_entropy_step hγ
  have hδpos := hδ.1
  have hδlt := hδ.2
  have hδ2 : δ^2 ≤ 1 := by nlinarith [sq_nonneg (1-δ)]
  have hδ3 : δ^3 ≤ δ := by nlinarith [mul_nonneg hδ.1.le (sub_nonneg.mpr hδ2)]
  constructor
  · by_contra hn
    have ha : a = 0 := le_antisymm (le_of_not_gt hn) h.1.1
    have hh := h.2.2 δ b ⟨hδ.1.le,hδ.2.le⟩ h.2.1
    rw [ha] at hh
    have hb2 : b^2 ≤ 1 := by nlinarith [h.2.1.1,h.2.1.2]
    have hdb : δ*b^2 ≤ δ := by nlinarith
    unfold balancedPenalty balancedCost balancedTriangle entropy at hh
    simp only [zero_mul] at hh
    rw [hlog] at hh
    have hm := mul_le_mul_of_nonneg_left (show δ^3+3*δ*b^2 ≤ 4*δ by nlinarith) hγ.le
    nlinarith [mul_pos hγ hδ.1]
  · by_contra hn
    have hb : b = 0 := le_antisymm (le_of_not_gt hn) h.2.1.1
    have hh := h.2.2 a δ h.1 ⟨hδ.1.le,hδ.2.le⟩
    rw [hb] at hh
    have hδsq : δ^2 ≤ δ := by nlinarith
    have hab : a*δ^2 ≤ δ := by nlinarith [h.1.1,h.1.2]
    unfold balancedPenalty balancedCost balancedTriangle entropy at hh
    simp only [zero_mul] at hh
    rw [hlog] at hh
    have hm := mul_le_mul_of_nonneg_left hab hγ.le
    nlinarith [mul_pos hγ hδ.1]

private theorem derivative_nonpos_at_one {f : ℝ → ℝ} {d : ℝ}
    (h : ∀ x ∈ Icc (0:ℝ) 1, f 1 ≤ f x) (hd : HasDerivAt f d 1) : d ≤ 0 := by
  have hmin : IsLocalMinOn (fun s => f (1-s)) (Ici 0) 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds]
      with s hs hs1
    simpa using h (1-s) ⟨by linarith,by linarith [show 0 ≤ s from hs]⟩
  have hg : HasDerivAt (fun s => f (1-s)) (-d) 0 := by
    have hp : HasDerivAt (fun s : ℝ => 1-s) (-1) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub 1
    have hd1 : HasDerivAt f d (1-(0:ℝ)) := by simpa using hd
    convert hd1.comp 0 hp using 1
    simp
  have hn := right_derivative_nonneg_of_localMin hmin hg.hasDerivWithinAt
  linarith

theorem penalizedMinimizer_interior {γ a b : ℝ} (hγ : 0 < γ)
    (h : IsBalancedPenalizedMinimizer γ a b) : a ∈ Ioo (0:ℝ) 1 ∧ b ∈ Ioo (0:ℝ) 1 := by
  have hp := penalizedMinimizer_pos hγ h
  have ha : a < 1 := by
    by_contra hn
    have he : a = 1 := le_antisymm h.1.2 (le_of_not_gt hn)
    have hd := derivative_nonpos_at_one
      (f := fun x => balancedPenalty γ x b) (by simpa [he] using fun x hx => h.2.2 x b hx h.2.1)
      (hasDerivAt_balancedPenalty_left γ 1 b one_ne_zero)
    simp only [Real.log_one, zero_div, zero_add, one_pow] at hd
    nlinarith [sq_nonneg b, mul_pos hγ (show 0<1+b^2 by positivity)]
  have hb : b < 1 := by
    by_contra hn
    have he : b = 1 := le_antisymm h.2.1.2 (le_of_not_gt hn)
    have hd := derivative_nonpos_at_one
      (f := fun y => balancedPenalty γ a y) (by simpa [he] using fun y hy => h.2.2 a y h.1 hy)
      (hasDerivAt_balancedPenalty_right γ a 1 one_ne_zero)
    simp only [Real.log_one, zero_div, zero_add, mul_one] at hd
    nlinarith [mul_pos hγ hp.1]
  exact ⟨⟨hp.1,ha⟩,⟨hp.2,hb⟩⟩

theorem penalizedMinimizer_balancedEL {γ a b : ℝ} (hγ : 0 < γ)
    (h : IsBalancedPenalizedMinimizer γ a b) : BalancedEL a b (3*γ) := by
  have hi := penalizedMinimizer_interior hγ h
  have hma : IsLocalMin (fun x => balancedPenalty γ x b) a := by
    filter_upwards [isOpen_Ioo.mem_nhds hi.1] with x hx
    exact h.2.2 x b ⟨hx.1.le,hx.2.le⟩ h.2.1
  have hmb : IsLocalMin (fun y => balancedPenalty γ a y) b := by
    filter_upwards [isOpen_Ioo.mem_nhds hi.2] with y hy
    exact h.2.2 a y h.1 ⟨hy.1.le,hy.2.le⟩
  have ha := hma.hasDerivAt_eq_zero (hasDerivAt_balancedPenalty_left γ a b (ne_of_gt hi.1.1))
  have hb := hmb.hasDerivAt_eq_zero (hasDerivAt_balancedPenalty_right γ a b (ne_of_gt hi.2.1))
  constructor <;> nlinarith

/-- The stationary Euler identity, manuscript `lem:stationary`(c). -/
theorem penalized_stationary_identity {γ a b : ℝ} (h : BalancedEL a b (3*γ)) :
    balancedCost a b+3*γ*balancedTriangle a b = 1-(a+b)/2 := by
  have he := balancedEL_multiplier_cost h
  linarith

/-- Every nonconstant penalized minimizer is exactly a point of the proved
stationary branch, with its own ratio as parameter. -/
theorem penalizedMinimizer_branch {γ a b : ℝ} (hγ : 0 < γ)
    (h : IsBalancedPenalizedMinimizer γ a b) (hne : a ≠ b) :
    a < b ∧ a/b ∈ Ioo (0:ℝ) 1 ∧
      a = branchA (a/b) ∧ b = branchB (a/b) ∧ branchMu (a/b) = 3*γ := by
  have hi := penalizedMinimizer_interior hγ h
  have hap := hi.1.1
  have hal := hi.1.2
  have hbp := hi.2.1
  have hbl := hi.2.2
  have hb2 : b^2 < 1 := by nlinarith
  have ha3 : a^3 < 1 := pow_lt_one₀ hi.1.1.le hi.1.2 (by norm_num)
  have hab : a*b^2 < 1 := by nlinarith [sq_nonneg b]
  have ht : balancedTriangle a b < 1 := by unfold balancedTriangle; linarith
  obtain ⟨hab,hz,hz1,ha,hb,hm⟩ := balancedEL_parametrization hi.1.1 hi.2.1 hne ht
    (penalizedMinimizer_balancedEL hγ h)
  exact ⟨hab,⟨hz,hz1⟩,ha,hb,hm.symm⟩

/-- The scalar equation for a constant stationary pair. -/
def constantEquation (γ s : ℝ) : ℝ := Real.log s+3*γ*s^2

theorem constantEquation_strictMono {γ : ℝ} (hγ : 0 ≤ γ) :
    StrictMonoOn (constantEquation γ) (Ioi 0) := by
  intro x hx y hy hxy
  have hlog := Real.log_lt_log (show 0<x from hx) hxy
  have hsq : x^2 ≤ y^2 := by nlinarith [show 0<x from hx,show 0<y from hy]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3*γ by positivity)
  unfold constantEquation
  linarith

theorem exists_unique_constantRoot {γ : ℝ} (hγ : 0 < γ) :
    ∃! s, s ∈ Ioo (0:ℝ) 1 ∧ constantEquation γ s = 0 := by
  obtain ⟨δ,hδ,hlog⟩ := small_entropy_step hγ
  have hneg : constantEquation γ δ < 0 := by
    have hs : δ^2 ≤ 1 := by nlinarith [hδ.1,hδ.2]
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3*γ by positivity)
    unfold constantEquation
    rw [hlog]
    linarith
  have hpos : 0 < constantEquation γ 1 := by simpa [constantEquation] using hγ
  have hc : ContinuousOn (constantEquation γ) (Icc δ 1) := by
    apply ContinuousOn.add
    · exact Real.continuousOn_log.mono (fun x hx => ne_of_gt (hδ.1.trans_le hx.1))
    · fun_prop
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc hδ.2.le hc ⟨hneg.le,hpos.le⟩
  have hs1 : s < 1 := by
    apply lt_of_le_of_ne hs.2
    intro hh
    rw [hh] at he
    linarith
  refine ⟨s,⟨⟨hδ.1.trans_le hs.1,hs1⟩,he⟩,?_⟩
  intro t ht
  exact (constantEquation_strictMono hγ.le).injOn ht.1.1
    (hδ.1.trans_le hs.1) (ht.2.trans he.symm)

/-- The constant stationary parameter `s_γ`, with arbitrary value outside γ>0. -/
def constantRoot (γ : ℝ) : ℝ :=
  if hγ : 0 < γ then Classical.choose (exists_unique_constantRoot hγ) else 1

theorem constantRoot_spec {γ : ℝ} (hγ : 0 < γ) :
    constantRoot γ ∈ Ioo (0:ℝ) 1 ∧ constantEquation γ (constantRoot γ) = 0 := by
  rw [constantRoot, dif_pos hγ]
  exact (Classical.choose_spec (exists_unique_constantRoot hγ)).1

theorem constantRoot_unique {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s)
    (he : constantEquation γ s = 0) : s = constantRoot γ :=
  (constantEquation_strictMono hγ.le).injOn hs (constantRoot_spec hγ).1.1
    (he.trans (constantRoot_spec hγ).2.symm)

theorem constantRoot_strictAnti : StrictAntiOn constantRoot (Ioi 0) := by
  intro γ hγ η hη hlt
  have hs := constantRoot_spec hγ
  have ht := constantRoot_spec hη
  by_contra hn
  have hle := le_of_not_gt hn
  have heq := (constantEquation_strictMono (le_of_lt hγ)).monotoneOn hs.1.1 ht.1.1 hle
  have hparam : constantEquation γ (constantRoot η) < constantEquation η (constantRoot η) := by
    unfold constantEquation
    nlinarith [sq_pos_of_pos ht.1.1]
  rw [hs.2,ht.2] at *
  linarith

/-- Full stationary-point classification in the open square. -/
theorem penalized_stationary_iff {γ a b : ℝ} (hγ : 0 < γ)
    (ha : a ∈ Ioo (0:ℝ) 1) (hb : b ∈ Ioo (0:ℝ) 1) :
    BalancedEL a b (3*γ) ↔
      (a=constantRoot γ ∧ b=constantRoot γ) ∨
      ∃ z ∈ Ioo (0:ℝ) 1, a=branchA z ∧ b=branchB z ∧ branchMu z=3*γ := by
  constructor
  · intro hel
    by_cases he : a=b
    · left
      have hroot : a=constantRoot γ := constantRoot_unique hγ ha.1 (by
        have hh := hel.2
        rw [← he] at hh
        unfold constantEquation
        nlinarith)
      exact ⟨hroot,he.symm.trans hroot⟩
    · right
      have hb2 : b^2 < 1 := by nlinarith [hb.1,hb.2]
      have ha3 : a^3 < 1 := pow_lt_one₀ ha.1.le ha.2 (by norm_num)
      have hab : a*b^2 < 1 := by nlinarith [ha.1,ha.2,sq_nonneg b]
      have ht : balancedTriangle a b < 1 := by unfold balancedTriangle; linarith
      obtain ⟨_,hz,hz1,ha,hb,hm⟩ := balancedEL_parametrization ha.1 hb.1 he ht hel
      exact ⟨a/b,⟨hz,hz1⟩,ha,hb,hm.symm⟩
  · rintro (⟨rfl,rfl⟩|⟨z,hz,rfl,rfl,hm⟩)
    · have he := (constantRoot_spec hγ).2
      unfold constantEquation at he
      constructor <;> nlinarith
    · rw [← hm]
      exact branch_balancedEL hz.1 hz.2

/-- Every actual scalar minimizer belongs to the classified stationary list. -/
theorem penalizedMinimizer_classification {γ a b : ℝ} (hγ : 0 < γ)
    (h : IsBalancedPenalizedMinimizer γ a b) :
    (a=constantRoot γ ∧ b=constantRoot γ) ∨
      ∃ z ∈ Ioo (0:ℝ) 1, a=branchA z ∧ b=branchB z ∧ branchMu z=3*γ :=
  (penalized_stationary_iff hγ (penalizedMinimizer_interior hγ h).1
    (penalizedMinimizer_interior hγ h).2).mp (penalizedMinimizer_balancedEL hγ h)

/-- The penalized objective restricted to constant pairs. -/
def constantPenalty (γ s : ℝ) : ℝ := entropy s+γ*s^3

theorem balancedPenalty_diagonal (γ s : ℝ) :
    balancedPenalty γ s s = constantPenalty γ s := by
  unfold balancedPenalty balancedCost balancedTriangle constantPenalty
  ring

theorem continuous_constantPenalty (γ : ℝ) : Continuous (constantPenalty γ) :=
  continuous_entropy.add (continuous_const.mul (continuous_id.pow 3))

theorem hasDerivAt_constantPenalty (γ s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (constantPenalty γ) (constantEquation γ s) s := by
  convert (hasDerivAt_entropy hs).add (((hasDerivAt_id s).pow 3).const_mul γ) using 1
  simp [constantEquation]
  ring

/-- The constant root is the unique constant-pair minimum, including endpoints. -/
theorem constantPenalty_strict_min {γ s : ℝ} (hγ : 0 < γ)
    (hs : s ∈ Icc (0:ℝ) 1) (hne : s ≠ constantRoot γ) :
    constantPenalty γ (constantRoot γ) < constantPenalty γ s := by
  have hr := constantRoot_spec hγ
  have hleft : StrictAntiOn (constantPenalty γ) (Icc 0 (constantRoot γ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_constantPenalty γ).continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_constantPenalty γ x (ne_of_gt hx.1)).deriv]
    have hh := constantEquation_strictMono hγ.le hx.1 hr.1.1 hx.2
    rwa [hr.2] at hh
  have hright : StrictMonoOn (constantPenalty γ) (Icc (constantRoot γ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_constantPenalty γ).continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_constantPenalty γ x (ne_of_gt (hr.1.1.trans hx.1))).deriv]
    have hh := constantEquation_strictMono hγ.le hr.1.1 (hr.1.1.trans hx.1) hx.1
    rwa [hr.2] at hh
  rcases lt_or_gt_of_ne hne with hl | hg
  · exact hleft ⟨hs.1,hl.le⟩ ⟨hr.1.1.le,le_rfl⟩ hl
  · exact hright ⟨le_rfl,hr.1.2.le⟩ ⟨hg.le,hs.2⟩ hg

theorem constantPenalty_min {γ s : ℝ} (hγ : 0 < γ) (hs : s ∈ Icc (0:ℝ) 1) :
    constantPenalty γ (constantRoot γ) ≤ constantPenalty γ s := by
  by_cases he : s=constantRoot γ
  · simp [he]
  · exact (constantPenalty_strict_min hγ hs he).le

/-- At a tie, a nonconstant stationary pair has larger edge density and smaller
triangle density than the stationary constant. This is the strict comparison
in `lem:tie`, before any fold or gap-root argument. -/
theorem stationary_tie_density_order {γ a b : ℝ} (hγ : 0 < γ)
    (ha : a ∈ Ioo (0:ℝ) 1) (hb : b ∈ Ioo (0:ℝ) 1) (hne : a ≠ b)
    (hel : BalancedEL a b (3*γ))
    (htie : balancedPenalty γ a b = constantPenalty γ (constantRoot γ)) :
    constantRoot γ < (a+b)/2 ∧ balancedTriangle a b < (constantRoot γ)^3 := by
  let s := constantRoot γ
  have hs := constantRoot_spec hγ
  have hcost := penalized_stationary_identity hel
  have hsidentity : entropy s+3*γ*s^3 = 1-s := by
    have he := hs.2
    change Real.log s+3*γ*s^2=0 at he
    unfold entropy
    nlinarith [congrArg (fun x : ℝ => s*x) he]
  have hid : 2*γ*(balancedTriangle a b-s^3) = s-(a+b)/2 := by
    change balancedCost a b+γ*balancedTriangle a b = entropy s+γ*s^3 at htie
    linarith
  have hm : s < (a+b)/2 := by
    by_contra hn
    have hms : (a+b)/2 ≤ s := le_of_not_gt hn
    have ht : s^3 ≤ balancedTriangle a b := by nlinarith
    have hmean : (a+b)/2 ∈ Icc (0:ℝ) 1 := by
      constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
    have hh := strictAntiOn_entropy.antitoneOn hmean ⟨hs.1.1.le,hs.1.2.le⟩ hms
    have hj := entropy_mean_lt_balancedCost ha.1.le hb.1.le hne
    change balancedCost a b+γ*balancedTriangle a b = entropy s+γ*s^3 at htie
    nlinarith [mul_le_mul_of_nonneg_left ht hγ.le]
  exact ⟨hm,by nlinarith⟩

end SparseLowerTail.Section07

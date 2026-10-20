import SparseLowerTail.Section03.LowerTailRate

/-! Eventual scalar bounds needed to apply the finite conditioned-structure estimate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section03

/-- The sparse hypothesis also forces np to infinity. -/
theorem sparse_edge_scale_tendsto_atTop (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hp : ∀ j, 0≤p j)
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => (n j:ℝ)*p j) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hsparse
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hj
  have hn1 : (1:ℝ)≤n j := by exact_mod_cast hj
  have hs := Real.sq_sqrt (show (0:ℝ)≤n j by positivity)
  have hr : Real.sqrt (n j:ℝ)≤(n j:ℝ) := by nlinarith [Real.sqrt_nonneg (n j:ℝ)]
  exact mul_le_mul_of_nonneg_right hr (hp j)

/-- The normalization pn² tends to infinity. -/
theorem sparse_volume_tendsto_atTop (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hp : ∀ j, 0≤p j)
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => p j*(n j:ℝ)^2) atTop atTop := by
  have hh := (triangleRateScale_tendsto_atTop n p hn hp hsparse).const_mul_atTop (by norm_num : (0:ℝ)<2)
  convert hh using 1
  funext j
  unfold triangleRateScale
  ring

/-- The 2·4ⁿ cut-test prefactor is absorbed by half of its exponential rate. -/
theorem eventually_cut_prefactor_bound (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hnp : Tendsto (fun j => (n j:ℝ)*p j) atTop atTop)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ j in atTop, 2*4^(n j)*Real.exp (-ε^2*p j*(n j:ℝ)^2/128)≤
      Real.exp (-ε^2*p j*(n j:ℝ)^2/256) := by
  have hcast : Tendsto (fun j => (n j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  filter_upwards [hcast.eventually_ge_atTop (Real.log 2),
    hnp.eventually_ge_atTop (256*(Real.log 4+1)/ε^2)] with j hj hnpbound
  have hpref : Real.log 2+(n j:ℝ)*Real.log 4≤ε^2*p j*(n j:ℝ)^2/256 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hnpbound
    have hm := mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤n j by positivity)
    nlinarith
  have he : Real.exp (Real.log 2+(n j:ℝ)*Real.log 4)=2*4^(n j) := by
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ)<4)]
  rw [← he,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The logarithmic and revealed-edge exponential errors satisfy every fixed positive tolerance eventually. -/
theorem eventually_reduction_log_exp_bounds (n : ℕ → ℕ) (p : ℕ → ℝ)
    (hvolume : Tendsto (fun j => p j*(n j:ℝ)^2) atTop atTop)
    {ω α θ : ℝ} (hω : 0<ω) (hα : 0<α) (hθ : 0<θ) :
    ∀ᶠ j in atTop, Real.log 2≤ω*(p j*(n j:ℝ)^2) ∧
      Real.exp (-α*p j*(n j:ℝ)^2)≤θ/8 := by
  have hωvol := hvolume.const_mul_atTop hω
  have hαvol := hvolume.const_mul_atTop hα
  filter_upwards [hωvol.eventually_ge_atTop (Real.log 2),
    hαvol.eventually_ge_atTop (-Real.log (θ/8))] with j hj hαj
  refine ⟨hj,?_⟩
  have hh := Real.exp_le_exp.mpr (show -α*p j*(n j:ℝ)^2≤Real.log (θ/8) by linarith)
  rwa [Real.exp_log (div_pos hθ (by norm_num))] at hh

end SparseLowerTail.Section03

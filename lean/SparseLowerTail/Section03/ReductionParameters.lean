import SparseLowerTail.Section03.ReductionSlack

/-! Simultaneous fixed tolerances for the conditioned-structure limit. -/
noncomputable section
open Set
namespace SparseLowerTail.Section03

structure ReductionParameters (r ε δ θ : ℝ) where
  α : ℝ
  γ : ℝ
  ζ : ℝ
  s : ℝ
  β : ℝ
  ω : ℝ
  alpha_mem : α∈Ioo (0:ℝ) 1
  beta_mem : β∈Ioo (0:ℝ) 1
  gamma_pos : 0<γ
  zeta_pos : 0<ζ
  omega_pos : 0<ω
  alpha_eps : α≤ε/16
  alpha_omega : α≤ω/8
  gamma_alpha : γ+2*α≤δ/2
  zeta_delta : ζ≤δ
  zeta_omega : ζ≤ω/8
  s_mem : s∈Ioo r 1
  s_cube : s^3=r^3+ζ
  scale_loss : 1-r/s≤ω/8
  beta_omega : β/ζ≤ω/8
  beta_theta : β/ζ≤θ/8
  cost_theta : ω/γ≤θ/8
  cut_theta : 384*ω/ε^2≤θ/8

/-- Every prescribed stability tolerance and probability tolerance admits all the paper's error choices simultaneously. -/
theorem exists_reduction_parameters {r ε δ θ : ℝ} (hr : r∈Ioo (0:ℝ) 1)
    (hε : ε∈Ioo (0:ℝ) 1) (hδ : 0<δ) (hθ : θ∈Ioo (0:ℝ) 1) :
    Nonempty (ReductionParameters r ε δ θ) := by
  let γ := δ/4
  have hγ : 0<γ := div_pos hδ (by norm_num)
  let ω := (θ/8)*min γ (ε^2/400)
  have hω : 0<ω := mul_pos (div_pos hθ.1 (by norm_num)) (lt_min hγ (div_pos (sq_pos_of_pos hε.1) (by norm_num)))
  have hωγ : ω≤(θ/8)*γ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith [hθ.1])
  have hωε : ω≤(θ/8)*(ε^2/400) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith [hθ.1])
  have hεsq : ε^2<1 := by nlinarith [hε.1,hε.2]
  have hθε : θ*ε^2≤θ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hεsq.le hθ.1.le
  have hω1 : ω<1 := by nlinarith [hθ.2]
  let α := min (ε/16) (min (δ/16) (ω/8))
  have hα : 0<α := lt_min (by linarith [hε.1]) (lt_min (by positivity) (by positivity))
  have hαε : α≤ε/16 := min_le_left _ _
  have hαδ : α≤δ/16 := (min_le_left _ _).trans' (min_le_right _ _)
  have hαω : α≤ω/8 := (min_le_right _ _).trans' (min_le_right _ _)
  obtain ⟨ζ,s,hζ,hsmem,hscube,hζδ,hζω,hscale⟩ := exists_reduction_cube_slack hr hδ hω
  let β := ζ*min ω θ/8
  have hβ : 0<β := div_pos (mul_pos hζ (lt_min hω hθ.1)) (by norm_num)
  have hζ1 : ζ<1 := by linarith
  have hmin : 0≤min ω θ := le_min hω.le hθ.1.le
  have hβ1 : β<1 := by
    have hh := mul_le_of_le_one_left hmin hζ1.le
    have hm : min ω θ≤ω := min_le_left _ _
    dsimp only [β]
    nlinarith
  have hratio : β/ζ=min ω θ/8 := by dsimp only [β]; field_simp [hζ.ne']
  refine ⟨⟨α,γ,ζ,s,β,ω,⟨hα,by linarith [hε.2]⟩,⟨hβ,hβ1⟩,hγ,hζ,hω,hαε,hαω,?_,hζδ,hζω,
    hsmem,hscube,hscale,?_,?_,?_,?_⟩⟩
  · dsimp only [γ]
    linarith
  · rw [hratio]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  · rw [hratio]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  · apply (div_le_iff₀ hγ).mpr
    nlinarith
  · apply (div_le_iff₀ (sq_pos_of_pos hε.1)).mpr
    nlinarith [mul_nonneg hθ.1.le (sq_nonneg ε)]

end SparseLowerTail.Section03

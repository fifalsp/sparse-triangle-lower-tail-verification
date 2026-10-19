import SparseLowerTail.Section07.PenalizedScalar

/-! The constant penalized branch: `lem:stationary`(d), including the proved
inverse construction, continuous differentiability, envelope derivative and limit. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

/-- Inverse parameter of the constant stationary equation. -/
def constantParameter (s : ℝ) : ℝ := -Real.log s/(3*s^2)

theorem constantParameter_pos {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    0 < constantParameter s := by
  have hp := hs.1
  exact div_pos (neg_pos.mpr (Real.log_neg hs.1 hs.2)) (by positivity)

theorem constantParameter_constantRoot {γ : ℝ} (hγ : 0 < γ) :
    constantParameter (constantRoot γ) = γ := by
  have h := constantRoot_spec hγ
  have he := h.2
  have hp := h.1.1
  unfold constantEquation at he
  unfold constantParameter
  apply (div_eq_iff (by positivity : 3*(constantRoot γ)^2 ≠ 0)).mpr
  linarith

theorem constantRoot_constantParameter {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    constantRoot (constantParameter s) = s := by
  symm
  apply constantRoot_unique (constantParameter_pos hs) hs.1
  unfold constantEquation constantParameter
  field_simp [ne_of_gt hs.1]
  ring

/-- A genuine order isomorphism, with the reversal dictated by the penalty. -/
def constantRootIso : Ioi (0:ℝ) ≃o (Ioo (0:ℝ) 1)ᵒᵈ where
  toEquiv :=
    { toFun := fun γ => ⟨constantRoot γ,(constantRoot_spec γ.property).1⟩
      invFun := fun s => ⟨constantParameter (OrderDual.ofDual s).val,constantParameter_pos (OrderDual.ofDual s).property⟩
      left_inv := fun γ => Subtype.ext (constantParameter_constantRoot γ.property)
      right_inv := fun s => Subtype.ext (constantRoot_constantParameter s.property) }
  map_rel_iff' := by
    intro γ η
    exact constantRoot_strictAnti.le_iff_ge η.property γ.property

theorem continuousOn_constantRoot : ContinuousOn constantRoot (Ioi (0:ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_subtype_val.comp constantRootIso.continuous

theorem hasDerivAt_constantParameter {s : ℝ} (hs : 0 < s) :
    HasDerivAt constantParameter ((2*Real.log s-1)/(3*s^3)) s := by
  have h := ((Real.hasDerivAt_log (ne_of_gt hs)).neg).div
    (((hasDerivAt_id s).pow 2).const_mul 3) (by dsimp; positivity)
  convert h using 1
  dsimp
  field_simp [ne_of_gt hs]
  ring

theorem hasDerivAt_constantRoot {γ : ℝ} (hγ : 0 < γ) :
    HasDerivAt constantRoot
      (((2*Real.log (constantRoot γ)-1)/(3*(constantRoot γ)^3))⁻¹) γ := by
  have hs := constantRoot_spec hγ
  have hsp := hs.1.1
  have hc := continuousOn_constantRoot.continuousAt (isOpen_Ioi.mem_nhds hγ)
  have hn : (2*Real.log (constantRoot γ)-1)/(3*(constantRoot γ)^3) ≠ 0 := by
    apply div_ne_zero
    · have hl := Real.log_neg hs.1.1 hs.1.2
      linarith
    · positivity
  apply (hasDerivAt_constantParameter hs.1.1).of_local_left_inverse hc hn
  filter_upwards [eventually_gt_nhds hγ] with η hη
  exact constantParameter_constantRoot hη

/-- Explicit implicit-differentiation formula, with negative denominator sign
removed. This is proved from the inverse rule, not supplied as an assumption. -/
theorem hasDerivAt_constantRoot_explicit {γ : ℝ} (hγ : 0 < γ) :
    HasDerivAt constantRoot (-3*(constantRoot γ)^3/(1+6*γ*(constantRoot γ)^2)) γ := by
  have hs := constantRoot_spec hγ
  have hsp := hs.1.1
  have he := hs.2
  unfold constantEquation at he
  have hlog : Real.log (constantRoot γ) = -3*γ*(constantRoot γ)^2 := by linarith
  convert hasDerivAt_constantRoot hγ using 1
  rw [hlog,inv_div]
  rw [show 2*(-3*γ*(constantRoot γ)^2)-1 = -(1+6*γ*(constantRoot γ)^2) by ring, div_neg]
  ring

theorem contDiffOn_constantRoot : ContDiffOn ℝ 1 constantRoot (Ioi (0:ℝ)) := by
  have hc := continuousOn_constantRoot
  have hd : ContinuousOn (fun γ => -3*(constantRoot γ)^3/(1+6*γ*(constantRoot γ)^2))
      (Ioi (0:ℝ)) := by
    apply ContinuousOn.div (continuousOn_const.mul (hc.pow 3))
      (continuousOn_const.add ((continuousOn_const.mul continuousOn_id).mul (hc.pow 2)))
    intro γ hγ
    have hg : 0 < γ := hγ
    positivity
  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun γ hγ => (hasDerivAt_constantRoot hγ).differentiableAt.differentiableWithinAt,?_,?_⟩
  · simp
  · rw [contDiffOn_zero]
    exact hd.congr (fun γ hγ => (hasDerivAt_constantRoot_explicit hγ).deriv)

/-- The constant stationary edge density vanishes at infinite penalty. -/
theorem tendsto_constantRoot_atTop : Tendsto constantRoot atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℝ)] with γ hγ
    exact ha.trans (constantRoot_spec hγ).1.1
  · intro b hb
    let s : ℝ := min (b/2) (1/2)
    have hs : s ∈ Ioo (0:ℝ) 1 := by
      constructor
      · exact lt_min (by linarith) (by norm_num)
      · exact (min_le_right _ _).trans_lt (by norm_num)
    have hsb : s < b := (min_le_left _ _).trans_lt (by linarith)
    filter_upwards [eventually_gt_atTop (constantParameter s)] with γ hγ
    have hg : 0 < γ := (constantParameter_pos hs).trans hγ
    have hh := constantRoot_strictAnti (constantParameter_pos hs) hg hγ
    rw [constantRoot_constantParameter hs] at hh
    exact hh.trans hsb

/-- The minimum constant-pair penalty `C₀(γ)`. -/
def constantMinimum (γ : ℝ) : ℝ := constantPenalty γ (constantRoot γ)

theorem hasDerivAt_constantMinimum {γ : ℝ} (hγ : 0 < γ) :
    HasDerivAt constantMinimum ((constantRoot γ)^3) γ := by
  have hs := constantRoot_spec hγ
  have hsp := hs.1.1
  have hd := hasDerivAt_constantRoot_explicit hγ
  have h := (((hasDerivAt_entropy (ne_of_gt hs.1.1)).comp γ hd).add
    ((hasDerivAt_id γ).mul (hd.pow 3)))
  convert h using 1
  dsimp
  have he := hs.2
  unfold constantEquation at he
  nlinarith [congrArg (fun x : ℝ =>
    x*(-3*(constantRoot γ)^3/(1+6*γ*(constantRoot γ)^2))) he]

theorem contDiffOn_constantMinimum : ContDiffOn ℝ 1 constantMinimum (Ioi (0:ℝ)) := by
  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun γ hγ => (hasDerivAt_constantMinimum hγ).differentiableAt.differentiableWithinAt,?_,?_⟩
  · simp
  · rw [contDiffOn_zero]
    exact (continuousOn_constantRoot.pow 3).congr
      (fun γ hγ => (hasDerivAt_constantMinimum hγ).deriv)

theorem constantMinimum_eq {γ : ℝ} (hγ : 0 < γ) :
    constantMinimum γ = (2*entropy (constantRoot γ)+1-constantRoot γ)/3 := by
  have he := (constantRoot_spec hγ).2
  unfold constantEquation at he
  unfold constantMinimum constantPenalty entropy
  nlinarith [congrArg (fun x : ℝ => constantRoot γ*x) he]

theorem tendsto_constantMinimum_atTop : Tendsto constantMinimum atTop (𝓝 1) := by
  have h := (((continuous_entropy.tendsto 0).comp tendsto_constantRoot_atTop).const_mul 2
    |>.add_const 1).sub tendsto_constantRoot_atTop |>.div_const 3
  have he : constantMinimum =ᶠ[atTop] (fun γ =>
      (2*entropy (constantRoot γ)+1-constantRoot γ)/3) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with γ hγ
    exact constantMinimum_eq hγ
  have ht : Tendsto (fun γ => (2*entropy (constantRoot γ)+1-constantRoot γ)/3) atTop (𝓝 1) := by
    norm_num at h ⊢
    exact h
  exact ht.congr' he.symm

end SparseLowerTail.Section07

import SparseLowerTail.Section02.MeanGap
import SparseLowerTail.Section04.Rescaling

/-! Downward propagation of strict improvement, manuscript lem:push. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section02

/-- Scaling by a number in [0,1] preserves the graphon range. -/
def scaledGraphon (U : Graphon) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) : Graphon where
  toFun := fun p => c*U p
  measurable := U.measurable.const_mul c
  symmetric := U.symmetric.mono fun _ h => congrArg (fun t => c*t) h
  bounded := by
    filter_upwards [U.bounded] with p hp
    exact ⟨mul_nonneg hc.1 hp.1, by nlinarith [mul_le_mul hc.2 hp.2 hp.1 (by norm_num : (0:ℝ)≤1)]⟩

theorem triangle_scaledGraphon (U : Graphon) (c : ℝ) (hc : c ∈ Icc (0:ℝ) 1) :
    triangle (scaledGraphon U c hc) = c^3*triangle U := by
  exact NonnegativeKernel.triangle_scale (NonnegativeKernel.ofGraphon U) c hc.1

theorem cost_scaledGraphon_sub_entropy (U : Graphon) (c s : ℝ)
    (hc : c ∈ Icc (0:ℝ) 1) (hcp : 0 < c) (hs : 0 ≤ s) :
    cost (scaledGraphon U c hc)-entropy (c*s) =
      c*(cost U-entropy s)+(c*Real.log c)*(edgeDensity U-s) := by
  exact NonnegativeKernel.cost_scale_sub_entropy (NonnegativeKernel.ofGraphon U) c s hcp hs

/-- Full graphon conclusion of lem:push for the literal scalar multiple W. -/
theorem push_graphon {r r' : ℝ} {U : Graphon} (hr' : 0 < r') (hrr : r' < r) (hr1 : r < 1)
    (hf : Feasible r U) (hc : cost U ≤ entropy r) (hn : ¬∃ c, IsConstant U c) :
    let ha : r'/r ∈ Icc (0:ℝ) 1 :=
      ⟨(div_pos hr' (hr'.trans hrr)).le, ((div_lt_one (hr'.trans hrr)).mpr hrr).le⟩
    Feasible r' (scaledGraphon U (r'/r) ha) ∧
      cost (scaledGraphon U (r'/r) ha) < entropy r' := by
  dsimp
  have hr : 0 < r := hr'.trans hrr
  have hcp : 0 < r'/r := div_pos hr' hr
  have hc1 : r'/r < 1 := (div_lt_one hr).mpr hrr
  have hscale : r'/r*r = r' := div_mul_cancel₀ _ hr.ne'
  constructor
  · change triangle _ ≤ r'^3
    rw [triangle_scaledGraphon]
    calc
      (r'/r)^3*triangle U ≤ (r'/r)^3*r^3 := mul_le_mul_of_nonneg_left hf (pow_nonneg hcp.le _)
      _ = r'^3 := by rw [← mul_pow, hscale]
  · have hid := cost_scaledGraphon_sub_entropy U (r'/r) r ⟨hcp.le, hc1.le⟩ hcp hr.le
    rw [hscale] at hid
    have hmean := edgeDensity_gt_target ⟨hr, hr1⟩ hc hn
    have hfirst : (r'/r)*(cost U-entropy r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcp.le (sub_nonpos.mpr hc)
    have hsecond : (r'/r*Real.log (r'/r))*(edgeDensity U-r) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hcp (Real.log_neg hcp hc1)) (sub_pos.mpr hmean)
    linarith

/-- The variational consequence in lem:push. -/
theorem push_value {r r' : ℝ} {U : Graphon} (hr' : 0 < r') (hrr : r' < r) (hr1 : r < 1)
    (hf : Feasible r U) (hc : cost U ≤ entropy r) (hn : ¬∃ c, IsConstant U c) :
    value r' < entropy r' := by
  obtain ⟨hfeas, hcost⟩ := push_graphon hr' hrr hr1 hf hc hn
  exact (value_le_cost hfeas).trans_lt hcost

end SparseLowerTail.Section02

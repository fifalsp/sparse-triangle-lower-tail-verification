import SparseLowerTail.Section04.EntropyGeometry
import SparseLowerTail.Triangle

/-!
# Activity of the triangle constraint

Stable manuscript anchor: `lem:active` (and the positivity assertion of
`lem:existence`). The proof follows the paper's perturbation toward one.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace SparseLowerTail.Section04

theorem entropy_eq_zero_iff {x : ℝ} (hx : x ∈ Icc 0 1) : entropy x = 0 ↔ x = 1 := by
  constructor
  · intro heq
    apply strictAntiOn_entropy.injOn hx (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    simpa using heq
  · rintro rfl
    simp

/-- Entropy zero characterizes the all-one graphon up to null sets. -/
theorem cost_eq_zero_iff (U : Graphon) : cost U = 0 ↔ IsConstant U 1 := by
  have hn : 0 ≤ᵐ[squareMeasure] fun p => entropy (U p) := by
    filter_upwards [U.bounded] with p hp
    exact entropy_nonneg hp.1
  rw [cost, integral_eq_zero_iff_of_nonneg_ae hn (cost_integrable U)]
  constructor
  · intro h
    filter_upwards [U.bounded, h] with p hp he
    exact (entropy_eq_zero_iff hp).mp he
  · intro h
    filter_upwards [h] with p hp
    simp [hp]

/-- The strictly positive cost used in `lem:active` holds for every feasible graphon. -/
theorem cost_pos_of_feasible {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hf : Feasible r U) : 0 < cost U := by
  apply lt_of_le_of_ne (cost_nonneg U)
  intro heq
  have he := (cost_eq_zero_iff U).mp heq.symm
  have ht : triangle U = 1 := by
    have h := triangle_congr_ae (U := U)
      (W := constant 1 (by norm_num)) he
    simpa using h
  have hr3 := pow_lt_one₀ hr.1.le hr.2 (by decide : 3 ≠ 0)
  unfold Feasible at hf
  linarith

/-- The graphon path `(1-s)U+s`, for interpolation parameters in `[0,1]`. -/
def towardOneGraphon (U : Graphon) (s : ℝ) (hs : s ∈ Icc 0 1) : Graphon where
  toFun := fun p => towardOne s (U p)
  measurable := ((aemeasurable_const.mul U.measurable).add aemeasurable_const)
  symmetric := by
    filter_upwards [U.symmetric] with p hp
    rw [hp]
  bounded := by
    filter_upwards [U.bounded] with p hp
    exact towardOne_mem hs hp

/-- Pointwise convexity estimate used by `lem:active`. -/
theorem entropy_towardOne_le {s x : ℝ} (hs : s ∈ Icc 0 1) (hx : 0 ≤ x) :
    entropy (towardOne s x) ≤ (1 - s) * entropy x := by
  have h := strictConvexOn_entropy.convexOn.2 hx (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (sub_nonneg.mpr hs.2) hs.1 (show 1 - s + s = 1 by ring)
  simpa [towardOne, smul_eq_mul] using h

/-- Cost contracts by at least `1-s` along the perturbation toward one. -/
theorem cost_towardOne_le (U : Graphon) {s : ℝ} (hs : s ∈ Icc 0 1) :
    cost (towardOneGraphon U s hs) ≤ (1 - s) * cost U := by
  have hm : cost (towardOneGraphon U s hs) ≤
      ∫ p, (1 - s) * entropy (U p) ∂squareMeasure := by
    apply integral_mono_ae (cost_integrable _) ((cost_integrable U).const_mul (1 - s))
    filter_upwards [U.bounded] with p hp
    exact entropy_towardOne_le hs hp.1
  simpa [integral_const_mul, cost] using hm

private theorem product_increase_le {a b a' b' : ℝ}
    (ha : a ∈ Icc 0 1) (hb' : b' ∈ Icc 0 1) (haa : a ≤ a') (hbb : b ≤ b') :
    a' * b' - a * b ≤ (a' - a) + (b' - b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr haa) (sub_nonneg.mpr hb'.2),
    mul_nonneg (sub_nonneg.mpr hbb) (sub_nonneg.mpr ha.2)]

private theorem triple_towardOne_le {s x y z : ℝ} (hs : s ∈ Icc 0 1)
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) (hz : z ∈ Icc 0 1) :
    towardOne s x * towardOne s y * towardOne s z ≤ x * y * z + 3 * s := by
  have hx' := towardOne_mem hs hx
  have hy' := towardOne_mem hs hy
  have hz' := towardOne_mem hs hz
  have hxx := le_towardOne hs.1 hx.2
  have hyy := le_towardOne hs.1 hy.2
  have hzz := le_towardOne hs.1 hz.2
  have hxy : x * y ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hx.1 hy.1, by nlinarith [mul_le_mul hx.2 hy.2 hy.1 (by norm_num : (0 : ℝ) ≤ 1)]⟩
  have hprod : x * y ≤ towardOne s x * towardOne s y :=
    mul_le_mul hxx hyy hy.1 hx'.1
  have h₁ := product_increase_le hx hy' hxx hyy
  have h₂ := product_increase_le hxy hz' hprod hzz
  have hxs : towardOne s x - x ≤ s := by unfold towardOne; nlinarith [mul_nonneg hs.1 hx.1]
  have hys : towardOne s y - y ≤ s := by unfold towardOne; nlinarith [mul_nonneg hs.1 hy.1]
  have hzs : towardOne s z - z ≤ s := by unfold towardOne; nlinarith [mul_nonneg hs.1 hz.1]
  linarith

private theorem active_edge12_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.1))
      cubeMeasure squareMeasure :=
  QuasiMeasurePreserving.prodMap
    (QuasiMeasurePreserving.id unitMeasure) quasiMeasurePreserving_fst

private theorem active_edge23_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.2.1, p.2.2))
      cubeMeasure squareMeasure := quasiMeasurePreserving_snd

private theorem active_edge13_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.2))
      cubeMeasure squareMeasure :=
  QuasiMeasurePreserving.prodMap
    (QuasiMeasurePreserving.id unitMeasure) quasiMeasurePreserving_snd

/-- An explicit bound supplies the small-perturbation continuity step in `lem:active`.
The paper uses polynomial continuity; the bound is stronger and avoids assuming it. -/
theorem triangle_towardOne_le (U : Graphon) {s : ℝ} (hs : s ∈ Icc 0 1) :
    triangle (towardOneGraphon U s hs) ≤ triangle U + 3 * s := by
  have hi := (triangle_integrable U).add (integrable_const (3 * s))
  have hm : triangle (towardOneGraphon U s hs) ≤
      ∫ p : ℝ × (ℝ × ℝ),
        U (p.1, p.2.1) * U (p.2.1, p.2.2) * U (p.1, p.2.2) + 3 * s ∂cubeMeasure := by
    apply integral_mono_ae (triangle_integrable _) hi
    filter_upwards [active_edge12_qmp.ae U.bounded, active_edge23_qmp.ae U.bounded,
      active_edge13_qmp.ae U.bounded] with p h12 h23 h13
    exact triple_towardOne_le hs h12 h23 h13
  simpa [integral_add (triangle_integrable U) (integrable_const (3 * s)), triangle] using hm

/-- Stable manuscript anchor `lem:active`: every minimizer saturates the triangle
constraint. This is a theorem for arbitrary graphons, with no external hypotheses. -/
theorem minimizer_triangle_eq {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hmin : IsMinimizer r U) : triangle U = r ^ 3 := by
  apply le_antisymm hmin.1
  by_contra hn
  have hgap : 0 < r ^ 3 - triangle U := by linarith
  let s : ℝ := min (1 / 2) ((r ^ 3 - triangle U) / 6)
  have hsp : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hsp.le, hs1⟩
  have hsgap : 3 * s < r ^ 3 - triangle U := by
    have h := min_le_right (1 / 2 : ℝ) ((r ^ 3 - triangle U) / 6)
    change s ≤ (r ^ 3 - triangle U) / 6 at h
    linarith
  have hf : Feasible r (towardOneGraphon U s hs) := by
    unfold Feasible
    have ht := triangle_towardOne_le U hs
    linarith
  have hp := cost_pos_of_feasible hr hmin.1
  have hc := cost_towardOne_le U hs
  have hm := hmin.2 _ hf
  nlinarith [mul_pos hsp hp]

end SparseLowerTail.Section04

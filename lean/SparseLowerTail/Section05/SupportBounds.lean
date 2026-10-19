import SparseLowerTail.Section04.VertexIdentity
import SparseLowerTail.Section02.Goodman
import SparseLowerTail.Section02.MeanGap

/-!
# The sharp support bound from vertex stationarity

Stable manuscript anchors: `lem:support`, `cor:identities`, `eq:Lambda`.
The scalar bound on vertex entropy uses only `u log u ≤ 0` and `u² ≤ u`.
The codegree estimate integrates `2ab ≤ a²+b²`, which yields the same
constant as Cauchy--Schwarz and avoids square-root bookkeeping.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace SparseLowerTail.Section05
open Section04

/-- The support exponent Q expressed in triangle density, mean, and cost. -/
def supportExponent (t m F : ℝ) : ℝ := ((1-F)^2-m^2)/(2*t)

/-- The function Λ from `eq:Lambda`. -/
def supportLambda (t m F : ℝ) : ℝ := Real.exp (-supportExponent t m F)

/-- Squared L² norm of a graphon row. -/
def rowSquare (U : Graphon) (x : ℝ) : ℝ := ∫ y, U (x,y)^2 ∂unitMeasure

/-- The common upper bound on row squares and codegrees. -/
def supportCodegreeBound (U : Graphon) (r : ℝ) : ℝ := (2-vertexMean U r)/2

theorem vertexEntropy_le_two_sub_two_sq {u : ℝ} (hu : u ∈ Icc 0 1) :
    vertexEntropy u ≤ 2-2*u^2 := by
  have hlog := Real.log_nonpos hu.1 hu.2
  have hmul := mul_nonpos_of_nonneg_of_nonpos hu.1 hlog
  have hsq : u^2 ≤ u := by nlinarith [hu.1,hu.2]
  unfold vertexEntropy
  nlinarith

theorem graphon_square_bounded (U : Graphon) :
    BoundedObservable squareMeasure (fun p => U p^2) := by
  simpa only [pow_two] using (graphon_boundedObservable U).mul (graphon_boundedObservable U)

theorem graphon_vertexEntropy_bounded (U : Graphon) :
    BoundedObservable squareMeasure (fun p => vertexEntropy (U p)) := by
  have h := ((graphon_mulLog_boundedObservable U).add
    ((graphon_boundedObservable U).const_mul (-2))).add (BoundedObservable.const 2)
  convert h using 1
  funext p
  unfold vertexEntropy
  ring

/-- The row L² estimate in `lem:support`. -/
theorem minimizer_rowSquare_le (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, rowSquare U x ≤ supportCodegreeBound U r := by
  have hsq := (graphon_square_bounded U).integrable.prod_right_ae
  have hk := (graphon_vertexEntropy_bounded U).integrable.prod_right_ae
  have hb := Measure.ae_ae_of_ae_prod U.bounded
  filter_upwards [hsq, hk, hb, minimizer_vertex_stationary hSampling hr hU,
    minimizer_row_vertexEntropy hr hU] with x hxs hxk hxb hstat hrow
  have hi : Integrable (fun y => 2-2*U (x,y)^2) unitMeasure :=
    (integrable_const 2).sub (hxs.const_mul 2)
  have hm := integral_mono_ae hxk hi (hxb.mono fun y hy => vertexEntropy_le_two_sub_two_sq hy)
  rw [integral_sub (integrable_const 2) (hxs.const_mul 2), integral_const_mul] at hm
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hm
  rw [hrow, hstat] at hm
  change rowSquare U x ≤ (2-vertexMean U r)/2
  change vertexMean U r ≤ 2-2*rowSquare U x at hm
  linarith

/-- Codegrees inherit the uniform row-square bound. -/
theorem codegree_le_of_rowSquare_le {U : Graphon} {K : ℝ}
    (hK : ∀ᵐ x ∂unitMeasure, rowSquare U x ≤ K) :
    ∀ᵐ p ∂squareMeasure, codegree U p.1 p.2 ≤ K := by
  have hsq := (graphon_square_bounded U).integrable.prod_right_ae
  have hip := ((TriangleIntegration.boundedZ U).mul (TriangleIntegration.boundedY U)).integrable.prod_right_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hK,
    Measure.quasiMeasurePreserving_snd.ae hK,
    Measure.quasiMeasurePreserving_fst.ae hsq,
    Measure.quasiMeasurePreserving_snd.ae hsq, hip] with p hp hq hip₁ hip₂ hiprod
  have hir : Integrable (fun z => U (p.1,z)^2+U (p.2,z)^2) unitMeasure := hip₁.add hip₂
  have hm := integral_mono_ae (hiprod.const_mul 2) hir (Eventually.of_forall fun z => by
    change 2*(U (p.1,z)*U (p.2,z)) ≤ U (p.1,z)^2+U (p.2,z)^2
    nlinarith [sq_nonneg (U (p.1,z)-U (p.2,z))])
  rw [integral_const_mul, integral_add hip₁ hip₂] at hm
  change 2*codegree U p.1 p.2 ≤ rowSquare U p.1+rowSquare U p.2 at hm
  linarith

/-- The sharp codegree bound in `lem:support`. -/
theorem minimizer_codegree_le (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, codegree U p.1 p.2 ≤ supportCodegreeBound U r :=
  codegree_le_of_rowSquare_le (minimizer_rowSquare_le hSampling hr hU)

/-- The sharp lower support bound in `lem:support`. -/
theorem minimizer_support_lower (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, Real.exp (-graphonMultiplier U r*supportCodegreeBound U r) ≤ U p := by
  have hμ := minimizer_multiplier_pos hr hU
  filter_upwards [minimizer_exp_equation hr hU, minimizer_codegree_le hSampling hr hU] with p he hc
  rw [he]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr hμ.le)

/-- The explicit codegree bound from `cor:identities`(b). -/
theorem supportCodegreeBound_eq {r : ℝ} (hr : r ≠ 0) (U : Graphon) :
    supportCodegreeBound U r = (1-cost U+edgeDensity U)/2 := by
  unfold supportCodegreeBound
  rw [vertexMean_eq hr]
  ring

/-- The exponent is exactly Q, rather than an assumed numerical estimate. -/
theorem multiplier_mul_supportCodegreeBound {r : ℝ} (hr : r ≠ 0) (U : Graphon) :
    graphonMultiplier U r*supportCodegreeBound U r =
      supportExponent (r^3) (edgeDensity U) (cost U) := by
  rw [supportCodegreeBound_eq hr]
  unfold graphonMultiplier supportExponent
  ring

/-- The parameter-form lower support bound `cor:identities`(c). -/
theorem minimizer_supportLambda_lower (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, supportLambda (r^3) (edgeDensity U) (cost U) ≤ U p := by
  have h := minimizer_support_lower hSampling hr hU
  have he := multiplier_mul_supportCodegreeBound (ne_of_gt hr.1) U
  simpa only [neg_mul, he, supportLambda] using h

/-- Integrating the support bound gives Λ≤m. -/
theorem minimizer_supportLambda_le_mean (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    supportLambda (r^3) (edgeDensity U) (cost U) ≤ edgeDensity U := by
  have h := integral_mono_ae (integrable_const (supportLambda (r^3) (edgeDensity U) (cost U)))
    (graphon_integrable U) (minimizer_supportLambda_lower hSampling hr hU)
  simpa [edgeDensity] using h

/-- Coordinatewise monotonicity in `cor:identities`(d). -/
theorem supportLambda_mono {t m₀ m₁ F₀ F₁ : ℝ} (ht : 0 < t)
    (hm₀ : 0 ≤ m₀) (hm : m₀ ≤ m₁) (hF : F₀ ≤ F₁) (hF₁ : F₁ ≤ 1) :
    supportLambda t m₀ F₀ ≤ supportLambda t m₁ F₁ := by
  apply Real.exp_le_exp.mpr
  unfold supportExponent
  apply neg_le_neg
  apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) ht)).mpr
  have hmSq : m₀^2 ≤ m₁^2 := by nlinarith
  have hFSq : (1-F₁)^2 ≤ (1-F₀)^2 := by nlinarith
  linarith

theorem supportLambda_strictMono_mean {t F : ℝ} (ht : 0 < t) :
    StrictMonoOn (fun m => supportLambda t m F) (Ici 0) := by
  intro a ha b hb hab
  apply Real.exp_lt_exp.mpr
  unfold supportExponent
  apply neg_lt_neg
  apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) ht)).mpr
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  nlinarith

theorem supportLambda_strictMono_cost {t m : ℝ} (ht : 0 < t) :
    StrictMonoOn (fun F => supportLambda t m F) (Iic 1) := by
  intro a ha b hb hab
  apply Real.exp_lt_exp.mpr
  unfold supportExponent
  apply neg_lt_neg
  apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num) ht)).mpr
  change a ≤ 1 at ha
  change b ≤ 1 at hb
  nlinarith

/-- First cost comparison from `cor:identities`(a). -/
theorem minimizer_cost_le_entropy {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : cost U ≤ entropy r := by
  have h := hU.2 (constant r ⟨hr.1.le,hr.2.le⟩) (by simp [Feasible])
  simpa using h

theorem minimizer_cost_bounds {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : 0 < cost U ∧ cost U ≤ entropy r ∧ entropy r < 1 := by
  refine ⟨cost_pos_of_feasible hr hU.1, minimizer_cost_le_entropy hr hU, ?_⟩
  have h := strictAntiOn_entropy (show (0:ℝ) ∈ Icc 0 1 by norm_num)
    ⟨hr.1.le,hr.2.le⟩ hr.1
  simpa using h

theorem minimizer_mean_add_cost_lt_one {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : edgeDensity U+cost U < 1 := by
  have h := graphonMultiplier_integral_identity (U := U) (ne_of_gt hr.1)
  rw [integral_mulLog_identity] at h
  have hp := mul_pos (minimizer_multiplier_pos hr hU) (pow_pos hr.1 3)
  linarith

/-- The mean lies between the target and the explicit Goodman bound. -/
theorem minimizer_mean_bounds {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) :
    r ≤ edgeDensity U ∧ edgeDensity U ≤ (1+Real.sqrt (1+8*r^3))/4 := by
  have hcost := minimizer_cost_le_entropy hr hU
  refine ⟨?_, ?_⟩
  · by_cases hc : ∃ c, IsConstant U c
    · obtain ⟨c,hc⟩ := hc
      have he := Section02.constant_of_cost_le_target hr hc hU.1 hcost
      subst c
      have hm := edgeDensity_congr_ae (U := U) (W := constant r ⟨hr.1.le,hr.2.le⟩) hc
      simpa [edgeDensity,constant] using hm.ge
    · exact (Section02.edgeDensity_gt_target hr hcost hc).le
  · simpa only [minimizer_triangle_eq hr hU] using Section02.goodman_mean_bound U

theorem minimizer_mean_eq_target_iff {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : edgeDensity U = r ↔ IsConstant U r := by
  constructor
  · intro he
    by_contra hn
    have hnc : ¬∃ c, IsConstant U c := by
      rintro ⟨c,hc⟩
      have hcval := Section02.constant_of_cost_le_target hr hc hU.1 (minimizer_cost_le_entropy hr hU)
      exact hn (hcval ▸ hc)
    have hgt := Section02.edgeDensity_gt_target hr (minimizer_cost_le_entropy hr hU) hnc
    linarith
  · intro hc
    have hm := edgeDensity_congr_ae (U := U) (W := constant r ⟨hr.1.le,hr.2.le⟩) hc
    simpa [edgeDensity,constant] using hm


/-- Positivity of Q on the parameter domain Π. -/
theorem supportExponent_pos {t m F : ℝ} (ht : 0 < t)
    (hm : 0 < m) (hPi : m+F < 1) : 0 < supportExponent t m F := by
  unfold supportExponent
  apply div_pos _ (mul_pos (by norm_num) ht)
  nlinarith

/-- The support parameter lies strictly between zero and one on Π. -/
theorem supportLambda_mem_Ioo {t m F : ℝ} (ht : 0 < t)
    (hm : 0 < m) (hPi : m+F < 1) : supportLambda t m F ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (supportExponent_pos ht hm hPi))

/-- Every minimizer yields admissible parameters for the triangle-law relaxation. -/
theorem minimizer_parameter_domain {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : 0 < edgeDensity U ∧ edgeDensity U+cost U < 1 :=
  ⟨hr.1.trans_le (minimizer_mean_bounds hr hU).1, minimizer_mean_add_cost_lt_one hr hU⟩

/-- Bridge to an interval-certified cell upper bound on Q. -/
theorem minimizer_support_lower_of_exponent_le (hSampling : UniformSampling) {r Q : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U)
    (hQ : supportExponent (r^3) (edgeDensity U) (cost U) ≤ Q) :
    ∀ᵐ p ∂squareMeasure, Real.exp (-Q) ≤ U p := by
  filter_upwards [minimizer_supportLambda_lower hSampling hr hU] with p hp
  exact (Real.exp_le_exp.mpr (neg_le_neg hQ)).trans hp

end SparseLowerTail.Section05

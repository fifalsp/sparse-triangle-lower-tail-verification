import SparseLowerTail.Section04.Rescaling
import SparseLowerTail.Section08.GraphonIntegration
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Euler--Lagrange equation and quantitative bounds

Stable manuscript anchor: `prop:euler`. Positivity uses the same entropy
singularity and restoration of the triangle constraint as the paper. The
perturbation is `(1-s)U+s`; the already proved `3s` triangle bound replaces
the paper's support-sensitive expansion. This changes no conclusion.

For the Euler equation, bounded multiplicative perturbations `U * exp(s * D)`
replace the manuscript's cutoff-supported additive perturbations. The entropy
scaling identity, dominated differentiation, and cyclic symmetry give their
first derivatives. Testing with the bounded weighted Euler residual proves
the equation almost everywhere. All four parts of `prop:euler`, including
multiplier uniqueness, are proved from the minimizer hypothesis; none of
these variational conclusions are assumptions.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace SparseLowerTail.Section04

/-- Indicator of the zero set of a graphon representative. -/
def zeroIndicator (U : Graphon) (p : ℝ × ℝ) : ℝ := if U p = 0 then 1 else 0

def zeroMass (U : Graphon) : ℝ := ∫ p, zeroIndicator U p ∂squareMeasure

theorem zeroIndicator_nonneg (U : Graphon) (p : ℝ × ℝ) : 0 ≤ zeroIndicator U p := by
  unfold zeroIndicator
  split <;> norm_num

theorem zeroIndicator_integrable (U : Graphon) : Integrable (zeroIndicator U) squareMeasure := by
  have hZ : NullMeasurableSet {p | U p = 0} squareMeasure := by
    simpa using U.measurable.nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ))
  have hm : AEMeasurable (zeroIndicator U) squareMeasure :=
    aemeasurable_const.indicator₀ hZ
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall (fun p => by unfold zeroIndicator; split <;> norm_num)

theorem zeroMass_nonneg (U : Graphon) : 0 ≤ zeroMass U :=
  integral_nonneg (zeroIndicator_nonneg U)

theorem zeroMass_zero_iff (U : Graphon) : zeroMass U = 0 ↔ ∀ᵐ p ∂squareMeasure, 0 < U p := by
  rw [zeroMass, integral_eq_zero_iff_of_nonneg (zeroIndicator_nonneg U) (zeroIndicator_integrable U)]
  constructor
  · intro hz
    filter_upwards [hz, U.bounded] with p hp hu
    have hn : U p ≠ 0 := by
      intro he
      simp [zeroIndicator, he] at hp
    exact lt_of_le_of_ne hu.1 (Ne.symm hn)
  · intro hp
    filter_upwards [hp] with p hu
    simp [zeroIndicator, ne_of_gt hu]

/-- Convexity with the exact extra entropy saving on the zero set. -/
theorem entropy_towardOne_zero_saving {s x : ℝ} (hs : s ∈ Icc 0 1) (hx : 0 ≤ x) :
    entropy (towardOne s x) ≤ (1-s) * entropy x +
      (s * Real.log s) * (if x = 0 then 1 else 0) := by
  by_cases hz : x = 0
  · subst x
    simp [towardOne, entropy]
    ring_nf
    exact le_rfl
  · simpa [hz] using entropy_towardOne_le hs hx

/-- The integrated zero-set saving driving `prop:euler`(a). -/
theorem cost_towardOne_zero_saving (U : Graphon) {s : ℝ} (hs : s ∈ Icc 0 1) :
    cost (towardOneGraphon U s hs) ≤ (1-s) * cost U + (s * Real.log s) * zeroMass U := by
  have h₁ : Integrable (fun p => (1-s) * entropy (U p)) squareMeasure :=
    (cost_integrable U).const_mul (1-s)
  have h₂ : Integrable (fun p => (s * Real.log s) * zeroIndicator U p) squareMeasure :=
    (zeroIndicator_integrable U).const_mul (s * Real.log s)
  have h := integral_mono_ae (cost_integrable (towardOneGraphon U s hs)) (h₁.add h₂) (by
    filter_upwards [U.bounded] with p hp
    exact entropy_towardOne_zero_saving hs hp.1)
  simp only [Pi.add_apply] at h
  simpa only [cost, integral_add h₁ h₂, integral_const_mul, zeroMass] using h

/-- Interpolating toward one can only increase triangle density. -/
theorem triangle_le_towardOne (U : Graphon) {s : ℝ} (hs : s ∈ Icc 0 1) :
    triangle U ≤ triangle (towardOneGraphon U s hs) := by
  apply integral_mono_ae (triangle_integrable U) (triangle_integrable _)
  filter_upwards [NonnegativeKernel.edge12_qmp.ae U.bounded,
    NonnegativeKernel.edge23_qmp.ae U.bounded,
    NonnegativeKernel.edge13_qmp.ae U.bounded] with p h12 h23 h13
  have i12 := le_towardOne hs.1 h12.2
  have i23 := le_towardOne hs.1 h23.2
  have i13 := le_towardOne hs.1 h13.2
  exact mul_le_mul (mul_le_mul i12 i23 h23.1 (towardOne_mem hs h12).1) i13 h13.1
    (mul_nonneg (towardOne_mem hs h12).1 (towardOne_mem hs h23).1)

/-- Scaling a graphon down costs at most the additive loss of scale. -/
theorem scaledGraphon_cost_le (U : Graphon) {c : ℝ} (hc : c ∈ Ioc 0 1) :
    ((NonnegativeKernel.ofGraphon U).scale c hc.1.le).cost ≤ cost U + 1 - c := by
  rw [NonnegativeKernel.cost_scale _ _ hc.1, NonnegativeKernel.cost_ofGraphon,
    NonnegativeKernel.edgeDensity_ofGraphon]
  have he : 0 ≤ edgeDensity U := by
    apply integral_nonneg_of_ae
    exact U.bounded.mono fun _ h => h.1
  have hl : c * Real.log c ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc.1.le (Real.log_nonpos hc.1.le hc.2)
  have hprod := mul_nonpos_of_nonpos_of_nonneg hl he
  have hcost := mul_le_mul_of_nonneg_right hc.2 (cost_nonneg U)
  nlinarith

/-- Quantitative control of the scale loss; a coarse linear bound suffices. -/
theorem normalizingScale_bounds {r t d : ℝ} (hr : 0 < r)
    (ht : r ^ 3 ≤ t) (hd : t ≤ r ^ 3 + d) :
    normalizingScale r t ∈ Ioc (0 : ℝ) 1 ∧ 1 - normalizingScale r t ≤ d / r ^ 3 := by
  have hr3 : 0 < r ^ 3 := pow_pos hr _
  have htp : 0 < t := hr3.trans_le ht
  have hp := normalizingScale_pos hr htp
  have hcube := normalizingScale_cube hr htp
  have hle : normalizingScale r t ≤ 1 := by
    apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [hcube, one_pow]
    exact (div_le_one htp).mpr ht
  have hcub_le : normalizingScale r t ^ 3 ≤ normalizingScale r t := by
    have hsq : normalizingScale r t ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hp.le]
  have hscaled : (1-normalizingScale r t) * t ≤ t-r^3 := by
    rw [hcube] at hcub_le
    have h := (div_le_iff₀ htp).mp hcub_le
    linarith
  have hmul := mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hle)
  refine ⟨⟨hp, hle⟩, (le_div_iff₀ hr3).mpr ?_⟩
  nlinarith

/-- `prop:euler`(a): an optimizer cannot vanish on a set of positive measure. -/
theorem minimizer_pos_ae {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : ∀ᵐ p ∂squareMeasure, 0 < U p := by
  apply (zeroMass_zero_iff U).mp
  by_contra hn
  have hζ : 0 < zeroMass U := lt_of_le_of_ne (zeroMass_nonneg U) (Ne.symm hn)
  let s : ℝ := Real.exp (-(4 / (zeroMass U * r ^ 3)))
  have hden : 0 < zeroMass U * r ^ 3 := mul_pos hζ (pow_pos hr.1 _)
  have hsp : 0 < s := Real.exp_pos _
  have hs1 : s < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (div_pos (by norm_num) hden)
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hsp.le, hs1.le⟩
  have hlog : Real.log s = -(4 / (zeroMass U * r ^ 3)) := Real.log_exp _
  have hcoeff : zeroMass U * Real.log s + 3 / r ^ 3 < 0 := by
    rw [hlog]
    have hid : zeroMass U * -(4 / (zeroMass U * r ^ 3)) + 3 / r ^ 3 = -(1 / r ^ 3) := by
      field_simp [ne_of_gt hζ, ne_of_gt hr.1]
      ring
    rw [hid]
    exact neg_neg_of_pos (one_div_pos.mpr (pow_pos hr.1 _))
  let V := towardOneGraphon U s hs
  have htU := minimizer_triangle_eq hr hU
  have htlo : r ^ 3 ≤ triangle V := by rw [← htU]; exact triangle_le_towardOne U hs
  have hthi : triangle V ≤ r ^ 3 + 3 * s := by rw [← htU]; exact triangle_towardOne_le U hs
  have htp : 0 < triangle V := (pow_pos hr.1 3).trans_le htlo
  have hl := normalizingScale_bounds hr.1 htlo hthi
  have hmin := NonnegativeKernel.minimizer_cost_le hU
    ((NonnegativeKernel.ofGraphon V).scale (normalizingScale r (triangle V)) hl.1.1.le)
    (triangle_normalized (NonnegativeKernel.ofGraphon V) hr.1 htp).le
  have hscale := scaledGraphon_cost_le V hl.1
  have hsaving := cost_towardOne_zero_saving U hs
  have hnonneg := mul_nonneg hsp.le (cost_nonneg U)
  have hnegative := mul_neg_of_pos_of_neg hsp hcoeff
  have hfrac : 3 * s / r ^ 3 = s * (3 / r ^ 3) := by ring
  have hloss := hl.2
  rw [hfrac] at hloss
  change cost V ≤ (1 - s) * cost U + s * Real.log s * zeroMass U at hsaving
  nlinarith

/-- Differentiating a bounded exponential tilt under a finite measure. -/
theorem hasDerivAt_integral_exp_tilt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : BoundedObservable μ f) (hg : BoundedObservable μ g) :
    HasDerivAt (fun s : ℝ => ∫ x, f x * Real.exp (s * g x) ∂μ)
      (∫ x, f x * g x ∂μ) 0 := by
  obtain ⟨A, hA, hfA⟩ := hf.bound
  obtain ⟨B, hB, hgB⟩ := hg.bound
  have hm : ∀ᶠ s : ℝ in 𝓝 0, AEStronglyMeasurable
      (fun x => f x * Real.exp (s * g x)) μ := Eventually.of_forall fun s =>
    (hf.measurable.mul (Real.measurable_exp.comp_aemeasurable
      (aemeasurable_const.mul hg.measurable))).aestronglyMeasurable
  have hi : Integrable (fun x => f x * Real.exp ((0 : ℝ) * g x)) μ := by
    simpa using hf.integrable
  have hdm : AEStronglyMeasurable (fun x => f x * (Real.exp ((0 : ℝ) * g x) * g x)) μ := by
    simpa using (hf.mul hg).measurable.aestronglyMeasurable
  have hbnd : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖f x * (Real.exp (s * g x) * g x)‖ ≤ A * Real.exp B * B := by
    filter_upwards [hfA, hgB] with x hfx hgx
    intro s hs
    have hs1 : |s| ≤ 1 := by
      have hh : |s| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      exact hh.le
    have hsg : s * g x ≤ B := calc
      s * g x ≤ |s * g x| := le_abs_self _
      _ = |s| * |g x| := abs_mul _ _
      _ ≤ 1 * B := mul_le_mul hs1 hgx (abs_nonneg _) (by norm_num)
      _ = B := one_mul _
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have he : Real.exp (s * g x) ≤ Real.exp B := Real.exp_le_exp.mpr hsg
    have hh := mul_le_mul hfx (mul_le_mul he hgx (norm_nonneg _) (Real.exp_pos B).le)
      (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hA
    simpa only [mul_assoc] using hh
  have hd : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => f x * Real.exp (t * g x))
        (f x * (Real.exp (s * g x) * g x)) s := by
    refine Eventually.of_forall fun x s _ => ?_
    simpa using ((hasDerivAt_id s).mul_const (g x)).exp.const_mul (f x)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (by norm_num : (0 : ℝ) < 1)
    hm hi hdm hbnd (integrable_const (A * Real.exp B * B)) hd
  simpa using h.2

/-- Exponential tilts preserve bounded observability for every fixed real parameter. -/
theorem boundedObservable_exp_tilt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : BoundedObservable μ g) (s : ℝ) :
    BoundedObservable μ (fun x => Real.exp (s * g x)) := by
  obtain ⟨B, hB, hgB⟩ := hg.bound
  refine ⟨Real.measurable_exp.comp_aemeasurable (aemeasurable_const.mul hg.measurable),
    Real.exp (|s| * B), (Real.exp_pos _).le, ?_⟩
  filter_upwards [hgB] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    s * g x ≤ |s * g x| := le_abs_self _
    _ = |s| * |g x| := abs_mul _ _
    _ ≤ |s| * B := mul_le_mul_of_nonneg_left hx (abs_nonneg _)

/-- Multiplicative perturbations remain bounded nonnegative kernels for all s. -/
def expTilt (U : Graphon) (D : ℝ × ℝ → ℝ) (hD : BoundedObservable squareMeasure D)
    (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) (s : ℝ) : NonnegativeKernel :=
  let hobs := (graphon_boundedObservable U).mul (boundedObservable_exp_tilt hD s)
  { toFun := fun p => U p * Real.exp (s * D p)
    measurable := hobs.measurable
    symmetric := by
      filter_upwards [U.symmetric, hDs] with p hu hd
      rw [hu, hd]
    nonneg := by
      filter_upwards [U.bounded] with p hp
      exact mul_nonneg hp.1 (Real.exp_pos _).le
    bound := hobs.bound.choose
    bound_nonneg := hobs.bound.choose_spec.1
    bounded := by
      filter_upwards [hobs.bound.choose_spec.2] with p hp
      exact (le_abs_self _).trans hp }

@[simp] theorem expTilt_zero (U : Graphon) (D : ℝ × ℝ → ℝ)
    (hD : BoundedObservable squareMeasure D) (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) :
    (expTilt U D hD hDs 0).toFun = U.toFun := by
  funext p
  simp [expTilt]

theorem graphon_entropy_boundedObservable (U : Graphon) :
    BoundedObservable squareMeasure (fun p => entropy (U p)) := by
  refine ⟨continuous_entropy.measurable.comp_aemeasurable U.measurable, 1, by norm_num, ?_⟩
  filter_upwards [U.bounded] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (entropy_nonneg hp.1)]
  exact entropy_le_one hp

/-- An exact formula for entropy along multiplicative perturbations. -/
theorem expTilt_cost_formula (U : Graphon) (D : ℝ × ℝ → ℝ)
    (hD : BoundedObservable squareMeasure D) (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p)
    (s : ℝ) :
    (expTilt U D hD hDs s).cost =
      (∫ p, entropy (U p) * Real.exp (s * D p) ∂squareMeasure) +
      s * (∫ p, (U p * D p) * Real.exp (s * D p) ∂squareMeasure) + 1 -
      (∫ p, Real.exp (s * D p) ∂squareMeasure) := by
  have hE := boundedObservable_exp_tilt hD s
  have h₁ : Integrable (fun p => entropy (U p) * Real.exp (s * D p)) squareMeasure :=
    ((graphon_entropy_boundedObservable U).mul hE).integrable
  have h₂ : Integrable (fun p => s * ((U p * D p) * Real.exp (s * D p))) squareMeasure :=
    ((((graphon_boundedObservable U).mul hD).mul hE).const_mul s).integrable
  have h₁₂ : Integrable (fun p => entropy (U p) * Real.exp (s * D p) +
      s * ((U p * D p) * Real.exp (s * D p))) squareMeasure := h₁.add h₂
  have h₁₂₃ : Integrable (fun p => entropy (U p) * Real.exp (s * D p) +
      s * ((U p * D p) * Real.exp (s * D p)) + 1) squareMeasure := h₁₂.add (integrable_const 1)
  have he : (fun p => entropy (expTilt U D hD hDs s p)) =ᵐ[squareMeasure]
      (fun p => entropy (U p) * Real.exp (s * D p) +
        s * ((U p * D p) * Real.exp (s * D p)) + 1 - Real.exp (s * D p)) := by
    filter_upwards [U.bounded] with p hp
    change entropy (U p * Real.exp (s * D p)) = _
    rw [mul_comm (U p), entropy_mul (Real.exp_pos _) hp.1, Real.log_exp]
    ring
  unfold NonnegativeKernel.cost
  rw [integral_congr_ae he, integral_sub h₁₂₃ hE.integrable,
    integral_add h₁₂ (integrable_const 1), integral_add h₁ h₂, integral_const_mul]
  simp

/-- Cost derivative of the multiplicative path, requiring no lower bound on U. -/
theorem hasDerivAt_expTilt_cost (U : Graphon) (D : ℝ × ℝ → ℝ)
    (hD : BoundedObservable squareMeasure D) (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) :
    HasDerivAt (fun s => (expTilt U D hD hDs s).cost)
      (∫ p, U p * Real.log (U p) * D p ∂squareMeasure) 0 := by
  have h₁ := hasDerivAt_integral_exp_tilt (graphon_entropy_boundedObservable U) hD
  have h₂ := hasDerivAt_integral_exp_tilt ((graphon_boundedObservable U).mul hD) hD
  have h₃ := hasDerivAt_integral_exp_tilt (BoundedObservable.const (μ := squareMeasure) 1) hD
  have hd := ((h₁.add ((hasDerivAt_id 0).mul h₂)).add_const 1).sub h₃
  have he : (fun s => (expTilt U D hD hDs s).cost) =
      (fun s => (∫ p, entropy (U p) * Real.exp (s * D p) ∂squareMeasure) +
        s * (∫ p, (U p * D p) * Real.exp (s * D p) ∂squareMeasure) + 1 -
        (∫ p, (1 : ℝ) * Real.exp (s * D p) ∂squareMeasure)) := by
    funext s
    simpa using expTilt_cost_formula U D hD hDs s
  rw [he]
  convert hd using 1
  simp only [id_eq, one_mul, zero_mul, Real.exp_zero, mul_one, add_zero]
  have hi₁ := ((graphon_entropy_boundedObservable U).mul hD).integrable
  have hi₂ := ((graphon_boundedObservable U).mul hD).integrable
  have hi₁₂ : Integrable (fun p => entropy (U p) * D p + U p * D p) squareMeasure := hi₁.add hi₂
  rw [← integral_add hi₁ hi₂, ← integral_sub hi₁₂ hD.integrable]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by unfold entropy; ring)

theorem hasDerivAt_expTilt_edgeDensity (U : Graphon) (D : ℝ × ℝ → ℝ)
    (hD : BoundedObservable squareMeasure D) (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) :
    HasDerivAt (fun s => (expTilt U D hD hDs s).edgeDensity)
      (∫ p, U p * D p ∂squareMeasure) 0 :=
  hasDerivAt_integral_exp_tilt (graphon_boundedObservable U) hD

/-- Product of the three original edge values in the product-measure convention. -/
def tiltTriangleWeight (U : Graphon) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  TriangleIntegration.X U p * TriangleIntegration.Y U p * TriangleIntegration.Z U p

def tiltTriangleDirection (D : ℝ × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  D p.1 + D (p.1.2,p.2) + D (p.1.1,p.2)

theorem tiltTriangleWeight_bounded (U : Graphon) :
    BoundedObservable TriangleIntegration.tripleMeasure (tiltTriangleWeight U) :=
  ((TriangleIntegration.boundedX U).mul (TriangleIntegration.boundedY U)).mul
    (TriangleIntegration.boundedZ U)

theorem tiltTriangleDirection_bounded {D : ℝ × ℝ → ℝ}
    (hD : BoundedObservable squareMeasure D) :
    BoundedObservable TriangleIntegration.tripleMeasure (tiltTriangleDirection D) :=
  ((hD.comp TriangleIntegration.edgeX_qmp).add (hD.comp TriangleIntegration.edgeY_qmp)).add
    (hD.comp TriangleIntegration.edgeZ_qmp)

/-- Exact triangle formula for the multiplicative perturbation. -/
theorem expTilt_triangle_formula (U : Graphon) (D : ℝ × ℝ → ℝ)
    (hD : BoundedObservable squareMeasure D) (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p)
    (s : ℝ) :
    (expTilt U D hD hDs s).triangle =
      ∫ p, tiltTriangleWeight U p * Real.exp (s * tiltTriangleDirection D p)
        ∂TriangleIntegration.tripleMeasure := by
  unfold NonnegativeKernel.triangle
  rw [← (measurePreserving_prodAssoc unitMeasure unitMeasure unitMeasure).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun p : ℝ × (ℝ × ℝ) => expTilt U D hD hDs s (p.1,p.2.1) *
      expTilt U D hD hDs s (p.2.1,p.2.2) * expTilt U D hD hDs s (p.1,p.2.2))]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    change (U (p.1.1,p.1.2) * Real.exp (s * D p.1)) *
      (U (p.1.2,p.2) * Real.exp (s * D (p.1.2,p.2))) *
      (U (p.1.1,p.2) * Real.exp (s * D (p.1.1,p.2))) =
      (U (p.1.1,p.1.2) * U (p.1.2,p.2) * U (p.1.1,p.2)) *
        Real.exp (s * (D p.1 + D (p.1.2,p.2) + D (p.1.1,p.2)))
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
    ring

/-- Cyclic invariance with an arbitrary bounded symmetric direction, rather
than a direction depending only on the value of the graphon. -/
theorem integral_triangle_direction_cycle (U : Graphon) {D : ℝ × ℝ → ℝ}
    (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) :
    (∫ p, tiltTriangleWeight U p * D (p.1.2,p.2) ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p * D p.1 ∂TriangleIntegration.tripleMeasure) ∧
    (∫ p, tiltTriangleWeight U p * D (p.1.1,p.2) ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p * D p.1 ∂TriangleIntegration.tripleMeasure) := by
  have h₁ : (∫ p, tiltTriangleWeight U p * D (p.1.2,p.2) ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p * D p.1 ∂TriangleIntegration.tripleMeasure) := by
    calc
      _ = ∫ p, tiltTriangleWeight U (TriangleIntegration.cycle p) *
          D (TriangleIntegration.cycle p).1 ∂TriangleIntegration.tripleMeasure := by
        apply integral_congr_ae
        filter_upwards [TriangleIntegration.edgeZ_qmp.ae U.symmetric,
          TriangleIntegration.edgeX_qmp.ae U.symmetric] with p hz hx
        change U (p.2,p.1.1) = U (p.1.1,p.2) at hz
        change U (p.1.2,p.1.1) = U (p.1.1,p.1.2) at hx
        change U (p.1.1,p.1.2) * U (p.1.2,p.2) * U (p.1.1,p.2) * D (p.1.2,p.2) =
          U (p.1.2,p.2) * U (p.2,p.1.1) * U (p.1.2,p.1.1) * D (p.1.2,p.2)
        rw [hz, hx]
        ring
      _ = _ := TriangleIntegration.cycle_preserving.integral_comp
        TriangleIntegration.cycle.measurableEmbedding
        (fun p => tiltTriangleWeight U p * D p.1)
  refine ⟨h₁, ?_⟩
  calc
    _ = ∫ p, tiltTriangleWeight U (TriangleIntegration.cycle p) *
        D ((TriangleIntegration.cycle p).1.2,(TriangleIntegration.cycle p).2)
          ∂TriangleIntegration.tripleMeasure := by
      apply integral_congr_ae
      filter_upwards [TriangleIntegration.edgeZ_qmp.ae U.symmetric,
        TriangleIntegration.edgeX_qmp.ae U.symmetric,
        TriangleIntegration.edgeZ_qmp.ae hDs] with p hz hx hd
      change U (p.2,p.1.1) = U (p.1.1,p.2) at hz
      change U (p.1.2,p.1.1) = U (p.1.1,p.1.2) at hx
      change D (p.2,p.1.1) = D (p.1.1,p.2) at hd
      change U (p.1.1,p.1.2) * U (p.1.2,p.2) * U (p.1.1,p.2) * D (p.1.1,p.2) =
        U (p.1.2,p.2) * U (p.2,p.1.1) * U (p.1.2,p.1.1) * D (p.2,p.1.1)
      rw [hz, hx, hd]
      ring
    _ = ∫ p, tiltTriangleWeight U p * D (p.1.2,p.2) ∂TriangleIntegration.tripleMeasure :=
      TriangleIntegration.cycle_preserving.integral_comp
        TriangleIntegration.cycle.measurableEmbedding
        (fun p => tiltTriangleWeight U p * D (p.1.2,p.2))
    _ = _ := h₁

/-- The three edge derivatives coincide and each is a codegree integral. -/
theorem integral_tiltTriangleDirection (U : Graphon) (D : ℝ × ℝ → ℝ)
    (hD : BoundedObservable squareMeasure D) (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) :
    (∫ p, tiltTriangleWeight U p * tiltTriangleDirection D p ∂TriangleIntegration.tripleMeasure) =
      3 * ∫ p, (U p * D p) * codegree U p.1 p.2 ∂squareMeasure := by
  have hw := tiltTriangleWeight_bounded U
  have h₁ := (hw.mul (hD.comp TriangleIntegration.edgeX_qmp)).integrable
  have h₂ := (hw.mul (hD.comp TriangleIntegration.edgeY_qmp)).integrable
  have h₃ := (hw.mul (hD.comp TriangleIntegration.edgeZ_qmp)).integrable
  have h₁₂ : Integrable (fun p => tiltTriangleWeight U p * D p.1 +
      tiltTriangleWeight U p * D (p.1.2,p.2)) TriangleIntegration.tripleMeasure := h₁.add h₂
  simp only [tiltTriangleDirection, mul_add]
  rw [integral_add h₁₂ h₃, integral_add h₁ h₂,
    (integral_triangle_direction_cycle U hDs).1, (integral_triangle_direction_cycle U hDs).2]
  have htest : (∫ p, tiltTriangleWeight U p * D p.1 ∂TriangleIntegration.tripleMeasure) =
      ∫ p, (U p * D p) * codegree U p.1 p.2 ∂squareMeasure := by
    calc
      _ = ∫ p, (U p.1 * D p.1) * TriangleIntegration.Y U p * TriangleIntegration.Z U p
          ∂TriangleIntegration.tripleMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by unfold tiltTriangleWeight TriangleIntegration.X; ring)
      _ = _ := TriangleIntegration.integral_test_codegree U ((graphon_boundedObservable U).mul hD)
  rw [htest]
  ring

/-- Triangle derivative of the bounded multiplicative perturbation. -/
theorem hasDerivAt_expTilt_triangle (U : Graphon) (D : ℝ × ℝ → ℝ)
    (hD : BoundedObservable squareMeasure D) (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) :
    HasDerivAt (fun s => (expTilt U D hD hDs s).triangle)
      (3 * ∫ p, (U p * D p) * codegree U p.1 p.2 ∂squareMeasure) 0 := by
  have hd := hasDerivAt_integral_exp_tilt (tiltTriangleWeight_bounded U) (tiltTriangleDirection_bounded hD)
  rw [integral_tiltTriangleDirection U D hD hDs] at hd
  have he := funext (expTilt_triangle_formula U D hD hDs)
  rw [he]
  exact hd

theorem graphon_mulLog_boundedObservable (U : Graphon) :
    BoundedObservable squareMeasure (fun p => U p * Real.log (U p)) := by
  have hf := Real.continuous_mul_log
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨hf.measurable.comp_aemeasurable U.measurable, max K 0, le_max_right _ _, ?_⟩
  filter_upwards [U.bounded] with p hp
  exact (hK (U p) hp).trans (le_max_left _ _)

/-- The residual multiplied by U is bounded even before proving any positive lower bound. -/
def weightedEulerResidual (U : Graphon) (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  U p * Real.log (U p) + graphonMultiplier U r * U p * codegree U p.1 p.2

theorem weightedEulerResidual_bounded (U : Graphon) (r : ℝ) :
    BoundedObservable squareMeasure (weightedEulerResidual U r) :=
  (graphon_mulLog_boundedObservable U).add
    (((graphon_boundedObservable U).const_mul (graphonMultiplier U r)).mul (codegree_boundedObservable U))

theorem codegree_symm (U : Graphon) (x y : ℝ) : codegree U x y = codegree U y x := by
  unfold codegree
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => mul_comm _ _)

theorem weightedEulerResidual_symmetric (U : Graphon) (r : ℝ) :
    ∀ᵐ p ∂squareMeasure, weightedEulerResidual U r p.swap = weightedEulerResidual U r p := by
  filter_upwards [U.symmetric] with p hp
  change U p.swap * Real.log (U p.swap) + graphonMultiplier U r * U p.swap * codegree U p.2 p.1 =
    U p * Real.log (U p) + graphonMultiplier U r * U p * codegree U p.1 p.2
  rw [hp, codegree_symm U p.2 p.1]

/-- Stationarity against every bounded symmetric multiplicative direction. -/
theorem minimizer_weighted_variation {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) (D : ℝ × ℝ → ℝ) (hD : BoundedObservable squareMeasure D)
    (hDs : ∀ᵐ p ∂squareMeasure, D p.swap = D p) :
    (∫ p, weightedEulerResidual U r p * D p ∂squareMeasure) = 0 := by
  have hz : (expTilt U D hD hDs 0).toFun =ᵐ[squareMeasure] U.toFun := by
    rw [expTilt_zero]
  have h := rescaling_firstVariation hr hU hz (hasDerivAt_expTilt_cost U D hD hDs)
    (hasDerivAt_expTilt_edgeDensity U D hD hDs) (hasDerivAt_expTilt_triangle U D hD hDs)
  have hi₁ : Integrable (fun p => U p * Real.log (U p) * D p) squareMeasure :=
    ((graphon_mulLog_boundedObservable U).mul hD).integrable
  have hi₂ : Integrable (fun p => graphonMultiplier U r * ((U p * D p) * codegree U p.1 p.2))
      squareMeasure := ((((graphon_boundedObservable U).mul hD).mul
        (codegree_boundedObservable U)).const_mul _).integrable
  have he : (∫ p, weightedEulerResidual U r p * D p ∂squareMeasure) =
      (∫ p, U p * Real.log (U p) * D p ∂squareMeasure) + graphonMultiplier U r *
        (∫ p, (U p * D p) * codegree U p.1 p.2 ∂squareMeasure) := by
    rw [← integral_const_mul, ← integral_add hi₁ hi₂]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by unfold weightedEulerResidual; ring)
  rw [he]
  nlinarith [h]

/-- `prop:euler`(b): the actual Euler--Lagrange equation for all minimizers.
The bounded weighted residual is itself an admissible multiplicative test. -/
theorem minimizer_log_equation {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, Real.log (U p) = -graphonMultiplier U r * codegree U p.1 p.2 := by
  have hD := weightedEulerResidual_bounded U r
  have hv := minimizer_weighted_variation hr hU (weightedEulerResidual U r) hD
    (weightedEulerResidual_symmetric U r)
  have hzero : (fun p => weightedEulerResidual U r p * weightedEulerResidual U r p) =ᵐ[squareMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => mul_self_nonneg _) (hD.mul hD).integrable).mp hv
  filter_upwards [hzero, minimizer_pos_ae hr hU] with p hp hUp
  have hres : weightedEulerResidual U r p = 0 := mul_self_eq_zero.mp hp
  unfold weightedEulerResidual at hres
  have hmul : U p * (Real.log (U p) + graphonMultiplier U r * codegree U p.1 p.2) = 0 := by
    nlinarith [hres]
  have he := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hUp)
  linarith

/-- Every graphon has codegrees in the unit interval almost everywhere. -/
theorem codegree_mem_Icc_ae (U : Graphon) :
    ∀ᵐ p ∂squareMeasure, codegree U p.1 p.2 ∈ Icc (0 : ℝ) 1 := by
  have hb := (TriangleIntegration.edgeZ_qmp.ae U.bounded).and
    (TriangleIntegration.edgeY_qmp.ae U.bounded)
  have hrow := Measure.ae_ae_of_ae_prod hb
  filter_upwards [hrow] with p hp
  have hlo : ∀ᵐ z ∂unitMeasure, 0 ≤ U (p.1,z) * U (p.2,z) := hp.mono fun z hz =>
    mul_nonneg hz.1.1 hz.2.1
  have hhi : ∀ᵐ z ∂unitMeasure, ‖U (p.1,z) * U (p.2,z)‖ ≤ 1 := by
    filter_upwards [hp] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz.1.1 hz.2.1)]
    exact (mul_le_mul hz.1.2 hz.2.2 hz.2.1 (by norm_num)).trans (by norm_num)
  refine ⟨integral_nonneg_of_ae hlo, ?_⟩
  have hn : ‖codegree U p.1 p.2‖ ≤ 1 := by simpa [codegree] using norm_integral_le_of_norm_le_const hhi
  exact (le_abs_self _).trans hn

/-- Positive lower bounds pass to codegrees by Fubini and monotonicity of integrals. -/
theorem codegree_lower_bound_ae (U : Graphon) {ell : ℝ} (hell : 0 ≤ ell)
    (hU : ∀ᵐ p ∂squareMeasure, ell ≤ U p) :
    ∀ᵐ p ∂squareMeasure, ell ^ 2 ≤ codegree U p.1 p.2 := by
  have hb := (TriangleIntegration.edgeZ_qmp.ae hU).and (TriangleIntegration.edgeY_qmp.ae hU)
  have hrow := Measure.ae_ae_of_ae_prod hb
  have hi := ((TriangleIntegration.boundedZ U).mul (TriangleIntegration.boundedY U)).integrable.prod_right_ae
  filter_upwards [hrow, hi] with p hp hip
  have hm : ∀ᵐ z ∂unitMeasure, ell ^ 2 ≤ U (p.1,z) * U (p.2,z) := by
    filter_upwards [hp] with z hz
    simpa only [pow_two] using mul_le_mul hz.1 hz.2 hell (hell.trans hz.1)
  have h := integral_mono_ae (integrable_const (ell ^ 2)) hip hm
  simpa [codegree] using h

/-- The integral identity in `prop:euler`(c), before multiplication by μ. -/
theorem integral_mulLog_identity (U : Graphon) :
    (∫ p, U p * Real.log (U p) ∂squareMeasure) = cost U + edgeDensity U - 1 := by
  have hsum : Integrable (fun p => entropy (U p) + U p) squareMeasure :=
    (cost_integrable U).add (graphon_integrable U)
  calc
    _ = ∫ p, entropy (U p) + U p - 1 ∂squareMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by unfold entropy; ring)
    _ = _ := by
      rw [integral_sub hsum (integrable_const 1), integral_add (cost_integrable U) (graphon_integrable U)]
      simp [cost, edgeDensity]

/-- The multiplier-integral identity uses only its explicit definition. -/
theorem graphonMultiplier_integral_identity {U : Graphon} {r : ℝ} (hr : r ≠ 0) :
    graphonMultiplier U r * r ^ 3 = -(∫ p, U p * Real.log (U p) ∂squareMeasure) := by
  rw [graphonMultiplier, div_mul_cancel₀ _ (pow_ne_zero _ hr), integral_mulLog_identity]
  ring

/-- `prop:euler`(c): the multiplier is strictly positive. -/
theorem minimizer_multiplier_pos {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : 0 < graphonMultiplier U r := by
  by_contra hn
  have hμ : graphonMultiplier U r ≤ 0 := le_of_not_gt hn
  have hall : IsConstant U 1 := by
    filter_upwards [minimizer_pos_ae hr hU, minimizer_log_equation hr hU,
      codegree_mem_Icc_ae U, U.bounded] with p hp hel hc hb
    have hlogp : 0 ≤ Real.log (U p) := by
      rw [hel]
      exact mul_nonneg (neg_nonneg.mpr hμ) hc.1
    have hlogn : Real.log (U p) ≤ 0 := Real.log_nonpos hb.1 hb.2
    exact Real.eq_one_of_pos_of_log_eq_zero hp (le_antisymm hlogn hlogp)
  have ht : triangle U = 1 := by
    have h := triangle_congr_ae (U := U) (W := constant 1 (by norm_num)) hall
    simpa using h
  have hact := minimizer_triangle_eq hr hU
  have hr3 := pow_lt_one₀ hr.1.le hr.2 (by decide : 3 ≠ 0)
  linarith

/-- Exponential form of the Euler--Lagrange equation, with positivity already proved. -/
theorem minimizer_exp_equation {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, U p = Real.exp (-graphonMultiplier U r * codegree U p.1 p.2) := by
  filter_upwards [minimizer_pos_ae hr hU, minimizer_log_equation hr hU] with p hp he
  rw [← he, Real.exp_log hp]

/-- First quantitative lower bound in `prop:euler`(d). -/
theorem minimizer_lower_bound {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, Real.exp (-graphonMultiplier U r) ≤ U p := by
  have hμ := minimizer_multiplier_pos hr hU
  filter_upwards [minimizer_exp_equation hr hU, codegree_mem_Icc_ae U] with p he hc
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hc.2 hμ.le]

/-- Positive codegree lower bound in `prop:euler`(d). -/
theorem minimizer_codegree_lower_bound {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, Real.exp (-2 * graphonMultiplier U r) ≤ codegree U p.1 p.2 := by
  have h := codegree_lower_bound_ae U (Real.exp_pos (-graphonMultiplier U r)).le
    (minimizer_lower_bound hr hU)
  have he : Real.exp (-graphonMultiplier U r) ^ 2 = Real.exp (-2 * graphonMultiplier U r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [he] using h

/-- Quantitative upper bound in `prop:euler`(d). -/
theorem minimizer_upper_bound {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) :
    ∀ᵐ p ∂squareMeasure, U p ≤
      Real.exp (-graphonMultiplier U r * Real.exp (-2 * graphonMultiplier U r)) := by
  have hμ := minimizer_multiplier_pos hr hU
  filter_upwards [minimizer_exp_equation hr hU, minimizer_codegree_lower_bound hr hU] with p he hc
  rw [he]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr hμ.le)

theorem minimizer_upper_constant_lt_one {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) :
    Real.exp (-graphonMultiplier U r * Real.exp (-2 * graphonMultiplier U r)) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (minimizer_multiplier_pos hr hU)) (Real.exp_pos _)

/-- Uniqueness of the multiplier in `prop:euler`(c). -/
theorem minimizer_multiplier_unique {r μ : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U)
    (he : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ * codegree U p.1 p.2) :
    μ = graphonMultiplier U r := by
  have hall : ∀ᵐ p ∂squareMeasure, μ = graphonMultiplier U r := by
    filter_upwards [he, minimizer_log_equation hr hU, minimizer_codegree_lower_bound hr hU]
      with p he₁ he₂ hc
    have hp : 0 < codegree U p.1 p.2 := (Real.exp_pos _).trans_le hc
    have hh : (μ - graphonMultiplier U r) * codegree U p.1 p.2 = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (ne_of_gt hp))
  obtain ⟨p, hp⟩ := hall.exists
  exact hp

end SparseLowerTail.Section04

import SparseLowerTail.Section04.ActiveConstraint
import SparseLowerTail.Section04.BalancedStationary
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Nonnegative kernels, truncation, and rescaling variations

Stable manuscript anchors: `lem:scaling`, `eq:scale1`, `lem:truncation`,
`s3:rescale`. The manuscript's kernels are bounded measurable symmetric
functions. The representation below preserves that convention, while allowing
values greater than one. No integrability assertion is made for arbitrary L¹
kernels: all needed integrability follows from the recorded finite bound.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace SparseLowerTail

/-- A bounded nonnegative symmetric kernel, with a finite a.e. bound.
This extends `Graphon` without requiring an upper bound of one. -/
structure NonnegativeKernel where
  toFun : ℝ × ℝ → ℝ
  measurable : AEMeasurable toFun squareMeasure
  symmetric : ∀ᵐ p ∂squareMeasure, toFun p.swap = toFun p
  nonneg : ∀ᵐ p ∂squareMeasure, 0 ≤ toFun p
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ᵐ p ∂squareMeasure, toFun p ≤ bound

instance : CoeFun NonnegativeKernel (fun _ => ℝ × ℝ → ℝ) := ⟨NonnegativeKernel.toFun⟩

namespace NonnegativeKernel

def ofGraphon (U : Graphon) : NonnegativeKernel where
  toFun := U.toFun
  measurable := U.measurable
  symmetric := U.symmetric
  nonneg := U.bounded.mono fun _ h => h.1
  bound := 1
  bound_nonneg := by norm_num
  bounded := U.bounded.mono fun _ h => h.2

def cost (W : NonnegativeKernel) : ℝ := ∫ p, entropy (W p) ∂squareMeasure

def edgeDensity (W : NonnegativeKernel) : ℝ := ∫ p, W p ∂squareMeasure

def triangle (W : NonnegativeKernel) : ℝ :=
  ∫ p : ℝ × (ℝ × ℝ), W (p.1, p.2.1) * W (p.2.1, p.2.2) * W (p.1, p.2.2) ∂cubeMeasure

@[simp] theorem cost_ofGraphon (U : Graphon) : (ofGraphon U).cost = SparseLowerTail.cost U := rfl
@[simp] theorem triangle_ofGraphon (U : Graphon) :
    (ofGraphon U).triangle = SparseLowerTail.triangle U := rfl
@[simp] theorem edgeDensity_ofGraphon (U : Graphon) :
    (ofGraphon U).edgeDensity = SparseLowerTail.edgeDensity U := rfl

theorem integrable (W : NonnegativeKernel) : Integrable W.toFun squareMeasure := by
  apply Integrable.of_bound W.measurable.aestronglyMeasurable W.bound
  filter_upwards [W.nonneg, W.bounded] with p hp hpb
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hpb

theorem cost_integrable (W : NonnegativeKernel) :
    Integrable (fun p => entropy (W p)) squareMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) W.bound)).exists_bound_of_continuousOn
    continuous_entropy.continuousOn
  apply Integrable.of_bound
    (continuous_entropy.measurable.comp_aemeasurable W.measurable).aestronglyMeasurable C
  filter_upwards [W.nonneg, W.bounded] with p hp hpb
  exact hC (W p) ⟨hp, hpb⟩

theorem edge12_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.1)) cubeMeasure squareMeasure :=
  QuasiMeasurePreserving.prodMap
    (QuasiMeasurePreserving.id unitMeasure) quasiMeasurePreserving_fst

theorem edge23_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.2.1, p.2.2)) cubeMeasure squareMeasure :=
  quasiMeasurePreserving_snd

theorem edge13_qmp :
    QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.2)) cubeMeasure squareMeasure :=
  QuasiMeasurePreserving.prodMap
    (QuasiMeasurePreserving.id unitMeasure) quasiMeasurePreserving_snd

theorem triangle_integrable (W : NonnegativeKernel) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      W (p.1, p.2.1) * W (p.2.1, p.2.2) * W (p.1, p.2.2)) cubeMeasure := by
  have hm := ((W.measurable.comp_quasiMeasurePreserving edge12_qmp).mul
    (W.measurable.comp_quasiMeasurePreserving edge23_qmp)).mul
    (W.measurable.comp_quasiMeasurePreserving edge13_qmp)
  apply Integrable.of_bound hm.aestronglyMeasurable (W.bound ^ 3)
  filter_upwards [edge12_qmp.ae W.nonneg, edge23_qmp.ae W.nonneg,
    edge13_qmp.ae W.nonneg, edge12_qmp.ae W.bounded, edge23_qmp.ae W.bounded,
    edge13_qmp.ae W.bounded] with p h12 h23 h13 b12 b23 b13
  change ‖W (p.1, p.2.1) * W (p.2.1, p.2.2) * W (p.1, p.2.2)‖ ≤ W.bound ^ 3
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h12 h23) h13)]
  have h := mul_le_mul (mul_le_mul b12 b23 h23 W.bound_nonneg) b13 h13
    (mul_nonneg W.bound_nonneg W.bound_nonneg)
  simpa only [pow_succ, pow_zero, one_mul] using h

/-- Positive scalar multiplication stays inside the class of kernels. -/
def scale (W : NonnegativeKernel) (c : ℝ) (hc : 0 ≤ c) : NonnegativeKernel where
  toFun := fun p => c * W p
  measurable := aemeasurable_const.mul W.measurable
  symmetric := W.symmetric.mono fun _ hp => congrArg (fun x => c * x) hp
  nonneg := W.nonneg.mono fun _ hp => mul_nonneg hc hp
  bound := c * W.bound
  bound_nonneg := mul_nonneg hc W.bound_nonneg
  bounded := W.bounded.mono fun _ hp => mul_le_mul_of_nonneg_left hp hc

/-- Cubic homogeneity in `lem:scaling`. -/
theorem triangle_scale (W : NonnegativeKernel) (c : ℝ) (hc : 0 ≤ c) :
    (W.scale c hc).triangle = c ^ 3 * W.triangle := by
  unfold triangle scale
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by dsimp; ring)

theorem edgeDensity_scale (W : NonnegativeKernel) (c : ℝ) (hc : 0 ≤ c) :
    (W.scale c hc).edgeDensity = c * W.edgeDensity := by
  simp only [edgeDensity, scale, integral_const_mul]

/-- Exact entropy scaling, stable manuscript anchor `eq:scale1`. -/
theorem cost_scale (W : NonnegativeKernel) (c : ℝ) (hc : 0 < c) :
    (W.scale c hc.le).cost = c * W.cost + (c * Real.log c) * W.edgeDensity + 1 - c := by
  have he : (fun p => entropy (W.scale c hc.le p)) =ᵐ[squareMeasure]
      (fun p => c * entropy (W p) + (c * Real.log c) * W p + (1 - c)) := by
    filter_upwards [W.nonneg] with p hp
    change entropy (c * W p) = _
    rw [Section04.entropy_mul hc hp]
    ring
  have h₁ : Integrable (fun p => c * entropy (W p)) squareMeasure := W.cost_integrable.const_mul c
  have h₂ : Integrable (fun p => (c * Real.log c) * W p) squareMeasure :=
    W.integrable.const_mul (c * Real.log c)
  have h₁₂ : Integrable (fun p => c * entropy (W p) + (c * Real.log c) * W p) squareMeasure :=
    h₁.add h₂
  unfold cost
  rw [integral_congr_ae he, integral_add h₁₂ (integrable_const (1 - c)),
    integral_add h₁ h₂, integral_const_mul, integral_const_mul]
  simp only [integral_const, measureReal_univ_eq_one, one_smul, edgeDensity]
  ring

/-- Cost relative to a constant, stable manuscript anchor `eq:scale2`. -/
theorem cost_scale_sub_entropy (W : NonnegativeKernel) (c s : ℝ)
    (hc : 0 < c) (hs : 0 ≤ s) :
    (W.scale c hc.le).cost - entropy (c * s) =
      c * (W.cost - entropy s) + (c * Real.log c) * (W.edgeDensity - s) := by
  rw [cost_scale W c hc, Section04.entropy_mul hc hs]
  ring

/-- Truncation produces a graphon while preserving symmetry and measurability. -/
def truncate (W : NonnegativeKernel) : Graphon where
  toFun := fun p => min (W p) 1
  measurable := W.measurable.min aemeasurable_const
  symmetric := W.symmetric.mono fun _ hp => congrArg (fun x => min x 1) hp
  bounded := by
    filter_upwards [W.nonneg] with p hp
    exact ⟨le_min hp (by norm_num), min_le_right _ _⟩

/-- Triangle truncation inequality in `lem:truncation`. -/
theorem triangle_truncate_le (W : NonnegativeKernel) :
    SparseLowerTail.triangle W.truncate ≤ W.triangle := by
  apply integral_mono_ae (SparseLowerTail.triangle_integrable W.truncate) W.triangle_integrable
  filter_upwards [edge12_qmp.ae W.nonneg, edge23_qmp.ae W.nonneg,
    edge13_qmp.ae W.nonneg] with p h12 h23 h13
  change min (W (p.1, p.2.1)) 1 * min (W (p.2.1, p.2.2)) 1 * min (W (p.1, p.2.2)) 1 ≤ _
  exact mul_le_mul
    (mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min h23 (by norm_num)) h12)
    (min_le_left _ _) (le_min h13 (by norm_num)) (mul_nonneg h12 h23)

/-- Scalar entropy decreases under truncation. -/
theorem entropy_min_one_le {x : ℝ} (hx : 0 ≤ x) : entropy (min x 1) ≤ entropy x := by
  by_cases h : x ≤ 1
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h), entropy_one]
    exact entropy_nonneg hx

/-- Entropy truncation inequality in `lem:truncation`. -/
theorem cost_truncate_le (W : NonnegativeKernel) : SparseLowerTail.cost W.truncate ≤ W.cost := by
  apply integral_mono_ae (SparseLowerTail.cost_integrable W.truncate) W.cost_integrable
  filter_upwards [W.nonneg] with p hp
  exact entropy_min_one_le hp

/-- The extended comparison `s3:ext` for every bounded nonnegative kernel. -/
theorem minimizer_cost_le {r : ℝ} {U : Graphon} (hU : IsMinimizer r U)
    (W : NonnegativeKernel) (hW : W.triangle ≤ r ^ 3) : SparseLowerTail.cost U ≤ W.cost :=
  (hU.2 W.truncate ((triangle_truncate_le W).trans hW)).trans (cost_truncate_le W)

/-- Entropy is strictly increasing above its minimum at one. -/
theorem strictMonoOn_entropy_aboveOne : StrictMonoOn entropy (Ici (1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) continuous_entropy.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hp : 0 < x := lt_trans (by norm_num) hx
  rw [(Section04.hasDerivAt_entropy (ne_of_gt hp)).deriv]
  exact Real.log_pos hx

theorem entropy_min_one_eq_iff {x : ℝ} (_hx : 0 ≤ x) :
    entropy (min x 1) = entropy x ↔ x ≤ 1 := by
  constructor
  · intro he
    by_contra hn
    have h := strictMonoOn_entropy_aboveOne (show (1 : ℝ) ∈ Ici (1 : ℝ) by norm_num)
      (le_of_not_ge hn) (lt_of_not_ge hn)
    rw [min_eq_right (le_of_not_ge hn), entropy_one] at he
    simp only [entropy_one] at h
    linarith
  · intro h
    rw [min_eq_left h]

/-- Equality in truncation forces the original kernel to be bounded by one a.e. -/
theorem cost_truncate_eq_iff (W : NonnegativeKernel) :
    SparseLowerTail.cost W.truncate = W.cost ↔ ∀ᵐ p ∂squareMeasure, W p ≤ 1 := by
  have hle : (fun p => entropy (W.truncate p)) ≤ᵐ[squareMeasure]
      (fun p => entropy (W p)) := by
    filter_upwards [W.nonneg] with p hp
    exact entropy_min_one_le hp
  rw [SparseLowerTail.cost, cost, integral_eq_iff_of_ae_le
    (SparseLowerTail.cost_integrable W.truncate) W.cost_integrable hle]
  constructor
  · intro he
    filter_upwards [he, W.nonneg] with p hp hn
    exact (entropy_min_one_eq_iff hn).mp hp
  · intro hb
    filter_upwards [hb] with p hp
    change entropy (min (W p) 1) = entropy (W p)
    rw [min_eq_left hp]

theorem cost_truncate_lt_of_not_bounded (W : NonnegativeKernel)
    (hW : ¬ ∀ᵐ p ∂squareMeasure, W p ≤ 1) : SparseLowerTail.cost W.truncate < W.cost := by
  exact lt_of_le_of_ne (cost_truncate_le W) (fun he => hW ((cost_truncate_eq_iff W).mp he))

theorem cost_congr_ae {W V : NonnegativeKernel}
    (he : W.toFun =ᵐ[squareMeasure] V.toFun) : W.cost = V.cost :=
  integral_congr_ae (he.fun_comp entropy)

theorem edgeDensity_congr_ae {W V : NonnegativeKernel}
    (he : W.toFun =ᵐ[squareMeasure] V.toFun) : W.edgeDensity = V.edgeDensity :=
  integral_congr_ae he

theorem triangle_congr_ae {W V : NonnegativeKernel}
    (he : W.toFun =ᵐ[squareMeasure] V.toFun) : W.triangle = V.triangle := by
  apply integral_congr_ae
  filter_upwards [edge12_qmp.ae he, edge23_qmp.ae he, edge13_qmp.ae he] with p h12 h23 h13
  change W (p.1,p.2.1) = V (p.1,p.2.1) at h12
  change W (p.2.1,p.2.2) = V (p.2.1,p.2.2) at h23
  change W (p.1,p.2.2) = V (p.1,p.2.2) at h13
  rw [h12, h23, h13]

/-- Literal strict truncation statement when the superlevel set has positive measure. -/
theorem cost_truncate_lt (W : NonnegativeKernel)
    (hW : 0 < squareMeasure {p | 1 < W p}) : SparseLowerTail.cost W.truncate < W.cost := by
  apply cost_truncate_lt_of_not_bounded W
  intro hb
  have hz := ae_iff.mp hb
  simp only [not_le] at hz
  rw [hz] at hW
  exact (lt_irrefl _ hW)

/-- Every feasible nonnegative kernel has cost at least the graphon variational value. -/
theorem value_le_cost {r : ℝ} (W : NonnegativeKernel) (hW : W.triangle ≤ r ^ 3) :
    value r ≤ W.cost :=
  (SparseLowerTail.value_le_cost ((triangle_truncate_le W).trans hW)).trans (cost_truncate_le W)

/-- Equality with the variational value cannot occur above one on a set of positive measure. -/
theorem bounded_of_cost_eq_value {r : ℝ} (W : NonnegativeKernel)
    (hW : W.triangle ≤ r ^ 3) (he : W.cost = value r) :
    ∀ᵐ p ∂squareMeasure, W p ≤ 1 := by
  apply (cost_truncate_eq_iff W).mp
  apply le_antisymm (cost_truncate_le W)
  rw [he]
  exact SparseLowerTail.value_le_cost ((triangle_truncate_le W).trans hW)

end NonnegativeKernel
namespace Section04

/-- The explicit multiplier in `eq:mult`. -/
def graphonMultiplier (U : Graphon) (r : ℝ) : ℝ :=
  (1 - SparseLowerTail.cost U - SparseLowerTail.edgeDensity U) / r ^ 3

/-- The positive scaling that restores the target triangle density. -/
def normalizingScale (r t : ℝ) : ℝ := (r ^ 3 / t) ^ (1 / 3 : ℝ)

theorem normalizingScale_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    0 < normalizingScale r t := Real.rpow_pos_of_pos (div_pos (pow_pos hr _) ht) _

theorem normalizingScale_cube {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    normalizingScale r t ^ 3 = r ^ 3 / t := by
  unfold normalizingScale
  simpa only [one_div] using Real.rpow_inv_natCast_pow (n := 3)
    (x := r ^ 3 / t) (div_nonneg (pow_nonneg hr.le _) ht.le) (by decide : (3 : ℕ) ≠ 0)

@[simp] theorem normalizingScale_self {r : ℝ} (hr : 0 < r) :
    normalizingScale r (r ^ 3) = 1 := by
  simp [normalizingScale, ne_of_gt hr]

/-- The restored triangle density is exactly the target, not merely feasible. -/
theorem triangle_normalized (W : NonnegativeKernel) {r : ℝ} (hr : 0 < r)
    (ht : 0 < W.triangle) :
    (W.scale (normalizingScale r W.triangle) (normalizingScale_pos hr ht).le).triangle = r ^ 3 := by
  rw [NonnegativeKernel.triangle_scale, normalizingScale_cube hr ht]
  exact div_mul_cancel₀ _ (ne_of_gt ht)

/-- Differentiation of the actual cube-root normalization, for arbitrary parameter domains. -/
theorem hasDerivWithinAt_normalizingScale {T : ℝ → ℝ} {S : Set ℝ} {r t' : ℝ}
    (hr : 0 < r) (hT : HasDerivWithinAt T t' S 0) (hT0 : T 0 = r ^ 3) :
    HasDerivWithinAt (fun s => normalizingScale r (T s)) (-t' / (3 * r ^ 3)) S 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hTnz : T 0 ≠ 0 := by rw [hT0]; positivity
  have hd := ((hasDerivWithinAt_const (0 : ℝ) S (r ^ 3)).div hT hTnz).rpow_const
    (p := (1/3 : ℝ)) (Or.inl (div_ne_zero (pow_ne_zero _ hr0) hTnz))
  rw [hT0] at hd
  convert hd using 1
  simp only [Pi.div_apply, hT0, div_self (pow_ne_zero 3 hr0), Real.one_rpow, mul_one, zero_mul, zero_sub]
  field_simp

/-- The scaling identity expresses the restored cost as a scalar function,
which is defined even away from the neighborhood where normalization is used. -/
def restoredCost (r : ℝ) (W : ℝ → NonnegativeKernel) (s : ℝ) : ℝ :=
  let lam := normalizingScale r (W s).triangle
  lam * (W s).cost + (lam * Real.log lam) * (W s).edgeDensity + 1 - lam

theorem restoredCost_eq_scale (W : ℝ → NonnegativeKernel) {r s : ℝ}
    (hr : 0 < r) (ht : 0 < (W s).triangle) :
    restoredCost r W s =
      ((W s).scale (normalizingScale r (W s).triangle) (normalizingScale_pos hr ht).le).cost := by
  rw [NonnegativeKernel.cost_scale _ _ (normalizingScale_pos hr ht)]
  rfl

theorem restoredCost_zero {U : Graphon} {r : ℝ} (hr : r ∈ Ioo 0 1)
    (hU : IsMinimizer r U) {W : ℝ → NonnegativeKernel}
    (hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun) : restoredCost r W 0 = SparseLowerTail.cost U := by
  have ht0 : (W 0).triangle = r ^ 3 :=
    (NonnegativeKernel.triangle_congr_ae (V := NonnegativeKernel.ofGraphon U) hW0).trans
      (minimizer_triangle_eq hr hU)
  have hF0 : (W 0).cost = SparseLowerTail.cost U :=
    NonnegativeKernel.cost_congr_ae (V := NonnegativeKernel.ofGraphon U) hW0
  simp [restoredCost, ht0, normalizingScale_self hr.1, hF0]

/-- Exact derivative computation in `s3:rescale`, valid also for one-sided derivatives. -/
theorem hasDerivWithinAt_restoredCost {U : Graphon} {r : ℝ} (hr : r ∈ Ioo 0 1)
    (hU : IsMinimizer r U) {W : ℝ → NonnegativeKernel} {S : Set ℝ} {F' e' t' : ℝ}
    (hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun)
    (hF : HasDerivWithinAt (fun s => (W s).cost) F' S 0)
    (he : HasDerivWithinAt (fun s => (W s).edgeDensity) e' S 0)
    (ht : HasDerivWithinAt (fun s => (W s).triangle) t' S 0) :
    HasDerivWithinAt (restoredCost r W) (F' + graphonMultiplier U r / 3 * t') S 0 := by
  have ht0 : (W 0).triangle = r ^ 3 :=
    (NonnegativeKernel.triangle_congr_ae (V := NonnegativeKernel.ofGraphon U) hW0).trans
      (minimizer_triangle_eq hr hU)
  have hF0 : (W 0).cost = SparseLowerTail.cost U :=
    NonnegativeKernel.cost_congr_ae (V := NonnegativeKernel.ofGraphon U) hW0
  have he0 : (W 0).edgeDensity = SparseLowerTail.edgeDensity U :=
    NonnegativeKernel.edgeDensity_congr_ae (V := NonnegativeKernel.ofGraphon U) hW0
  have hl := hasDerivWithinAt_normalizingScale hr.1 ht ht0
  have hl0 : normalizingScale r (W 0).triangle = 1 := by rw [ht0, normalizingScale_self hr.1]
  have hlog := (Real.hasDerivAt_mul_log (show normalizingScale r (W 0).triangle ≠ 0 by rw [hl0]; norm_num)).comp_hasDerivWithinAt 0 hl
  have hd := (((hl.mul hF).add (hlog.mul he)).add_const 1).sub hl
  convert hd using 1
  simp only [Function.comp_apply, hl0, hF0, he0, Real.log_one, zero_add, one_mul, mul_zero, zero_mul, add_zero]
  unfold graphonMultiplier
  field_simp
  ring

/-- Minimality of the normalized path, obtained from actual kernel truncation. -/
theorem restoredCost_isLocalMinOn {U : Graphon} {r : ℝ} (hr : r ∈ Ioo 0 1)
    (hU : IsMinimizer r U) {W : ℝ → NonnegativeKernel} {S : Set ℝ}
    (hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun)
    (ht : ContinuousWithinAt (fun s => (W s).triangle) S 0) :
    IsLocalMinOn (restoredCost r W) S 0 := by
  have ht0 : (W 0).triangle = r ^ 3 :=
    (NonnegativeKernel.triangle_congr_ae (V := NonnegativeKernel.ofGraphon U) hW0).trans
      (minimizer_triangle_eq hr hU)
  have hp : 0 < (W 0).triangle := by rw [ht0]; exact pow_pos hr.1 _
  have hpos : ∀ᶠ s in 𝓝[S] 0, 0 < (W s).triangle := ht (Ioi_mem_nhds hp)
  change ∀ᶠ s in 𝓝[S] 0, restoredCost r W 0 ≤ restoredCost r W s
  filter_upwards [hpos] with s hs
  rw [restoredCost_zero hr hU hW0, restoredCost_eq_scale W hr.1 hs]
  exact NonnegativeKernel.minimizer_cost_le hU _ (triangle_normalized (W s) hr.1 hs).le

/-- One-sided Fermat inequality at the left endpoint, proved via the positive tangent cone. -/
theorem right_derivative_nonneg_of_localMin {f : ℝ → ℝ} {f' : ℝ}
    (hmin : IsLocalMinOn f (Ici 0) 0) (hd : HasDerivWithinAt f f' (Ici 0) 0) : 0 ≤ f' := by
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    apply one_mem_posTangentConeAt_iff_frequently.mpr
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    exact hx.le
  have h := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt hcone
  simpa using h

/-- `s3:rescale`, right-sided form. Paths are represented on all ℝ, but only their
values and derivatives on the nonnegative side of zero enter the statement. -/
theorem rescaling_firstVariation_right {U : Graphon} {r : ℝ} (hr : r ∈ Ioo 0 1)
    (hU : IsMinimizer r U) {W : ℝ → NonnegativeKernel} {F' e' t' : ℝ}
    (hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun)
    (hF : HasDerivWithinAt (fun s => (W s).cost) F' (Ici 0) 0)
    (he : HasDerivWithinAt (fun s => (W s).edgeDensity) e' (Ici 0) 0)
    (ht : HasDerivWithinAt (fun s => (W s).triangle) t' (Ici 0) 0) :
    0 ≤ F' + graphonMultiplier U r / 3 * t' :=
  right_derivative_nonneg_of_localMin
    (restoredCost_isLocalMinOn hr hU hW0 ht.continuousWithinAt)
    (hasDerivWithinAt_restoredCost hr hU hW0 hF he ht)

/-- `s3:rescale`, two-sided form: the restored cost has vanishing derivative. -/
theorem rescaling_firstVariation {U : Graphon} {r : ℝ} (hr : r ∈ Ioo 0 1)
    (hU : IsMinimizer r U) {W : ℝ → NonnegativeKernel} {F' e' t' : ℝ}
    (hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun)
    (hF : HasDerivAt (fun s => (W s).cost) F' 0)
    (he : HasDerivAt (fun s => (W s).edgeDensity) e' 0)
    (ht : HasDerivAt (fun s => (W s).triangle) t' 0) :
    F' + graphonMultiplier U r / 3 * t' = 0 := by
  have hm := restoredCost_isLocalMinOn (S := univ) hr hU hW0 ht.continuousAt.continuousWithinAt
  have hd := hasDerivWithinAt_restoredCost (S := univ) hr hU hW0
    hF.hasDerivWithinAt he.hasDerivWithinAt ht.hasDerivWithinAt
  have hm' : IsLocalMin (restoredCost r W) 0 := by simpa [IsLocalMinOn, IsLocalMin] using hm
  exact hm'.hasDerivAt_eq_zero (hasDerivWithinAt_univ.mp hd)

/-- `s3:rescale` exactly on the manuscript's interval `[0,c]`. -/
theorem rescaling_firstVariation_right_interval {U : Graphon} {r c : ℝ}
    (hr : r ∈ Ioo 0 1) (hc : 0 < c) (hU : IsMinimizer r U)
    {W : ℝ → NonnegativeKernel} {F' e' t' : ℝ}
    (hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun)
    (hF : HasDerivWithinAt (fun s => (W s).cost) F' (Icc 0 c) 0)
    (he : HasDerivWithinAt (fun s => (W s).edgeDensity) e' (Icc 0 c) 0)
    (ht : HasDerivWithinAt (fun s => (W s).triangle) t' (Icc 0 c) 0) :
    0 ≤ F' + graphonMultiplier U r / 3 * t' := by
  have hm := restoredCost_isLocalMinOn hr hU hW0 ht.continuousWithinAt
  have hd := hasDerivWithinAt_restoredCost hr hU hW0 hF he ht
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) c) 0 := by
    apply one_mem_posTangentConeAt_iff_frequently.mpr
    apply Eventually.frequently
    have hu : ∀ᶠ x : ℝ in 𝓝[>] 0, x < c :=
      (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hu] with x hx hxc
    exact ⟨le_of_lt hx, hxc.le⟩
  have h := hm.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt hcone
  simpa using h

/-- `s3:rescale` exactly on the manuscript's interval `[-c,c]`. -/
theorem rescaling_firstVariation_interval {U : Graphon} {r c : ℝ}
    (hr : r ∈ Ioo 0 1) (hc : 0 < c) (hU : IsMinimizer r U)
    {W : ℝ → NonnegativeKernel} {F' e' t' : ℝ}
    (hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun)
    (hF : HasDerivWithinAt (fun s => (W s).cost) F' (Icc (-c) c) 0)
    (he : HasDerivWithinAt (fun s => (W s).edgeDensity) e' (Icc (-c) c) 0)
    (ht : HasDerivWithinAt (fun s => (W s).triangle) t' (Icc (-c) c) 0) :
    F' + graphonMultiplier U r / 3 * t' = 0 := by
  have hI : Icc (-c) c ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_neg_of_pos hc) hc
  exact rescaling_firstVariation hr hU hW0
    (hF.hasDerivAt hI) (he.hasDerivAt hI) (ht.hasDerivAt hI)

end Section04
end SparseLowerTail

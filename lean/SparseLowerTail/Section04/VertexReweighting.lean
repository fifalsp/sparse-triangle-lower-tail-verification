import SparseLowerTail.Section08.GraphonIntegration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Vertex reweighting is realized by a genuine graphon on the original probability space.
The only external input, `UniformSampling`, is the classical inverse-transform sampling
 theorem: any Borel probability measure on ℝ is the pushforward of uniform measure on
[0,1] by a measurable map. It is an explicit argument, not a new axiom.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace SparseLowerTail.Section04

/-- Classical inverse-transform sampling, used solely to realize a change of vertex law. -/
def UniformSampling : Prop := ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
  ∃ Q : ℝ → ℝ, MeasurePreserving Q unitMeasure ν

/-- A bounded nonnegative density with total mass one. -/
structure VertexWeight where
  toFun : ℝ → ℝ
  bounded : BoundedObservable unitMeasure toFun
  nonneg : ∀ᵐ x ∂unitMeasure, 0 ≤ toFun x
  mass : ∫ x, toFun x ∂unitMeasure = 1

instance : CoeFun VertexWeight (fun _ => ℝ → ℝ) := ⟨VertexWeight.toFun⟩

namespace VertexWeight

def measure (w : VertexWeight) : Measure ℝ :=
  unitMeasure.withDensity (fun x => ENNReal.ofReal (w x))

instance (w : VertexWeight) : IsProbabilityMeasure w.measure := by
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal w.bounded.integrable w.nonneg, w.mass]
  norm_num

theorem absolutelyContinuous (w : VertexWeight) : w.measure ≪ unitMeasure :=
  withDensity_absolutelyContinuous _ _

def sampler (hSampling : UniformSampling) (w : VertexWeight) : ℝ → ℝ :=
  Classical.choose (hSampling w.measure inferInstance)

theorem sampler_preserving (hSampling : UniformSampling) (w : VertexWeight) :
    MeasurePreserving (w.sampler hSampling) unitMeasure w.measure :=
  Classical.choose_spec (hSampling w.measure inferInstance)

theorem sampler_qmp (hSampling : UniformSampling) (w : VertexWeight) :
    QuasiMeasurePreserving (w.sampler hSampling) unitMeasure unitMeasure := by
  refine ⟨(w.sampler_preserving hSampling).measurable, ?_⟩
  rw [(w.sampler_preserving hSampling).map_eq]
  exact w.absolutelyContinuous

theorem integral_pair (w : VertexWeight) (f : ℝ × ℝ → ℝ) :
    ∫ p, f p ∂w.measure.prod w.measure =
      ∫ p, w p.1 * w p.2 * f p ∂squareMeasure := by
  have hm := w.bounded.measurable.ennreal_ofReal
  have hm2 := (hm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
    (hm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  dsimp only [Function.comp_def] at hm2
  rw [measure, prod_withDensity₀ hm hm,
    integral_withDensity_eq_integral_toReal_smul₀ hm2]
  · apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae w.nonneg,
      Measure.quasiMeasurePreserving_snd.ae w.nonneg] with p hp hq
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

theorem integral_triple (w : VertexWeight) (f : ℝ × (ℝ × ℝ) → ℝ) :
    ∫ p, f p ∂w.measure.prod (w.measure.prod w.measure) =
      ∫ p, w p.1 * w p.2.1 * w p.2.2 * f p ∂cubeMeasure := by
  have hm := w.bounded.measurable.ennreal_ofReal
  have hm2 := (hm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
    (hm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hm3 := (hm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
    (hm2.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  dsimp only [Function.comp_def] at hm2 hm3
  rw [measure, prod_withDensity₀ hm hm, prod_withDensity₀ hm hm2,
    integral_withDensity_eq_integral_toReal_smul₀ hm3]
  · apply integral_congr_ae
    have hnn : ∀ᵐ p ∂squareMeasure, 0 ≤ w p.1 ∧ 0 ≤ w p.2 := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae w.nonneg,
        Measure.quasiMeasurePreserving_snd.ae w.nonneg] with p hp hq
      exact ⟨hp,hq⟩
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae w.nonneg,
      Measure.quasiMeasurePreserving_snd.ae hnn] with p hp hq
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp,
      ENNReal.toReal_ofReal hq.1, ENNReal.toReal_ofReal hq.2, smul_eq_mul]
    ring
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

end VertexWeight

private theorem integral_preserving_real {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {Q : α → β}
    (hQ : MeasurePreserving Q μ ν) {f : β → ℝ} (hf : AEStronglyMeasurable f ν) :
    ∫ x, f (Q x) ∂μ = ∫ y, f y ∂ν := by
  rw [← hQ.map_eq] at hf ⊢
  exact (integral_map hQ.measurable.aemeasurable hf).symm

/-- Pull back along a sampled vertex law; this is an actual graphon. -/
def reweightedGraphon (hSampling : UniformSampling) (U : Graphon) (w : VertexWeight) :
    Graphon where
  toFun p := U (w.sampler hSampling p.1, w.sampler hSampling p.2)
  measurable := U.measurable.comp_quasiMeasurePreserving
    (MeasureTheory.QuasiMeasurePreserving.prodMap
      (w.sampler_qmp hSampling) (w.sampler_qmp hSampling))
  symmetric := (MeasureTheory.QuasiMeasurePreserving.prodMap
      (w.sampler_qmp hSampling) (w.sampler_qmp hSampling)).ae U.symmetric
  bounded := (MeasureTheory.QuasiMeasurePreserving.prodMap
      (w.sampler_qmp hSampling) (w.sampler_qmp hSampling)).ae U.bounded

theorem reweighted_integral_pair (hSampling : UniformSampling) (w : VertexWeight)
    {f : ℝ × ℝ → ℝ} (hf : AEStronglyMeasurable f squareMeasure) :
    ∫ p, f (w.sampler hSampling p.1, w.sampler hSampling p.2) ∂squareMeasure =
      ∫ p, w p.1 * w p.2 * f p ∂squareMeasure := by
  rw [← w.integral_pair f]
  exact integral_preserving_real ((w.sampler_preserving hSampling).prod
    (w.sampler_preserving hSampling))
    (hf.mono_ac (w.absolutelyContinuous.prod w.absolutelyContinuous))

theorem reweighted_integral_triple (hSampling : UniformSampling) (w : VertexWeight)
    {f : ℝ × (ℝ × ℝ) → ℝ} (hf : AEStronglyMeasurable f cubeMeasure) :
    ∫ p : ℝ × (ℝ × ℝ), f (w.sampler hSampling p.1,
        w.sampler hSampling p.2.1, w.sampler hSampling p.2.2) ∂cubeMeasure =
      ∫ p, w p.1 * w p.2.1 * w p.2.2 * f p ∂cubeMeasure := by
  rw [← w.integral_triple f]
  exact integral_preserving_real ((w.sampler_preserving hSampling).prod
    ((w.sampler_preserving hSampling).prod (w.sampler_preserving hSampling)))
    (hf.mono_ac (w.absolutelyContinuous.prod
      (w.absolutelyContinuous.prod w.absolutelyContinuous)))

theorem reweighted_edge (hSampling : UniformSampling) (U : Graphon) (w : VertexWeight) :
    edgeDensity (reweightedGraphon hSampling U w) =
      ∫ p, w p.1 * w p.2 * U p ∂squareMeasure :=
  reweighted_integral_pair hSampling w U.measurable.aestronglyMeasurable

theorem reweighted_cost (hSampling : UniformSampling) (U : Graphon) (w : VertexWeight) :
    cost (reweightedGraphon hSampling U w) =
      ∫ p, w p.1 * w p.2 * entropy (U p) ∂squareMeasure :=
  reweighted_integral_pair hSampling w (cost_integrable U).aestronglyMeasurable

theorem reweighted_triangle (hSampling : UniformSampling) (U : Graphon) (w : VertexWeight) :
    triangle (reweightedGraphon hSampling U w) =
      ∫ p : ℝ × (ℝ × ℝ), w p.1 * w p.2.1 * w p.2.2 *
        (U (p.1,p.2.1) * U (p.2.1,p.2.2) * U (p.1,p.2.2)) ∂cubeMeasure :=
  reweighted_integral_triple hSampling w (triangle_integrable U).aestronglyMeasurable

/-- The bounded mean-zero perturbation `1+sψ` is a probability density. -/
def variationWeight (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0)
    (s : ℝ) (hs : |s| ≤ 1/2) : VertexWeight where
  toFun x := 1+s*ψ x
  bounded := (BoundedObservable.const 1).add
    ((⟨hψ, 1, by norm_num, by simpa only [Real.norm_eq_abs] using hbound⟩ :
      BoundedObservable unitMeasure ψ).const_mul s)
  nonneg := by
    filter_upwards [hbound] with x hx
    have hmul : |s*ψ x| ≤ 1/2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg (ψ x)]
    linarith [neg_abs_le (s*ψ x)]
  mass := by
    have hi : Integrable ψ unitMeasure :=
      (⟨hψ, 1, by norm_num, by simpa only [Real.norm_eq_abs] using hbound⟩ :
        BoundedObservable unitMeasure ψ).integrable
    rw [integral_add (integrable_const 1) (hi.const_mul s), integral_const_mul, hmean]
    simp

/-- A total graphon path, equal to U at zero and realized by sampling the perturbed
vertex measure in the prescribed interval. Values outside that interval are irrelevant. -/
def vertexVariation (hSampling : UniformSampling) (U : Graphon) (ψ : ℝ → ℝ)
    (hψ : AEMeasurable ψ unitMeasure) (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1)
    (hmean : ∫ x, ψ x ∂unitMeasure = 0) (s : ℝ) : Graphon :=
  if s = 0 then U else if hs : |s| ≤ 1/2 then
    reweightedGraphon hSampling U (variationWeight ψ hψ hbound hmean s hs) else U

@[simp] theorem vertexVariation_zero (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0) :
    vertexVariation hSampling U ψ hψ hbound hmean 0 = U := by
  simp [vertexVariation]

theorem vertexVariation_edge (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0)
    {s : ℝ} (hs : |s| ≤ 1/2) :
    edgeDensity (vertexVariation hSampling U ψ hψ hbound hmean s) =
      ∫ p, (1+s*ψ p.1)*(1+s*ψ p.2)*U p ∂squareMeasure := by
  by_cases hs0 : s = 0
  · subst s; simp [edgeDensity]
  · simp only [vertexVariation, if_neg hs0, dif_pos hs]
    exact reweighted_edge hSampling U (variationWeight ψ hψ hbound hmean s hs)

theorem vertexVariation_cost (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0)
    {s : ℝ} (hs : |s| ≤ 1/2) :
    cost (vertexVariation hSampling U ψ hψ hbound hmean s) =
      ∫ p, (1+s*ψ p.1)*(1+s*ψ p.2)*entropy (U p) ∂squareMeasure := by
  by_cases hs0 : s = 0
  · subst s; simp [cost]
  · simp only [vertexVariation, if_neg hs0, dif_pos hs]
    exact reweighted_cost hSampling U (variationWeight ψ hψ hbound hmean s hs)

theorem vertexVariation_triangle (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0)
    {s : ℝ} (hs : |s| ≤ 1/2) :
    triangle (vertexVariation hSampling U ψ hψ hbound hmean s) =
      ∫ p : ℝ × (ℝ × ℝ), (1+s*ψ p.1)*(1+s*ψ p.2.1)*(1+s*ψ p.2.2)*
        (U (p.1,p.2.1)*U (p.2.1,p.2.2)*U (p.1,p.2.2)) ∂cubeMeasure := by
  by_cases hs0 : s = 0
  · subst s; simp [triangle]
  · simp only [vertexVariation, if_neg hs0, dif_pos hs]
    exact reweighted_triangle hSampling U (variationWeight ψ hψ hbound hmean s hs)

end SparseLowerTail.Section04

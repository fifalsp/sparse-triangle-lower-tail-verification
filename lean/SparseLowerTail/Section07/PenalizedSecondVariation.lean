import SparseLowerTail.Section07.PenalizedMultiplier
import SparseLowerTail.Section04.VertexIdentity

/-! The vertex second variation in `lem:penalized`. Symmetric evaluations at
±ε cancel the odd polynomial terms exactly. The only external input is the
classical realization of weighted probability measures by uniform sampling. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

/-- Symmetric two-vertex weighting isolates its quadratic coefficient. -/
theorem pair_weight_symmetric_sum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f u v : α → ℝ}
    (hf : BoundedObservable μ f) (hu : BoundedObservable μ u)
    (hv : BoundedObservable μ v) (s : ℝ) :
    (∫ x, f x*(1+s*u x)*(1+s*v x) ∂μ)+
      (∫ x, f x*(1-s*u x)*(1-s*v x) ∂μ) =
      2*(∫ x, f x ∂μ)+2*s^2*(∫ x, f x*u x*v x ∂μ) := by
  have hp := ((hf.mul ((hu.const_mul s).add (BoundedObservable.const 1))).mul
    ((hv.const_mul s).add (BoundedObservable.const 1))).integrable
  have hn := ((hf.mul ((hu.const_mul (-s)).add (BoundedObservable.const 1))).mul
    ((hv.const_mul (-s)).add (BoundedObservable.const 1))).integrable
  have hp' : Integrable (fun x => f x*(1+s*u x)*(1+s*v x)) μ := by
    convert hp using 1
    ext x
    ring
  have hn' : Integrable (fun x => f x*(1-s*u x)*(1-s*v x)) μ := by
    convert hn using 1
    ext x
    ring
  rw [← integral_add hp' hn', ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hf.integrable.const_mul 2) (((hf.mul hu).mul hv).integrable.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- Symmetric three-vertex weighting also cancels its cubic term. -/
theorem triple_weight_symmetric_sum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f u v w : α → ℝ}
    (hf : BoundedObservable μ f) (hu : BoundedObservable μ u)
    (hv : BoundedObservable μ v) (hw : BoundedObservable μ w) (s : ℝ) :
    (∫ x, f x*(1+s*u x)*(1+s*v x)*(1+s*w x) ∂μ)+
      (∫ x, f x*(1-s*u x)*(1-s*v x)*(1-s*w x) ∂μ) =
      2*(∫ x, f x ∂μ)+2*s^2*(∫ x, f x*(u x*v x+u x*w x+v x*w x) ∂μ) := by
  have hi (t : ℝ) : Integrable (fun x => f x*(1+t*u x)*(1+t*v x)*(1+t*w x)) μ := by
    convert (((hf.mul ((hu.const_mul t).add (BoundedObservable.const 1))).mul
      ((hv.const_mul t).add (BoundedObservable.const 1))).mul
      ((hw.const_mul t).add (BoundedObservable.const 1))).integrable using 1
    ext x
    ring
  have hn : Integrable (fun x => f x*(1-s*u x)*(1-s*v x)*(1-s*w x)) μ := by
    convert hi (-s) using 1
    ext x
    ring
  have hq := (hf.mul (((hu.mul hv).add (hu.mul hw)).add (hv.mul hw))).integrable
  rw [← integral_add (hi s) hn, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hf.integrable.const_mul 2) (hq.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- Cyclic symmetry identifies all three quadratic triangle coefficients. -/
theorem integral_triangle_vertex_pair_cycle (U : Graphon) (ψ : ℝ → ℝ) :
    (∫ p, tiltTriangleWeight U p*(ψ p.1.2*ψ p.2) ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2) ∂TriangleIntegration.tripleMeasure) ∧
    (∫ p, tiltTriangleWeight U p*(ψ p.1.1*ψ p.2) ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2) ∂TriangleIntegration.tripleMeasure) := by
  have hw : ∀ᵐ p ∂TriangleIntegration.tripleMeasure,
      tiltTriangleWeight U (TriangleIntegration.cycle p)=tiltTriangleWeight U p := by
    filter_upwards [TriangleIntegration.edgeZ_qmp.ae U.symmetric,
      TriangleIntegration.edgeX_qmp.ae U.symmetric] with p hz hx
    change U (p.2,p.1.1)=U (p.1.1,p.2) at hz
    change U (p.1.2,p.1.1)=U (p.1.1,p.1.2) at hx
    change U (p.1.2,p.2)*U (p.2,p.1.1)*U (p.1.2,p.1.1)=
      U (p.1.1,p.1.2)*U (p.1.2,p.2)*U (p.1.1,p.2)
    rw [hz,hx]
    ring
  have h₁ : (∫ p, tiltTriangleWeight U p*(ψ p.1.2*ψ p.2) ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2) ∂TriangleIntegration.tripleMeasure) := by
    calc
      _ = ∫ p, tiltTriangleWeight U (TriangleIntegration.cycle p)*
          (ψ (TriangleIntegration.cycle p).1.1*ψ (TriangleIntegration.cycle p).1.2)
          ∂TriangleIntegration.tripleMeasure := by
        apply integral_congr_ae
        filter_upwards [hw] with p hp
        rw [hp]
        rfl
      _ = _ := TriangleIntegration.cycle_preserving.integral_comp
        TriangleIntegration.cycle.measurableEmbedding (fun p => tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2))
  refine ⟨h₁,?_⟩
  calc
    _ = ∫ p, tiltTriangleWeight U (TriangleIntegration.cycle p)*
        (ψ (TriangleIntegration.cycle p).1.2*ψ (TriangleIntegration.cycle p).2)
        ∂TriangleIntegration.tripleMeasure := by
      apply integral_congr_ae
      filter_upwards [hw] with p hp
      rw [hp]
      change _=tiltTriangleWeight U p*(ψ p.2*ψ p.1.1)
      ring
    _ = ∫ p, tiltTriangleWeight U p*(ψ p.1.2*ψ p.2) ∂TriangleIntegration.tripleMeasure :=
      TriangleIntegration.cycle_preserving.integral_comp
        TriangleIntegration.cycle.measurableEmbedding (fun p => tiltTriangleWeight U p*(ψ p.1.2*ψ p.2))
    _ = _ := h₁

/-- Fubini identifies the quadratic coefficient with the codegree kernel. -/
theorem integral_triangle_vertex_pair (U : Graphon) {ψ : ℝ → ℝ}
    (hψ : BoundedObservable unitMeasure ψ) :
    (∫ p, tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2+ψ p.1.1*ψ p.2+ψ p.1.2*ψ p.2)
      ∂TriangleIntegration.tripleMeasure) =
      3*(∫ p, U p*codegree U p.1 p.2*(ψ p.1*ψ p.2) ∂squareMeasure) := by
  have hx := hψ.comp (Measure.quasiMeasurePreserving_fst.comp TriangleIntegration.edgeX_qmp)
  have hy := hψ.comp (Measure.quasiMeasurePreserving_snd.comp TriangleIntegration.edgeX_qmp)
  have hz := hψ.comp (Measure.quasiMeasurePreserving_snd (μ := squareMeasure) (ν := unitMeasure))
  dsimp only [Function.comp_def] at hx hy
  have h₁ := ((tiltTriangleWeight_bounded U).mul (hx.mul hy)).integrable
  have h₂ := ((tiltTriangleWeight_bounded U).mul (hx.mul hz)).integrable
  have h₃ := ((tiltTriangleWeight_bounded U).mul (hy.mul hz)).integrable
  have h₁₂ : Integrable (fun p => tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2)+
      tiltTriangleWeight U p*(ψ p.1.1*ψ p.2)) TriangleIntegration.tripleMeasure := h₁.add h₂
  have hcycle := integral_triangle_vertex_pair_cycle U ψ
  have hmain : (∫ p, tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2)
      ∂TriangleIntegration.tripleMeasure) =
      ∫ p, U p*codegree U p.1 p.2*(ψ p.1*ψ p.2) ∂squareMeasure := by
    calc
      _ = ∫ p, (U p.1*(ψ p.1.1*ψ p.1.2))*TriangleIntegration.Y U p*TriangleIntegration.Z U p
          ∂TriangleIntegration.tripleMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by unfold tiltTriangleWeight TriangleIntegration.X; ring
      _ = ∫ p, (U p*(ψ p.1*ψ p.2))*codegree U p.1 p.2 ∂squareMeasure :=
        TriangleIntegration.integral_test_codegree U
          ((graphon_boundedObservable U).mul ((hψ.comp Measure.quasiMeasurePreserving_fst).mul
            (hψ.comp Measure.quasiMeasurePreserving_snd)))
      _ = _ := by apply integral_congr_ae; exact Eventually.of_forall fun p => by ring
  rw [show (fun p => tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2+ψ p.1.1*ψ p.2+ψ p.1.2*ψ p.2)) =
    (fun p => (tiltTriangleWeight U p*(ψ p.1.1*ψ p.1.2)+tiltTriangleWeight U p*(ψ p.1.1*ψ p.2))+
      tiltTriangleWeight U p*(ψ p.1.2*ψ p.2)) by funext p; ring,
    integral_add h₁₂ h₃, integral_add h₁ h₂, hcycle.1,hcycle.2,hmain]
  ring

/-- The actual triangle variation in left-associated product coordinates. -/
theorem vertexVariation_triangle_left (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure, |ψ x|≤1) (hm : ∫ x, ψ x ∂unitMeasure=0)
    {s : ℝ} (hs : |s|≤1/2) :
    triangle (vertexVariation hSampling U ψ hψ hb hm s)=
      ∫ p, tiltTriangleWeight U p*(1+s*ψ p.1.1)*(1+s*ψ p.1.2)*(1+s*ψ p.2)
        ∂TriangleIntegration.tripleMeasure := by
  rw [vertexVariation_triangle hSampling U ψ hψ hb hm hs]
  rw [← (measurePreserving_prodAssoc unitMeasure unitMeasure unitMeasure).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun p : ℝ × (ℝ × ℝ) => (1+s*ψ p.1)*(1+s*ψ p.2.1)*(1+s*ψ p.2.2)*
      (U (p.1,p.2.1)*U (p.2.1,p.2.2)*U (p.1,p.2.2)))]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    change (1+s*ψ p.1.1)*(1+s*ψ p.1.2)*(1+s*ψ p.2)*
      (U (p.1.1,p.1.2)*U (p.1.2,p.2)*U (p.1.1,p.2)) = _
    unfold tiltTriangleWeight TriangleIntegration.X TriangleIntegration.Y TriangleIntegration.Z
    ring

/-- A global penalty minimum has nonnegative quadratic vertex coefficient.
Evaluating at ±1/2 proves the second-variation inequality exactly. -/
theorem penalized_vertex_quadratic_nonneg (hSampling : UniformSampling)
    {γ : ℝ} {U : Graphon}
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W)
    {ψ : ℝ → ℝ} (hψ : AEMeasurable ψ unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure, |ψ x|≤1) (hm : ∫ x, ψ x ∂unitMeasure=0) :
    0≤(∫ p, entropy (U p)*(ψ p.1*ψ p.2) ∂squareMeasure)+
      3*γ*(∫ p, U p*codegree U p.1 p.2*(ψ p.1*ψ p.2) ∂squareMeasure) := by
  let W := vertexVariation hSampling U ψ hψ hb hm
  have hbo : BoundedObservable unitMeasure ψ := ⟨hψ,1,by norm_num,hb⟩
  have hx := hbo.comp (Measure.quasiMeasurePreserving_fst.comp TriangleIntegration.edgeX_qmp)
  have hy := hbo.comp (Measure.quasiMeasurePreserving_snd.comp TriangleIntegration.edgeX_qmp)
  have hz := hbo.comp (Measure.quasiMeasurePreserving_snd (μ := squareMeasure) (ν := unitMeasure))
  dsimp only [Function.comp_def] at hx hy
  have hc (s : ℝ) (hs : |s|≤1/2) : cost (W s)=
      ∫ p, entropy (U p)*(1+s*ψ p.1)*(1+s*ψ p.2) ∂squareMeasure := by
    rw [vertexVariation_cost hSampling U ψ hψ hb hm hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by ring
  have hcs := pair_weight_symmetric_sum (graphon_entropy_boundedObservable U)
    (hbo.comp Measure.quasiMeasurePreserving_fst) (hbo.comp Measure.quasiMeasurePreserving_snd) (1/2)
  have hts := triple_weight_symmetric_sum (tiltTriangleWeight_bounded U) hx hy hz (1/2)
  have hcminus : cost (W (-(1/2)))=
      ∫ p, entropy (U p)*(1-(1/2)*ψ p.1)*(1-(1/2)*ψ p.2) ∂squareMeasure := by
    rw [hc _ (by norm_num)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by ring
  rw [← hc _ (by norm_num),← hcminus] at hcs
  have htplus := vertexVariation_triangle_left hSampling U ψ hψ hb hm (s := 1/2) (by norm_num)
  have htminus : triangle (W (-(1/2)))=
      ∫ p, tiltTriangleWeight U p*(1-(1/2)*ψ p.1.1)*(1-(1/2)*ψ p.1.2)*(1-(1/2)*ψ p.2)
        ∂TriangleIntegration.tripleMeasure := by
    rw [vertexVariation_triangle_left hSampling U ψ hψ hb hm (by norm_num : |-(1/2:ℝ)|≤1/2)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by ring
  rw [← htplus,← htminus,integral_triangle_vertex_pair U hbo] at hts
  have htbase : (∫ p, tiltTriangleWeight U p ∂TriangleIntegration.tripleMeasure)=triangle U := by
    have hh := vertexVariation_triangle_left hSampling U ψ hψ hb hm (s := 0) (by norm_num)
    simpa only [zero_mul,add_zero,mul_one,vertexVariation_zero] using hh.symm
  rw [htbase] at hts
  have hcost : (∫ p, entropy (U p)*ψ p.1*ψ p.2 ∂squareMeasure)=
      (∫ p, entropy (U p)*(ψ p.1*ψ p.2) ∂squareMeasure) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by ring
  rw [hcost] at hcs
  change cost (W (1/2))+cost (W (-(1/2)))=2*cost U+_ at hcs
  have hp := hpen (W (1/2))
  have hn := hpen (W (-(1/2)))
  change triangle (W (1/2))+triangle (W (-(1/2)))=_ at hts
  have htsγ := congrArg (fun x : ℝ => γ*x) hts
  nlinarith [htsγ]

/-- The bounded, normalized case of `lem:penalized`: the graphon quadratic
form is nonpositive on every bounded mean-zero vertex test. -/
theorem penalized_quadratic_nonpos_unit (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W)
    {ψ : ℝ → ℝ} (hψ : AEMeasurable ψ unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure, |ψ x|≤1) (hm : ∫ x, ψ x ∂unitMeasure=0) :
    (∫ p, U p*(ψ p.1*ψ p.2) ∂squareMeasure)≤0 := by
  have h := penalized_vertex_quadratic_nonneg hSampling hpen hψ hb hm
  have hbo : BoundedObservable unitMeasure ψ := ⟨hψ,1,by norm_num,hb⟩
  have hp := (hbo.comp Measure.quasiMeasurePreserving_fst).mul
    (hbo.comp Measure.quasiMeasurePreserving_snd)
  have hc := ((graphon_entropy_boundedObservable U).mul hp).integrable
  have ht := (((graphon_boundedObservable U).mul (codegree_boundedObservable U)).mul hp).integrable
  have hu := ((graphon_boundedObservable U).mul hp).integrable
  have hμ := minimizer_multiplier_eq_three_penalty hr hγ hU hpen
  have hel := minimizer_log_equation hr hU
  rw [hμ] at hel
  have he : (∫ p, entropy (U p)*(ψ p.1*ψ p.2) ∂squareMeasure)+
      3*γ*(∫ p, U p*codegree U p.1 p.2*(ψ p.1*ψ p.2) ∂squareMeasure)=
      -(∫ p, U p*(ψ p.1*ψ p.2) ∂squareMeasure) := by
    rw [← integral_const_mul,← integral_add hc (ht.const_mul _)]
    calc
      _ = ∫ p, (ψ p.1*ψ p.2)-U p*(ψ p.1*ψ p.2) ∂squareMeasure := by
        apply integral_congr_ae
        filter_upwards [hel] with p hlog
        unfold entropy
        rw [hlog]
        ring
      _ = _ := by
        rw [integral_sub hp.integrable hu,integral_prod_mul,hm]
        ring
  rw [he] at h
  linarith

end SparseLowerTail.Section07

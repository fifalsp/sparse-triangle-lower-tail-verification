import SparseLowerTail.Section04.EulerLagrange
import SparseLowerTail.Section04.BipodalGraphon
import SparseLowerTail.Section04.VertexReweighting

/-!
# Vertex variation and the row identity

Stable manuscript anchors: `s3:expand`, `prop:vertex`, `eq:vertex`, `s3:degree`.
The algebra and variational argument are proved internally. The realization of
weighted vertex measures is supplied by the explicit classical sampling input
in `VertexReweighting`.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace SparseLowerTail.Section04

/-- Derivative of a two-vertex weighted integral. -/
theorem hasDerivAt_integral_pair_weight {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f u v : α → ℝ}
    (hf : BoundedObservable μ f) (hu : BoundedObservable μ u) (hv : BoundedObservable μ v) :
    HasDerivAt (fun s : ℝ => ∫ x, f x * (1+s*u x) * (1+s*v x) ∂μ)
      (∫ x, f x * (u x+v x) ∂μ) 0 := by
  have hi₁ := (hf.mul (hu.add hv)).integrable
  have hi₂ := ((hf.mul hu).mul hv).integrable
  have he (s : ℝ) : (∫ x, f x * (1+s*u x) * (1+s*v x) ∂μ) =
      (∫ x, f x ∂μ) + s * (∫ x, f x*(u x+v x) ∂μ) +
        s^2 * (∫ x, f x*u x*v x ∂μ) := by
    have hi : Integrable (fun x => f x + s*(f x*(u x+v x))) μ :=
      hf.integrable.add (hi₁.const_mul s)
    calc
      _ = ∫ x, (f x + s*(f x*(u x+v x))) + s^2*(f x*u x*v x) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [integral_add hi (hi₂.const_mul _), integral_add hf.integrable (hi₁.const_mul _)]
        simp only [integral_const_mul]
  simp_rw [he]
  convert ((hasDerivAt_const (0 : ℝ) (∫ x, f x ∂μ)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (∫ x, f x*(u x+v x) ∂μ))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ x, f x*u x*v x ∂μ)) using 1
  simp

/-- Derivative of a three-vertex weighted integral. -/
theorem hasDerivAt_integral_triple_weight {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f u v w : α → ℝ}
    (hf : BoundedObservable μ f) (hu : BoundedObservable μ u)
    (hv : BoundedObservable μ v) (hw : BoundedObservable μ w) :
    HasDerivAt (fun s : ℝ => ∫ x, f x*(1+s*u x)*(1+s*v x)*(1+s*w x) ∂μ)
      (∫ x, f x*(u x+v x+w x) ∂μ) 0 := by
  let a := fun x => f x*(u x+v x+w x)
  let b := fun x => f x*(u x*v x+u x*w x+v x*w x)
  let c := fun x => f x*u x*v x*w x
  have ha : Integrable a μ := (hf.mul ((hu.add hv).add hw)).integrable
  have hb : Integrable b μ := (hf.mul (((hu.mul hv).add (hu.mul hw)).add (hv.mul hw))).integrable
  have hc : Integrable c μ := (((hf.mul hu).mul hv).mul hw).integrable
  have he (s : ℝ) : (∫ x, f x*(1+s*u x)*(1+s*v x)*(1+s*w x) ∂μ) =
      (∫ x, f x ∂μ) + s*(∫ x, a x ∂μ) + s^2*(∫ x, b x ∂μ) + s^3*(∫ x, c x ∂μ) := by
    have hfa : Integrable (fun x => f x+s*a x) μ := hf.integrable.add (ha.const_mul s)
    have hfab : Integrable (fun x => (f x+s*a x)+s^2*b x) μ := hfa.add (hb.const_mul _)
    calc
      _ = ∫ x, ((f x+s*a x)+s^2*b x)+s^3*c x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp [a,b,c]; ring
      _ = _ := by
        rw [integral_add hfab (hc.const_mul _), integral_add hfa (hb.const_mul _),
          integral_add hf.integrable (ha.const_mul _)]
        simp only [integral_const_mul]
  simp_rw [he]
  convert (((hasDerivAt_const (0 : ℝ) (∫ x, f x ∂μ)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (∫ x, a x ∂μ))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (∫ x, b x ∂μ))).add
    (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (∫ x, c x ∂μ)) using 1
  simp [a]

/-- Entropy integrated over one row. -/
def rowEntropy (U : Graphon) (x : ℝ) : ℝ := ∫ y, entropy (U (x,y)) ∂unitMeasure

/-- Degree of a vertex. -/
def rowDegree (U : Graphon) (x : ℝ) : ℝ := ∫ y, U (x,y) ∂unitMeasure

/-- Rooted triangle density. -/
def rowTriangle (U : Graphon) (x : ℝ) : ℝ :=
  ∫ y, U (x,y)*codegree U x y ∂unitMeasure

/-- The pointwise quantity whose constancy expresses vertex stationarity. -/
def vertexStationary (U : Graphon) (r x : ℝ) : ℝ :=
  2*rowEntropy U x + graphonMultiplier U r*rowTriangle U x

/-- The prescribed value of the vertex identity. -/
def vertexMean (U : Graphon) (r : ℝ) : ℝ := 2*cost U + graphonMultiplier U r*r^3

theorem rowEntropy_bounded (U : Graphon) : BoundedObservable unitMeasure (rowEntropy U) :=
  (graphon_entropy_boundedObservable U).integral_left

theorem rowDegree_bounded (U : Graphon) : BoundedObservable unitMeasure (rowDegree U) :=
  (graphon_boundedObservable U).integral_left

theorem rowTriangle_bounded (U : Graphon) : BoundedObservable unitMeasure (rowTriangle U) :=
  ((graphon_boundedObservable U).mul (codegree_boundedObservable U)).integral_left

theorem vertexStationary_bounded (U : Graphon) (r : ℝ) :
    BoundedObservable unitMeasure (vertexStationary U r) :=
  ((rowEntropy_bounded U).const_mul 2).add ((rowTriangle_bounded U).const_mul _)

theorem integral_rowEntropy (U : Graphon) : (∫ x, rowEntropy U x ∂unitMeasure) = cost U :=
  (integral_prod _ (cost_integrable U)).symm

theorem integral_rowDegree (U : Graphon) : (∫ x, rowDegree U x ∂unitMeasure) = edgeDensity U :=
  (integral_prod _ (graphon_integrable U)).symm

theorem integral_rowTriangle (U : Graphon) : (∫ x, rowTriangle U x ∂unitMeasure) = triangle U := by
  rw [triangle_eq_integral_codegree U]
  exact (integral_prod _ (((graphon_boundedObservable U).mul (codegree_boundedObservable U)).integrable)).symm

theorem integral_vertexStationary {r : ℝ} (hr : r ∈ Ioo 0 1) {U : Graphon}
    (hU : IsMinimizer r U) : (∫ x, vertexStationary U r x ∂unitMeasure) = vertexMean U r := by
  rw [show (fun x => vertexStationary U r x) =
    (fun x => 2*rowEntropy U x + graphonMultiplier U r*rowTriangle U x) from rfl,
    integral_add ((rowEntropy_bounded U).integrable.const_mul 2)
      ((rowTriangle_bounded U).integrable.const_mul _), integral_const_mul, integral_const_mul,
    integral_rowEntropy, integral_rowTriangle, minimizer_triangle_eq hr hU]
  rfl

/-- A bounded function orthogonal to every bounded mean-zero test is constant. -/
theorem ae_eq_mean_of_mean_zero_tests {g : ℝ → ℝ} (hg : BoundedObservable unitMeasure g)
    (htest : ∀ ψ : ℝ → ℝ, AEMeasurable ψ unitMeasure →
      (∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) → (∫ x, ψ x ∂unitMeasure) = 0 →
      (∫ x, ψ x*g x ∂unitMeasure) = 0) :
    ∀ᵐ x ∂unitMeasure, g x = ∫ y, g y ∂unitMeasure := by
  obtain ⟨K, hK, hgK⟩ := hg.bound
  let m := ∫ x, g x ∂unitMeasure
  let c := 1+2*K
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : |m| ≤ K := by simpa [m] using norm_integral_le_of_norm_le_const hgK
  let ψ := fun x => (g x-m)/c
  have hψ : BoundedObservable unitMeasure ψ := by
    refine ⟨(hg.measurable.sub aemeasurable_const).div_const c, 1, by norm_num, ?_⟩
    filter_upwards [hgK] with x hx
    change ‖(g x-m)/c‖ ≤ 1
    rw [norm_div, Real.norm_of_nonneg hc.le]
    apply (div_le_one hc).mpr
    have hn := norm_sub_le (g x) m
    simp only [Real.norm_eq_abs] at hx hn
    have hm' : ‖m‖ ≤ K := hm
    dsimp [c]
    linarith
  have hmean : (∫ x, ψ x ∂unitMeasure) = 0 := by
    simp only [ψ, integral_div, integral_sub hg.integrable (integrable_const m)]
    simp [m]
  have hψbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1 := by
    filter_upwards [hgK] with x hx
    change |(g x-m)/c| ≤ 1
    rw [abs_div, abs_of_pos hc]
    apply (div_le_one hc).mpr
    have hn := abs_sub (g x) m
    have hx' : |g x| ≤ K := hx
    dsimp [c]
    linarith
  have hv := htest ψ hψ.measurable hψbound hmean
  have hsub : Integrable (fun x => g x-m) unitMeasure := hg.integrable.sub (integrable_const m)
  have hsquare : Integrable (fun x => (g x-m)^2) unitMeasure := by
    have hb := hg.add ((BoundedObservable.const m).const_mul (-1))
    convert (hb.mul hb).integrable using 1
    funext x
    dsimp
    ring
  have hzero : (∫ x, (g x-m)^2 ∂unitMeasure) = 0 := by
    have hi : Integrable (fun x => ψ x*g x - m*ψ x) unitMeasure :=
      (hψ.mul hg).integrable.sub (hψ.integrable.const_mul m)
    have he : (∫ x, (g x-m)^2 ∂unitMeasure) =
        c*((∫ x, ψ x*g x ∂unitMeasure)-m*(∫ x, ψ x ∂unitMeasure)) := by
      calc
        _ = ∫ x, c*(ψ x*g x-m*ψ x) ∂unitMeasure := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp [ψ]; field_simp
        _ = c*(∫ x, ψ x*g x-m*ψ x ∂unitMeasure) := integral_const_mul _ _
        _ = _ := by
          rw [integral_sub (hψ.mul hg).integrable (hψ.integrable.const_mul m), integral_const_mul]
    rw [he, hv, hmean]
    ring
  have h := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsquare).mp hzero
  filter_upwards [h] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)


/-- Fubini for a bounded vertex test against a bounded pair observable. -/
theorem integral_vertex_test_pair {f : ℝ × ℝ → ℝ} {ψ : ℝ → ℝ}
    (hf : BoundedObservable squareMeasure f) (hψ : BoundedObservable unitMeasure ψ) :
    (∫ p, f p*ψ p.1 ∂squareMeasure) =
      ∫ x, ψ x*(∫ y, f (x,y) ∂unitMeasure) ∂unitMeasure := by
  have ht := hf.mul (hψ.comp Measure.quasiMeasurePreserving_fst)
  rw [integral_prod _ ht.integrable]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∫ y, f (x,y)*ψ x ∂unitMeasure) = _
    rw [integral_mul_const]
    ring

/-- Symmetry reduces the two vertex contributions to twice the row integral. -/
theorem integral_pair_vertex_direction {f : ℝ × ℝ → ℝ} {ψ : ℝ → ℝ}
    (hf : BoundedObservable squareMeasure f) (hψ : BoundedObservable unitMeasure ψ)
    (hs : ∀ᵐ p ∂squareMeasure, f p.swap = f p) :
    (∫ p, f p*(ψ p.1+ψ p.2) ∂squareMeasure) =
      2*(∫ x, ψ x*(∫ y, f (x,y) ∂unitMeasure) ∂unitMeasure) := by
  have h₁ := (hf.mul (hψ.comp Measure.quasiMeasurePreserving_fst)).integrable
  have h₂ := (hf.mul (hψ.comp Measure.quasiMeasurePreserving_snd)).integrable
  have he : (∫ p, f p*ψ p.2 ∂squareMeasure) = ∫ p, f p*ψ p.1 ∂squareMeasure := by
    calc
      _ = ∫ p, f p.swap*ψ p.swap.1 ∂squareMeasure := by
        apply integral_congr_ae
        filter_upwards [hs] with p hp
        simp only [Prod.fst_swap, hp]
      _ = _ := Measure.measurePreserving_swap.integral_comp
        MeasurableEquiv.prodComm.measurableEmbedding (fun p => f p*ψ p.1)
  rw [show (fun p => f p*(ψ p.1+ψ p.2)) =
    (fun p => f p*ψ p.1+f p*ψ p.2) by funext p; ring, integral_add h₁ h₂, he,
    integral_vertex_test_pair hf hψ]
  ring

/-- Cyclic equality of the three vertex contributions to a triangle. -/
theorem integral_triangle_vertex_cycle (U : Graphon) (ψ : ℝ → ℝ) :
    (∫ p, tiltTriangleWeight U p*ψ p.1.2 ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p*ψ p.1.1 ∂TriangleIntegration.tripleMeasure) ∧
    (∫ p, tiltTriangleWeight U p*ψ p.2 ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p*ψ p.1.1 ∂TriangleIntegration.tripleMeasure) := by
  have hw : ∀ᵐ p ∂TriangleIntegration.tripleMeasure,
      tiltTriangleWeight U (TriangleIntegration.cycle p) = tiltTriangleWeight U p := by
    filter_upwards [TriangleIntegration.edgeZ_qmp.ae U.symmetric,
      TriangleIntegration.edgeX_qmp.ae U.symmetric] with p hz hx
    change U (p.2,p.1.1) = U (p.1.1,p.2) at hz
    change U (p.1.2,p.1.1) = U (p.1.1,p.1.2) at hx
    change U (p.1.2,p.2)*U (p.2,p.1.1)*U (p.1.2,p.1.1) =
      U (p.1.1,p.1.2)*U (p.1.2,p.2)*U (p.1.1,p.2)
    rw [hz,hx]
    ring
  have h₁ : (∫ p, tiltTriangleWeight U p*ψ p.1.2 ∂TriangleIntegration.tripleMeasure) =
      (∫ p, tiltTriangleWeight U p*ψ p.1.1 ∂TriangleIntegration.tripleMeasure) := by
    calc
      _ = ∫ p, tiltTriangleWeight U (TriangleIntegration.cycle p)*
          ψ (TriangleIntegration.cycle p).1.1 ∂TriangleIntegration.tripleMeasure := by
        apply integral_congr_ae
        filter_upwards [hw] with p hp
        rw [hp]
        rfl
      _ = _ := TriangleIntegration.cycle_preserving.integral_comp
        TriangleIntegration.cycle.measurableEmbedding (fun p => tiltTriangleWeight U p*ψ p.1.1)
  refine ⟨h₁, ?_⟩
  calc
    _ = ∫ p, tiltTriangleWeight U (TriangleIntegration.cycle p)*
        ψ (TriangleIntegration.cycle p).1.2 ∂TriangleIntegration.tripleMeasure := by
      apply integral_congr_ae
      filter_upwards [hw] with p hp
      rw [hp]
      rfl
    _ = ∫ p, tiltTriangleWeight U p*ψ p.1.2 ∂TriangleIntegration.tripleMeasure :=
      TriangleIntegration.cycle_preserving.integral_comp
        TriangleIntegration.cycle.measurableEmbedding (fun p => tiltTriangleWeight U p*ψ p.1.2)
    _ = _ := h₁

/-- Triangle vertex differentiation is three times the rooted-triangle test. -/
theorem integral_triangle_vertex_direction (U : Graphon) {ψ : ℝ → ℝ}
    (hψ : BoundedObservable unitMeasure ψ) :
    (∫ p, tiltTriangleWeight U p*(ψ p.1.1+ψ p.1.2+ψ p.2)
      ∂TriangleIntegration.tripleMeasure) =
      3*(∫ x, ψ x*rowTriangle U x ∂unitMeasure) := by
  have hx := hψ.comp (Measure.quasiMeasurePreserving_fst.comp TriangleIntegration.edgeX_qmp)
  have hy := hψ.comp (Measure.quasiMeasurePreserving_snd.comp TriangleIntegration.edgeX_qmp)
  have hz := hψ.comp (Measure.quasiMeasurePreserving_snd (μ := squareMeasure) (ν := unitMeasure))
  dsimp only [Function.comp_def] at hx hy
  have h₁ := ((tiltTriangleWeight_bounded U).mul hx).integrable
  have h₂ := ((tiltTriangleWeight_bounded U).mul hy).integrable
  have h₃ := ((tiltTriangleWeight_bounded U).mul hz).integrable
  have h₁₂ : Integrable (fun p => tiltTriangleWeight U p*ψ p.1.1+
      tiltTriangleWeight U p*ψ p.1.2) TriangleIntegration.tripleMeasure := h₁.add h₂
  have hc := integral_triangle_vertex_cycle U ψ
  have hfirst : (∫ p, tiltTriangleWeight U p*ψ p.1.1 ∂TriangleIntegration.tripleMeasure) =
      ∫ x, ψ x*rowTriangle U x ∂unitMeasure := by
    calc
      _ = ∫ p, (U p.1*ψ p.1.1)*TriangleIntegration.Y U p*TriangleIntegration.Z U p
          ∂TriangleIntegration.tripleMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by unfold tiltTriangleWeight TriangleIntegration.X; ring
      _ = ∫ p, (U p*ψ p.1)*codegree U p.1 p.2 ∂squareMeasure :=
        TriangleIntegration.integral_test_codegree U
          ((graphon_boundedObservable U).mul (hψ.comp Measure.quasiMeasurePreserving_fst))
      _ = ∫ p, (U p*codegree U p.1 p.2)*ψ p.1 ∂squareMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by ring
      _ = _ := integral_vertex_test_pair
        ((graphon_boundedObservable U).mul (codegree_boundedObservable U)) hψ
  rw [show (fun p => tiltTriangleWeight U p*(ψ p.1.1+ψ p.1.2+ψ p.2)) =
    (fun p => (tiltTriangleWeight U p*ψ p.1.1+tiltTriangleWeight U p*ψ p.1.2)+
      tiltTriangleWeight U p*ψ p.2) by funext p; ring,
    integral_add h₁₂ h₃, integral_add h₁ h₂, hc.1, hc.2, hfirst]
  ring


private theorem eventually_abs_le_half : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ 1/2 := by
  have h : Icc (-(1/2 : ℝ)) (1/2) ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have he : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Icc (-(1/2 : ℝ)) (1/2) := h
  exact he.mono fun s hs => abs_le.mpr hs

/-- The cost derivative in `s3:expand`, for the actual sampled graphon path. -/
theorem hasDerivAt_vertexVariation_cost (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0) :
    HasDerivAt (fun s => cost (vertexVariation hSampling U ψ hψ hbound hmean s))
      (2*(∫ x, ψ x*rowEntropy U x ∂unitMeasure)) 0 := by
  have hb : BoundedObservable unitMeasure ψ := ⟨hψ,1,by norm_num,hbound⟩
  have hd := hasDerivAt_integral_pair_weight (graphon_entropy_boundedObservable U)
    (hb.comp Measure.quasiMeasurePreserving_fst) (hb.comp Measure.quasiMeasurePreserving_snd)
  have hs : ∀ᵐ p ∂squareMeasure, entropy (U p.swap) = entropy (U p) :=
    U.symmetric.mono fun p hp => congrArg entropy hp
  rw [integral_pair_vertex_direction (graphon_entropy_boundedObservable U) hb hs] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_abs_le_half] with s hs
  rw [vertexVariation_cost hSampling U ψ hψ hbound hmean hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by ring

/-- The degree derivative in `s3:expand`. -/
theorem hasDerivAt_vertexVariation_edge (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0) :
    HasDerivAt (fun s => edgeDensity (vertexVariation hSampling U ψ hψ hbound hmean s))
      (2*(∫ x, ψ x*rowDegree U x ∂unitMeasure)) 0 := by
  have hb : BoundedObservable unitMeasure ψ := ⟨hψ,1,by norm_num,hbound⟩
  have hd := hasDerivAt_integral_pair_weight (graphon_boundedObservable U)
    (hb.comp Measure.quasiMeasurePreserving_fst) (hb.comp Measure.quasiMeasurePreserving_snd)
  rw [integral_pair_vertex_direction (graphon_boundedObservable U) hb U.symmetric] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_abs_le_half] with s hs
  rw [vertexVariation_edge hSampling U ψ hψ hbound hmean hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by ring

/-- The triangle derivative in `s3:expand`. -/
theorem hasDerivAt_vertexVariation_triangle (hSampling : UniformSampling) (U : Graphon)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0) :
    HasDerivAt (fun s => triangle (vertexVariation hSampling U ψ hψ hbound hmean s))
      (3*(∫ x, ψ x*rowTriangle U x ∂unitMeasure)) 0 := by
  have hb : BoundedObservable unitMeasure ψ := ⟨hψ,1,by norm_num,hbound⟩
  have hx := hb.comp (Measure.quasiMeasurePreserving_fst.comp TriangleIntegration.edgeX_qmp)
  have hy := hb.comp (Measure.quasiMeasurePreserving_snd.comp TriangleIntegration.edgeX_qmp)
  have hz := hb.comp (Measure.quasiMeasurePreserving_snd (μ := squareMeasure) (ν := unitMeasure))
  dsimp only [Function.comp_def] at hx hy
  have hd := hasDerivAt_integral_triple_weight (tiltTriangleWeight_bounded U) hx hy hz
  rw [integral_triangle_vertex_direction U hb] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_abs_le_half] with s hs
  rw [vertexVariation_triangle hSampling U ψ hψ hbound hmean hs]
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

/-- Vertex first variation annihilates every bounded mean-zero test. -/
theorem minimizer_vertex_test (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U)
    (ψ : ℝ → ℝ) (hψ : AEMeasurable ψ unitMeasure)
    (hbound : ∀ᵐ x ∂unitMeasure, |ψ x| ≤ 1) (hmean : ∫ x, ψ x ∂unitMeasure = 0) :
    (∫ x, ψ x*vertexStationary U r x ∂unitMeasure) = 0 := by
  let W := fun s => NonnegativeKernel.ofGraphon (vertexVariation hSampling U ψ hψ hbound hmean s)
  have hW0 : (W 0).toFun =ᵐ[squareMeasure] U.toFun := by
    simp only [W, vertexVariation_zero]
    exact EventuallyEq.rfl
  have hF := hasDerivAt_vertexVariation_cost hSampling U ψ hψ hbound hmean
  have he := hasDerivAt_vertexVariation_edge hSampling U ψ hψ hbound hmean
  have ht := hasDerivAt_vertexVariation_triangle hSampling U ψ hψ hbound hmean
  have h := rescaling_firstVariation_interval (c := 1/2) hr (by norm_num) hU hW0
    hF.hasDerivWithinAt he.hasDerivWithinAt ht.hasDerivWithinAt
  have hb : BoundedObservable unitMeasure ψ := ⟨hψ,1,by norm_num,hbound⟩
  have h₁ := ((hb.mul (rowEntropy_bounded U)).const_mul 2).integrable
  have h₂ := ((hb.mul (rowTriangle_bounded U)).const_mul (graphonMultiplier U r)).integrable
  have hid : (∫ x, ψ x*vertexStationary U r x ∂unitMeasure) =
      2*(∫ x, ψ x*rowEntropy U x ∂unitMeasure) +
      graphonMultiplier U r*(∫ x, ψ x*rowTriangle U x ∂unitMeasure) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add h₁ h₂]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by unfold vertexStationary; ring
  rw [hid]
  linarith

/-- The first identity in `prop:vertex`: rooted entropy and triangles have a constant sum. -/
theorem minimizer_vertex_stationary (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, vertexStationary U r x = vertexMean U r := by
  have h := ae_eq_mean_of_mean_zero_tests (vertexStationary_bounded U r)
    (minimizer_vertex_test hSampling hr hU)
  simpa only [integral_vertexStationary hr hU] using h

/-- The constant in `prop:vertex`, expressed without the multiplier. -/
theorem vertexMean_eq {r : ℝ} (hr : r ≠ 0) (U : Graphon) :
    vertexMean U r = 1+cost U-edgeDensity U := by
  have h := graphonMultiplier_integral_identity (U := U) hr
  rw [integral_mulLog_identity] at h
  unfold vertexMean
  linarith

/-- The integrated row version of the edge Euler equation. -/
theorem minimizer_row_log_identity {r : ℝ} (hr : r ∈ Ioo 0 1)
    {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, graphonMultiplier U r*rowTriangle U x =
      -(∫ y, U (x,y)*Real.log (U (x,y)) ∂unitMeasure) := by
  have hrow := Measure.ae_ae_of_ae_prod (minimizer_log_equation hr hU)
  filter_upwards [hrow] with x hx
  unfold rowTriangle
  rw [← integral_const_mul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hx] with y hy
  rw [hy]
  ring

/-- Rewriting the stationary row expression as the paper's vertex entropy. -/
theorem minimizer_row_vertexEntropy {r : ℝ} (hr : r ∈ Ioo 0 1)
    {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, (∫ y, vertexEntropy (U (x,y)) ∂unitMeasure) =
      vertexStationary U r x := by
  have hh := (cost_integrable U).prod_right_ae
  have hl := (graphon_mulLog_boundedObservable U).integrable.prod_right_ae
  filter_upwards [hh, hl, minimizer_row_log_identity hr hU] with x hx hlog he
  unfold vertexStationary rowEntropy
  rw [he, ← sub_eq_add_neg, ← integral_const_mul, ← integral_sub (hx.const_mul 2) hlog]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by unfold vertexEntropy entropy; ring

/-- `prop:vertex`: the actual row integral identity used in bipodal classification. -/
theorem minimizer_vertex_identity (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) : VertexIdentity U := by
  refine ⟨vertexMean U r, ?_⟩
  filter_upwards [minimizer_vertex_stationary hSampling hr hU,
    minimizer_row_vertexEntropy hr hU] with x hx hy
  exact hy.trans hx

/-- The equivalent degree identity `s3:degree`. -/
theorem minimizer_vertex_degree (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, graphonMultiplier U r*rowTriangle U x + 2*rowDegree U x =
      graphonMultiplier U r*r^3+2*edgeDensity U := by
  have hh := (cost_integrable U).prod_right_ae
  have hd := (graphon_integrable U).prod_right_ae
  have hm := graphonMultiplier_integral_identity (U := U) (ne_of_gt hr.1)
  rw [integral_mulLog_identity] at hm
  filter_upwards [hh, hd, minimizer_vertex_stationary hSampling hr hU,
    minimizer_row_vertexEntropy hr hU] with x hx hdg hstat hrow
  have hv : (∫ y, vertexEntropy (U (x,y)) ∂unitMeasure) =
      rowEntropy U x-rowDegree U x+1 := by
    calc
      _ = ∫ y, (entropy (U (x,y))-U (x,y))+1 ∂unitMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by unfold vertexEntropy entropy; ring
      _ = _ := by
        have hi : Integrable (fun y => entropy (U (x,y))-U (x,y)) unitMeasure := hx.sub hdg
        rw [integral_add hi (integrable_const 1), integral_sub hx hdg]
        simp [rowEntropy,rowDegree]
  rw [hv] at hrow
  unfold vertexStationary at hstat hrow
  unfold vertexMean at hstat
  linarith

end SparseLowerTail.Section04

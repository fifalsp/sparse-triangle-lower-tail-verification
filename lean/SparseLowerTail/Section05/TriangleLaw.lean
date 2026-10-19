import SparseLowerTail.Section05.TriangleRelaxation
import SparseLowerTail.Section05.Hoeffding

/-! The actual pushforward law in `def:trilaw`. Coordinates are (A,B,C) =
(U(x,y),U(x,z),U(y,z)), in the manuscript's order. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section05
open Section04 TriangleIntegration

abbrev EdgeTriple := (ℝ × ℝ) × ℝ

def edgeValues (U : Graphon) (p : EdgeTriple) : EdgeTriple :=
  ((X U p,Z U p),Y U p)

theorem edgeValues_aemeasurable (U : Graphon) : AEMeasurable (edgeValues U) tripleMeasure :=
  ((boundedX U).measurable.prodMk (boundedZ U).measurable).prodMk (boundedY U).measurable

def triangleLaw (U : Graphon) : Measure EdgeTriple := tripleMeasure.map (edgeValues U)

instance (U : Graphon) : IsProbabilityMeasure (triangleLaw U) :=
  Measure.isProbabilityMeasure_map (edgeValues_aemeasurable U)

theorem integral_triangleLaw (U : Graphon) {f : EdgeTriple → ℝ}
    (hf : Measurable f) :
    (∫ u, f u ∂triangleLaw U) = ∫ p, f ((X U p,Z U p),Y U p) ∂tripleMeasure :=
  integral_map (edgeValues_aemeasurable U) hf.aestronglyMeasurable

def edgeCube (ell : ℝ) : Set EdgeTriple :=
  {u | u.1.1 ∈ Icc ell 1 ∧ u.1.2 ∈ Icc ell 1 ∧ u.2 ∈ Icc ell 1}

theorem measurableSet_edgeCube (ell : ℝ) : MeasurableSet (edgeCube ell) := by
  have hm : MeasurableSet (Icc ell (1:ℝ)) := measurableSet_Icc
  exact (hm.preimage (measurable_fst.comp measurable_fst)).inter
    ((hm.preimage (measurable_snd.comp measurable_fst)).inter
      (hm.preimage measurable_snd))

theorem triangleLaw_supported {U : Graphon} {ell : ℝ}
    (hl : ∀ᵐ p ∂squareMeasure, ell ≤ U p) :
    ∀ᵐ u ∂triangleLaw U, u ∈ edgeCube ell := by
  apply (ae_map_iff (edgeValues_aemeasurable U) (measurableSet_edgeCube ell)).mpr
  have hb : ∀ᵐ p ∂squareMeasure, U p ∈ Icc ell 1 := by
    filter_upwards [hl,U.bounded] with p hp hq
    exact ⟨hp,hq.2⟩
  filter_upwards [edgeX_qmp.ae hb,edgeZ_qmp.ae hb,edgeY_qmp.ae hb] with p hx hz hy
  exact ⟨hx,hz,hy⟩

theorem triangleLaw_unitCube (U : Graphon) : ∀ᵐ u ∂triangleLaw U, u ∈ edgeCube 0 :=
  triangleLaw_supported (U.bounded.mono fun _ h => h.1)

theorem triangleLaw_edge (U : Graphon) : (∫ u, u.1.1 ∂triangleLaw U) = edgeDensity U := by
  rw [integral_triangleLaw U (f := fun u => u.1.1) (measurable_fst.comp measurable_fst)]
  exact integral_X U (f := id) (graphon_boundedObservable U)

theorem triangleLaw_cost (U : Graphon) : (∫ u, entropy u.1.1 ∂triangleLaw U) = cost U := by
  rw [integral_triangleLaw U (f := fun u => entropy u.1.1) (continuous_entropy.measurable.comp
    (measurable_fst.comp measurable_fst))]
  exact integral_X U (graphon_entropy_boundedObservable U)

theorem triangleLaw_triangle (U : Graphon) :
    (∫ u, u.1.1*u.1.2*u.2 ∂triangleLaw U) = triangle U := by
  rw [integral_triangleLaw U (f := fun u => u.1.1*u.1.2*u.2)
    (((measurable_fst.comp measurable_fst).mul
      (measurable_snd.comp measurable_fst)).mul measurable_snd)]
  convert integral_XYZ U using 1
  congr 1
  funext p
  ring

theorem triangleLaw_edge_test {r : ℝ} (hr : r ∈ Ioo 0 1)
    {U : Graphon} (hU : IsMinimizer r U) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hb : BoundedObservable squareMeasure (fun p => φ (U p))) :
    (∫ u, φ u.1.1*(Real.log u.1.1+graphonMultiplier U r*u.1.2*u.2)
      ∂triangleLaw U) = 0 := by
  have hm : Measurable (fun u : EdgeTriple =>
      φ u.1.1*(Real.log u.1.1+graphonMultiplier U r*u.1.2*u.2)) := by fun_prop
  rw [integral_triangleLaw U hm]
  convert minimizer_edge_test hr hU hb using 1
  congr 1
  funext p
  dsimp [X]
  ring

theorem triangleLaw_vertex_test (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U)
    {χ : ℝ → ℝ} (hχ : Measurable χ)
    (hb : BoundedObservable squareMeasure (fun p => χ (U p))) :
    (∫ u, χ u.1.1*(vertexEntropy u.1.2+vertexEntropy u.2-2*vertexMean U r)
      ∂triangleLaw U) = 0 := by
  have hk : Measurable vertexEntropy := by unfold vertexEntropy; fun_prop
  have hm : Measurable (fun u : EdgeTriple =>
      χ u.1.1*(vertexEntropy u.1.2+vertexEntropy u.2-2*vertexMean U r)) := by fun_prop
  rw [integral_triangleLaw U hm]
  convert minimizer_vertex_test_moment hSampling hr hU hb using 1
  congr 1
  funext p
  dsimp [X]
  ring

/-- The nonlinear T4 constraint, for any coefficient ω, holds for every graphon. -/
theorem triangleLaw_hoeffding (U : Graphon) (ω : ℝ) :
    let g := fun u : ℝ => u+ω*entropy u
    0 ≤ (∫ u, (g u.1.1)^2 ∂triangleLaw U) -
      2*(∫ u, g u.1.1*g u.1.2 ∂triangleLaw U)+(edgeDensity U+ω*cost U)^2 := by
  dsimp
  have hentropy : Measurable entropy := continuous_entropy.measurable
  have hg : Measurable (fun u : ℝ => u+ω*entropy u) :=
    measurable_id.add (continuous_entropy.measurable.const_mul ω)
  have hm1 : Measurable (fun u : EdgeTriple => (u.1.1+ω*entropy u.1.1)^2) := by fun_prop
  have hm2 : Measurable (fun u : EdgeTriple =>
      (u.1.1+ω*entropy u.1.1)*(u.1.2+ω*entropy u.1.2)) := by fun_prop
  rw [integral_triangleLaw U hm1,integral_triangleLaw U hm2]
  exact hoeffding_affine_entropy_nonneg U ω

/-- Every minimizer's triangle law has the sharp support needed by the cover. -/
theorem minimizer_triangleLaw_supported (hSampling : UniformSampling) {r : ℝ}
    (hr : r ∈ Ioo 0 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ u ∂triangleLaw U,
      u ∈ edgeCube (supportLambda (r^3) (edgeDensity U) (cost U)) :=
  triangleLaw_supported (minimizer_supportLambda_lower hSampling hr hU)

end SparseLowerTail.Section05

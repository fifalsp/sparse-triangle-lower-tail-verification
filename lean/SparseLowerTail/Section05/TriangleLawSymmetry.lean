import SparseLowerTail.Section05.TriangleLaw

/-!
# Permutation symmetry of the actual triangle law

Stable manuscript anchors: `def:trilaw`, permutation invariance in `def:relaxed`.
Two adjacent coordinate swaps generate all permutations of the three edge values.
Their invariance is proved as equality of measures, not only for selected tests.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
namespace SparseLowerTail.Section05
open Section04 TriangleIntegration

/-- Swap the first two scalar coordinates of an associated triple. -/
def edgeSwap12 : EdgeTriple ≃ᵐ EdgeTriple :=
  MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℝ)

/-- Swap the last two scalar coordinates of an associated triple. -/
def edgeSwap23 : EdgeTriple ≃ᵐ EdgeTriple :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans MeasurableEquiv.prodAssoc.symm)

@[simp] theorem edgeSwap12_apply (p : EdgeTriple) : edgeSwap12 p = ((p.1.2,p.1.1),p.2) := rfl
@[simp] theorem edgeSwap23_apply (p : EdgeTriple) : edgeSwap23 p = ((p.1.1,p.2),p.1.2) := rfl

/-- Both generating swaps preserve the product measure of independent vertices. -/
theorem edgeSwap12_vertex_preserving : MeasurePreserving edgeSwap12 tripleMeasure tripleMeasure :=
  Measure.measurePreserving_swap.prod (MeasurePreserving.id unitMeasure)

theorem edgeSwap23_vertex_preserving : MeasurePreserving edgeSwap23 tripleMeasure tripleMeasure := by
  have ha := measurePreserving_prodAssoc unitMeasure unitMeasure unitMeasure
  have hb := (MeasurePreserving.id unitMeasure).prod
    (Measure.measurePreserving_swap (μ := unitMeasure) (ν := unitMeasure))
  exact (ha.symm MeasurableEquiv.prodAssoc).comp (hb.comp ha)

/-- Symmetry of a triple law, expressed through two generating adjacent swaps. -/
def TriangleLawSymmetric (ν : Measure EdgeTriple) : Prop :=
  ν.map edgeSwap12 = ν ∧ ν.map edgeSwap23 = ν

/-- Swapping vertices y,z swaps edge coordinates A,B. -/
theorem edgeValues_swap23_ae (U : Graphon) :
    (fun p => edgeValues U (edgeSwap23 p)) =ᵐ[tripleMeasure]
      (fun p => edgeSwap12 (edgeValues U p)) := by
  filter_upwards [edgeY_qmp.ae U.symmetric] with p hp
  change U (p.2,p.1.2) = U (p.1.2,p.2) at hp
  change ((U (p.1.1,p.2),U (p.1.1,p.1.2)),U (p.2,p.1.2)) =
    ((U (p.1.1,p.2),U (p.1.1,p.1.2)),U (p.1.2,p.2))
  rw [hp]

/-- Swapping vertices x,y swaps edge coordinates B,C. -/
theorem edgeValues_swap12_ae (U : Graphon) :
    (fun p => edgeValues U (edgeSwap12 p)) =ᵐ[tripleMeasure]
      (fun p => edgeSwap23 (edgeValues U p)) := by
  filter_upwards [edgeX_qmp.ae U.symmetric] with p hp
  change U (p.1.2,p.1.1) = U (p.1.1,p.1.2) at hp
  change ((U (p.1.2,p.1.1),U (p.1.2,p.2)),U (p.1.1,p.2)) =
    ((U (p.1.1,p.1.2),U (p.1.2,p.2)),U (p.1.1,p.2))
  rw [hp]

/-- A commuting vertex permutation induces invariance of the pushforward edge law. -/
theorem triangleLaw_map_eq_of_vertex_permutation (U : Graphon)
    (e v : EdgeTriple ≃ᵐ EdgeTriple) (hv : MeasurePreserving v tripleMeasure tripleMeasure)
    (hcomm : (fun p => edgeValues U (v p)) =ᵐ[tripleMeasure]
      (fun p => e (edgeValues U p))) :
    (triangleLaw U).map e = triangleLaw U := by
  have hme : AEMeasurable (edgeValues U) (tripleMeasure.map v) := by
    simpa only [hv.map_eq] using edgeValues_aemeasurable U
  calc
    _ = tripleMeasure.map (e ∘ edgeValues U) :=
      AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable (edgeValues_aemeasurable U)
    _ = tripleMeasure.map (edgeValues U ∘ v) := Measure.map_congr hcomm.symm
    _ = (tripleMeasure.map v).map (edgeValues U) :=
      (AEMeasurable.map_map_of_aemeasurable hme hv.measurable.aemeasurable).symm
    _ = triangleLaw U := by rw [hv.map_eq]; rfl

theorem triangleLaw_map_swap12 (U : Graphon) : (triangleLaw U).map edgeSwap12 = triangleLaw U :=
  triangleLaw_map_eq_of_vertex_permutation U edgeSwap12 edgeSwap23
    edgeSwap23_vertex_preserving (edgeValues_swap23_ae U)

theorem triangleLaw_map_swap23 (U : Graphon) : (triangleLaw U).map edgeSwap23 = triangleLaw U :=
  triangleLaw_map_eq_of_vertex_permutation U edgeSwap23 edgeSwap12
    edgeSwap12_vertex_preserving (edgeValues_swap12_ae U)

/-- The permutation-invariance requirement in `def:relaxed`, for every graphon. -/
theorem triangleLaw_symmetric (U : Graphon) : TriangleLawSymmetric (triangleLaw U) :=
  ⟨triangleLaw_map_swap12 U,triangleLaw_map_swap23 U⟩

theorem triangleLaw_swap12_preserving (U : Graphon) :
    MeasurePreserving edgeSwap12 (triangleLaw U) (triangleLaw U) :=
  ⟨edgeSwap12.measurable,triangleLaw_map_swap12 U⟩

theorem triangleLaw_swap23_preserving (U : Graphon) :
    MeasurePreserving edgeSwap23 (triangleLaw U) (triangleLaw U) :=
  ⟨edgeSwap23.measurable,triangleLaw_map_swap23 U⟩

/-- Universal real-test integral invariance, including nonintegrable tests under Bochner's convention. -/
theorem integral_triangleLaw_swap12 (U : Graphon) (f : EdgeTriple → ℝ) :
    (∫ p, f (edgeSwap12 p) ∂triangleLaw U) = ∫ p, f p ∂triangleLaw U :=
  (triangleLaw_swap12_preserving U).integral_comp edgeSwap12.measurableEmbedding f

theorem integral_triangleLaw_swap23 (U : Graphon) (f : EdgeTriple → ℝ) :
    (∫ p, f (edgeSwap23 p) ∂triangleLaw U) = ∫ p, f p ∂triangleLaw U :=
  (triangleLaw_swap23_preserving U).integral_comp edgeSwap23.measurableEmbedding f

/-- Invariance under any finite word in the two generators: these words include all six permutations. -/
def edgePermutationWord : List Bool → EdgeTriple ≃ᵐ EdgeTriple
  | [] => MeasurableEquiv.refl EdgeTriple
  | false :: w => edgeSwap12.trans (edgePermutationWord w)
  | true :: w => edgeSwap23.trans (edgePermutationWord w)

theorem TriangleLawSymmetric.word_preserving {ν : Measure EdgeTriple}
    (hν : TriangleLawSymmetric ν) (w : List Bool) :
    MeasurePreserving (edgePermutationWord w) ν ν := by
  induction w with
  | nil => exact MeasurePreserving.id ν
  | cons b w ih =>
    cases b with
    | false => exact ih.comp ⟨edgeSwap12.measurable,hν.1⟩
    | true => exact ih.comp ⟨edgeSwap23.measurable,hν.2⟩

theorem triangleLaw_permutationWord_preserving (U : Graphon) (w : List Bool) :
    MeasurePreserving (edgePermutationWord w) (triangleLaw U) (triangleLaw U) :=
  (triangleLaw_symmetric U).word_preserving w

theorem integral_triangleLaw_permutationWord (U : Graphon) (w : List Bool) (f : EdgeTriple → ℝ) :
    (∫ p, f (edgePermutationWord w p) ∂triangleLaw U) = ∫ p, f p ∂triangleLaw U :=
  (triangleLaw_permutationWord_preserving U w).integral_comp (edgePermutationWord w).measurableEmbedding f

end SparseLowerTail.Section05

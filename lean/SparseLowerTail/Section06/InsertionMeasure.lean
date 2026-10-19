import SparseLowerTail.Section06.PointwiseRepresentative
import SparseLowerTail.Section04.VertexReweighting
import SparseLowerTail.Section02.Relabeling

/-! The probability space for inserting a new class of vertices. An atom at 2
is disjoint from the old unit interval; inverse-transform sampling realizes
the mixture on the original graphon probability space. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace SparseLowerTail.Section06
open Section04

instance finiteMeasure_ofReal_smul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal s • μ) := μ.smul_finite ENNReal.ofReal_ne_top

def insertionMeasure (s : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1-s) • unitMeasure+ENNReal.ofReal s • Measure.dirac 2

instance (s : ℝ) : IsFiniteMeasure (insertionMeasure s) := by
  unfold insertionMeasure
  infer_instance

theorem insertionMeasure_probability {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    IsProbabilityMeasure (insertionMeasure s) := by
  constructor
  simp only [insertionMeasure,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hs.2) hs.1]
  norm_num

theorem unit_ne_insertionAtom : ∀ᵐ x ∂unitMeasure, x ≠ (2:ℝ) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  change x ∈ Icc (0:ℝ) 1 at hx
  linarith [hx.2]

/-- A pointwise bound yields integrability for every finite measure. -/
theorem integrable_of_measurable_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

/-- Integrating a mixture gives the old-vertex and new-vertex terms. -/
theorem integral_insertionMeasure {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1)
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂insertionMeasure s)=(1-s)*(∫ x, f x ∂unitMeasure)+s*f 2 := by
  rw [insertionMeasure,integral_add_measure
    (integrable_of_measurable_bound _ hf hb) (integrable_of_measurable_bound _ hf hb)]
  simp [integral_smul_measure,ENNReal.toReal_ofReal hs.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2)]

/-- Exact pair expansion, including the new-new vertex term. -/
theorem integral_insertionMeasure_pair {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ p, f p ∂(insertionMeasure s).prod (insertionMeasure s))=
      (1-s)^2*(∫ p, f p ∂squareMeasure)+
      s*(1-s)*((∫ x, f (2,x) ∂unitMeasure)+(∫ x, f (x,2) ∂unitMeasure))+
      s^2*f (2,2) := by
  have hi (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] : Integrable f μ :=
    integrable_of_measurable_bound μ hf hb
  simp only [insertionMeasure,Measure.add_prod,Measure.prod_add,
    Measure.prod_smul_left,Measure.prod_smul_right]
  simp only [integral_add_measure (hi _) (hi _),integral_smul_measure,
    ENNReal.toReal_ofReal hs.1,ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2),smul_eq_mul]
  have hleft : (∫ p, f p ∂(Measure.dirac (2:ℝ)).prod unitMeasure)=∫ x, f (2,x) ∂unitMeasure := by
    rw [integral_prod _ (hi _)]
    simp
  have hright : (∫ p, f p ∂unitMeasure.prod (Measure.dirac (2:ℝ)))=∫ x, f (x,2) ∂unitMeasure := by
    rw [integral_prod _ (hi _)]
    simp
  rw [hleft,hright,Measure.dirac_prod_dirac,integral_dirac]
  change _ = (1-s)^2*(∫ p, f p ∂unitMeasure.prod unitMeasure)+_+_
  ring

/-- Fubini for a globally bounded measurable three-variable integrand. -/
theorem integral_three_iterated (μ ν κ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ]
    {f : ℝ × (ℝ × ℝ) → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ p, f p ∂μ.prod (ν.prod κ))=∫ x, ∫ y, ∫ z, f (x,y,z) ∂κ ∂ν ∂μ := by
  rw [integral_prod _ (integrable_of_measurable_bound _ hf hb)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    integral_prod _ (integrable_of_measurable_bound _
      (hf.comp (measurable_const.prodMk measurable_id)) (fun p => hb (x,p)))

/-- Exact expansion by the number and position of inserted vertices. -/
theorem integral_insertionMeasure_triple {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1)
    {f : ℝ × (ℝ × ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ p, f p ∂(insertionMeasure s).prod ((insertionMeasure s).prod (insertionMeasure s)))=
      (1-s)^3*(∫ x, ∫ y, ∫ z, f (x,y,z) ∂unitMeasure ∂unitMeasure ∂unitMeasure)+
      s*(1-s)^2*((∫ y, ∫ z, f (2,y,z) ∂unitMeasure ∂unitMeasure)+
        (∫ x, ∫ z, f (x,2,z) ∂unitMeasure ∂unitMeasure)+
        (∫ x, ∫ y, f (x,y,2) ∂unitMeasure ∂unitMeasure))+
      s^2*(1-s)*((∫ z, f (2,2,z) ∂unitMeasure)+
        (∫ y, f (2,y,2) ∂unitMeasure)+(∫ x, f (x,2,2) ∂unitMeasure))+
      s^3*f (2,2,2) := by
  have hi (μ : Measure (ℝ × (ℝ × ℝ))) [IsFiniteMeasure μ] : Integrable f μ :=
    integrable_of_measurable_bound μ hf hb
  simp only [insertionMeasure,Measure.add_prod,Measure.prod_add,
    Measure.prod_smul_left,Measure.prod_smul_right]
  simp only [integral_add_measure (hi _) (hi _),integral_smul_measure,
    ENNReal.toReal_ofReal hs.1,ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2),smul_eq_mul]
  simp only [integral_three_iterated _ _ _ hf hb,integral_dirac]
  ring

end SparseLowerTail.Section06

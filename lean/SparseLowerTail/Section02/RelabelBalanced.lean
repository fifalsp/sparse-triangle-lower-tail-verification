import SparseLowerTail.Section02.Relabeling
import SparseLowerTail.Balanced
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! The measurable-partition/relabeling equivalence, manuscript lem:relabelB. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
namespace SparseLowerTail.Section02

instance unitMeasure_noAtoms : NoAtoms unitMeasure := by
  unfold unitMeasure
  infer_instance

/-- Classical probability-integral transform for finite nonatomic real measures,
including translation of the target interval. This is a CDF transport statement,
not an inverse-sampling theorem, and contains no graphon conclusion. -/
def ClassicalCDFTransport : Prop :=
  ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] [NoAtoms ν] (c : ℝ),
    MeasurePreserving (fun x => c+ν.real (Iic x)) ν
      (volume.restrict (Icc c (c+ν.real univ)))

/-- The piecewise cumulative-distribution map of a measurable half-partition. -/
def halfTransport (P : Set ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x∈P then (unitMeasure.restrict P).real (Iic x)
    else 1/2+(unitMeasure.restrict Pᶜ).real (Iic x)

private theorem half_restrict_masses {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) :
    (unitMeasure.restrict P).real univ=(1/2:ℝ) ∧
    (unitMeasure.restrict Pᶜ).real univ=(1/2:ℝ) := by
  have hc : unitMeasure Pᶜ=(1/2:ENNReal) := by
    rw [measure_compl hP (measure_ne_top _ _),measure_univ,hm]
    norm_num
  constructor <;> simp only [measureReal_def,Measure.restrict_apply_univ,hm,hc] <;> norm_num

private theorem half_intervals_add :
    volume.restrict (Icc (0:ℝ) (1/2))+volume.restrict (Icc (1/2:ℝ) 1)=unitMeasure := by
  have hi : Icc (0:ℝ) (1/2) ∩ Icc (1/2:ℝ) 1 ⊆ {(1/2:ℝ)} := by
    intro x hx
    simp only [mem_singleton_iff]
    linarith [hx.1.2,hx.2.1]
  have hd : AEDisjoint volume (Icc (0:ℝ) (1/2)) (Icc (1/2:ℝ) 1) :=
    measure_mono_null hi (measure_singleton _)
  have hu : Icc (0:ℝ) (1/2) ∪ Icc (1/2:ℝ) 1=Icc (0:ℝ) 1 := by
    ext x
    simp only [mem_union,mem_Icc]
    constructor
    · rintro (h|h) <;> constructor <;> linarith [h.1,h.2]
    · intro h
      by_cases hx : x≤1/2
      · exact Or.inl ⟨h.1,hx⟩
      · exact Or.inr ⟨(le_of_not_ge hx),h.2⟩
  rw [← Measure.restrict_union₀ hd measurableSet_Icc.nullMeasurableSet,hu]
  rfl

/-- The paper's piecewise CDF map preserves Lebesgue probability on [0,1]. -/
theorem halfTransport_preserving (hCDF : ClassicalCDFTransport)
    {P : Set ℝ} (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal)) :
    MeasurePreserving (halfTransport P) unitMeasure unitMeasure := by
  classical
  have hmass := half_restrict_masses hP hm
  have hleft := hCDF (unitMeasure.restrict P) 0
  have hright := hCDF (unitMeasure.restrict Pᶜ) (1/2)
  simp only [zero_add,hmass.1] at hleft
  rw [hmass.2,show (1/2:ℝ)+1/2=1 by norm_num] at hright
  have hmeas : Measurable (halfTransport P) := Measurable.piecewise hP hleft.measurable hright.measurable
  refine ⟨hmeas,?_⟩
  have hLp : Measure.map (halfTransport P) (unitMeasure.restrict P)=volume.restrict (Icc (0:ℝ) (1/2)) := by
    rw [Measure.map_congr (show halfTransport P =ᵐ[unitMeasure.restrict P]
      (fun x => (unitMeasure.restrict P).real (Iic x)) from by
        filter_upwards [ae_restrict_mem hP] with x hx
        simp [halfTransport,hx])]
    exact hleft.map_eq
  have hRp : Measure.map (halfTransport P) (unitMeasure.restrict Pᶜ)=volume.restrict (Icc (1/2:ℝ) 1) := by
    rw [Measure.map_congr (show halfTransport P =ᵐ[unitMeasure.restrict Pᶜ]
      (fun x => 1/2+(unitMeasure.restrict Pᶜ).real (Iic x)) from by
        filter_upwards [ae_restrict_mem hP.compl] with x hx
        have hxnot : x∉P := hx
        simp only [halfTransport,if_neg hxnot])]
    exact hright.map_eq
  calc
    Measure.map (halfTransport P) unitMeasure =
        Measure.map (halfTransport P) (unitMeasure.restrict P+unitMeasure.restrict Pᶜ) :=
      congrArg _ (Measure.restrict_add_restrict_compl hP).symm
    _ = _ := Measure.map_add _ _ hmeas
    _ = unitMeasure := by rw [hLp,hRp,half_intervals_add]

/-- Apart from a null boundary preimage, the transport exactly identifies the two halves. -/
theorem halfTransport_membership (hCDF : ClassicalCDFTransport)
    {P : Set ℝ} (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal)) :
    ∀ᵐ x ∂unitMeasure, halfTransport P x∈halfInterval ↔ x∈P := by
  classical
  have hmass := half_restrict_masses hP hm
  have hpres := halfTransport_preserving hCDF hP hm
  have hnone : ∀ᵐ x ∂unitMeasure, x ≠ (1/2:ℝ) := by
    rw [ae_iff]
    simpa only [not_not, setOf_eq_eq_singleton] using (measure_singleton (μ := unitMeasure) (1/2:ℝ))
  have hne : ∀ᵐ x ∂unitMeasure, halfTransport P x ≠ (1/2:ℝ) :=
    hpres.quasiMeasurePreserving.ae (p := fun x : ℝ => x ≠ (1/2:ℝ)) hnone
  filter_upwards [hne] with x hx
  by_cases hp : x∈P
  · have hval : halfTransport P x=(unitMeasure.restrict P).real (Iic x) := by
      unfold halfTransport
      exact if_pos hp
    have hlow : 0≤(unitMeasure.restrict P).real (Iic x) := measureReal_nonneg
    have hhi : (unitMeasure.restrict P).real (Iic x)≤1/2 :=
      (measureReal_mono (μ := unitMeasure.restrict P) (subset_univ (Iic x))).trans_eq hmass.1
    exact iff_of_true (show halfTransport P x∈halfInterval by rw [hval]; exact ⟨hlow,hhi⟩) hp
  · have hval : halfTransport P x=1/2+(unitMeasure.restrict Pᶜ).real (Iic x) := by
      unfold halfTransport
      exact if_neg hp
    apply iff_of_false _ hp
    intro hmem
    have hle : halfTransport P x≤(1/2:ℝ) := hmem.2
    have hnon : 0≤(unitMeasure.restrict Pᶜ).real (Iic x) := measureReal_nonneg
    apply hx
    rw [hval] at hle ⊢
    linarith

/-- Actual pullback presentation of a balanced graphon. -/
def IsBalancedRelabeling (U : Graphon) (a b : ℝ) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) : Prop :=
  ∃ φ : Relabeling, U.toFun =ᵐ[squareMeasure] (relabel (balancedGraphon a b ha hb) φ).toFun

/-- The partition-to-relabeling direction uses the explicitly constructed piecewise CDF. -/
theorem IsBalanced.exists_relabel (hCDF : ClassicalCDFTransport) {U : Graphon} {a b : ℝ}
    (hU : IsBalanced U a b) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    IsBalancedRelabeling U a b ha hb := by
  classical
  obtain ⟨P,hP,hm,heq⟩ := hU.exists_twoBlock ha hb
  let φ : Relabeling := ⟨halfTransport P,halfTransport_preserving hCDF hP hm⟩
  refine ⟨φ,?_⟩
  have hmem := halfTransport_membership hCDF hP hm
  filter_upwards [heq,Measure.quasiMeasurePreserving_fst.ae hmem,
    Measure.quasiMeasurePreserving_snd.ae hmem] with p hp hx hy
  rw [hp]
  change blockValue P a b p=blockValue halfInterval a b (halfTransport P p.1,halfTransport P p.2)
  unfold blockValue
  simp only [hx,hy]

/-- The relabeling-to-partition direction is unconditional. -/
theorem isBalanced_of_relabel {U : Graphon} {a b : ℝ} {ha : a∈Icc (0:ℝ) 1} {hb : b∈Icc (0:ℝ) 1}
    (hU : IsBalancedRelabeling U a b ha hb) : IsBalanced U a b := by
  classical
  obtain ⟨φ,hφ⟩ := hU
  let P := φ ⁻¹' halfInterval ∩ Icc (0:ℝ) 1
  have hP : MeasurableSet P := (φ.preserving.measurable halfInterval_measurable).inter measurableSet_Icc
  have hunit : ∀ᵐ x ∂unitMeasure, x∈Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have he : P =ᵐ[unitMeasure] φ ⁻¹' halfInterval := by
    filter_upwards [hunit] with x hx
    apply propext
    change (x∈φ ⁻¹' halfInterval ∧ x∈Icc (0:ℝ) 1) ↔ x∈φ ⁻¹' halfInterval
    exact and_iff_left hx
  have hmass : unitMeasure P=(1/2:ENNReal) := by
    rw [measure_congr he,φ.preserving.measure_preimage halfInterval_measurable.nullMeasurableSet,halfInterval_mass]
  refine ⟨P,hP,inter_subset_right,hmass,?_⟩
  filter_upwards [hφ,Measure.quasiMeasurePreserving_fst.ae hunit,
    Measure.quasiMeasurePreserving_snd.ae hunit] with p hp hx hy
  rw [hp]
  change blockValue halfInterval a b (φ p.1,φ p.2) = _
  by_cases h1 : φ p.1∈halfInterval <;> by_cases h2 : φ p.2∈halfInterval <;>
    simp [blockValue,P,h1,h2,hx,hy]

/-- Full manuscript lem:relabelB, with only the classical CDF transform explicit. -/
theorem isBalanced_iff_relabel (hCDF : ClassicalCDFTransport) {U : Graphon} {a b : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    IsBalanced U a b ↔ IsBalancedRelabeling U a b ha hb :=
  ⟨fun h => IsBalanced.exists_relabel hCDF h ha hb,isBalanced_of_relabel⟩

end SparseLowerTail.Section02

import SparseLowerTail.Section06.InsertionMeasure

/-! Actual insertion graphons and their moment formulas. The new vertex class
is represented by an atom before sampling; no graphon variation is assumed. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section04

structure VertexProfile where
  toFun : ℝ → ℝ
  measurable : Measurable toFun
  bounded : ∀ x, toFun x ∈ Icc (0:ℝ) 1

instance : CoeFun VertexProfile (fun _ => ℝ → ℝ) := ⟨VertexProfile.toFun⟩

def attachmentKernel (U : PointwiseGraphon) (v : VertexProfile) : PointwiseGraphon where
  toFun p := if p.1=2 then (if p.2=2 then 0 else v p.2)
    else (if p.2=2 then v p.1 else U p)
  measurable := Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const (v.measurable.comp measurable_snd))
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      (v.measurable.comp measurable_fst) U.measurable)
  symmetric p := by
    by_cases hx : p.1=2 <;> by_cases hy : p.2=2 <;>
      simp [hx,hy,U.symmetric]
  bounded p := by
    split_ifs <;> first | exact v.bounded _ | exact U.bounded _ | norm_num

def insertionSampler (hSampling : UniformSampling) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ℝ → ℝ :=
  Classical.choose (hSampling (insertionMeasure s) (insertionMeasure_probability hs))

theorem insertionSampler_preserving (hSampling : UniformSampling) (s : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) :
    MeasurePreserving (insertionSampler hSampling s hs) unitMeasure (insertionMeasure s) :=
  Classical.choose_spec (hSampling (insertionMeasure s) (insertionMeasure_probability hs))

def insertedGraphon (hSampling : UniformSampling) (U : PointwiseGraphon) (v : VertexProfile)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : Graphon where
  toFun p := attachmentKernel U v (insertionSampler hSampling s hs p.1,
    insertionSampler hSampling s hs p.2)
  measurable := ((attachmentKernel U v).measurable.comp
    ((insertionSampler_preserving hSampling s hs).measurable.prodMap
      (insertionSampler_preserving hSampling s hs).measurable)).aemeasurable
  symmetric := Eventually.of_forall fun p => (attachmentKernel U v).symmetric
    (insertionSampler hSampling s hs p.1,insertionSampler hSampling s hs p.2)
  bounded := Eventually.of_forall fun p => (attachmentKernel U v).bounded
    (insertionSampler hSampling s hs p.1,insertionSampler hSampling s hs p.2)

theorem integral_integral_congr_off_atom {f g : ℝ → ℝ → ℝ}
    (h : ∀ x, x≠2 → ∀ y, y≠2 → f x y=g x y) :
    (∫ x, ∫ y, f x y ∂unitMeasure ∂unitMeasure)=
      ∫ x, ∫ y, g x y ∂unitMeasure ∂unitMeasure := by
  apply integral_congr_ae
  filter_upwards [unit_ne_insertionAtom] with x hx
  apply integral_congr_ae
  filter_upwards [unit_ne_insertionAtom] with y hy
  exact h x hx y hy

/-- Pair observables split into old-old, old-new, and new-new contributions. -/
theorem insertedGraphon_observable (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1)
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hbound : ∀ x ∈ Icc (0:ℝ) 1, ‖f x‖ ≤ C) :
    (∫ p, f (insertedGraphon hSampling U v s hs p) ∂squareMeasure)=
      (1-s)^2*(∫ p, f (U p) ∂squareMeasure)+
      2*s*(1-s)*(∫ x, f (v x) ∂unitMeasure)+s^2*f 0 := by
  have hmeas := hf.comp (attachmentKernel U v).measurable
  have hb : ∀ p, ‖f (attachmentKernel U v p)‖ ≤ C :=
    fun p => hbound _ ((attachmentKernel U v).bounded p)
  have hi := integrable_of_measurable_bound
    ((insertionMeasure s).prod (insertionMeasure s)) hmeas hb
  have hmap := Section02.integral_comp_preserving
    ((insertionSampler_preserving hSampling s hs).prod
      (insertionSampler_preserving hSampling s hs)) hi
  change (∫ p, f (insertedGraphon hSampling U v s hs p) ∂squareMeasure)=_ at hmap
  rw [hmap,integral_insertionMeasure_pair hs hmeas hb]
  have hold : (∫ p, f (attachmentKernel U v p) ∂squareMeasure)=
      ∫ p, f (U p) ∂squareMeasure := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae unit_ne_insertionAtom,
      Measure.quasiMeasurePreserving_snd.ae unit_ne_insertionAtom] with p hx hy
    simp [attachmentKernel,hx,hy]
  have hleft : (∫ x, f (attachmentKernel U v (2,x)) ∂unitMeasure)=
      ∫ x, f (v x) ∂unitMeasure := by
    apply integral_congr_ae
    filter_upwards [unit_ne_insertionAtom] with x hx
    simp [attachmentKernel,hx]
  have hright : (∫ x, f (attachmentKernel U v (x,2)) ∂unitMeasure)=
      ∫ x, f (v x) ∂unitMeasure := by
    apply integral_congr_ae
    filter_upwards [unit_ne_insertionAtom] with x hx
    simp [attachmentKernel,hx]
  simp only [Function.comp_apply]
  rw [hold,hleft,hright]
  simp only [attachmentKernel,ite_true]
  ring

theorem insertedGraphon_edge (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    edgeDensity (insertedGraphon hSampling U v s hs)=
      (1-s)^2*edgeDensity U.toGraphon+2*s*(1-s)*(∫ x, v x ∂unitMeasure) := by
  have h := insertedGraphon_observable hSampling U v hs measurable_id
    (C := 1) (fun x hx => by simpa [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
  simpa [edgeDensity,PointwiseGraphon.toGraphon] using h

theorem insertedGraphon_cost (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    cost (insertedGraphon hSampling U v s hs)=
      (1-s)^2*cost U.toGraphon+2*s*(1-s)*(∫ x, entropy (v x) ∂unitMeasure)+s^2 := by
  have h := insertedGraphon_observable hSampling U v hs continuous_entropy.measurable
    (C := 1) (fun x hx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (entropy_nonneg hx.1)]
      exact entropy_le_one hx)
  simpa [cost,PointwiseGraphon.toGraphon,entropy_zero] using h

end SparseLowerTail.Section06

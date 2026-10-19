import SparseLowerTail.Section06.VertexInsertion

/-! Exact triangle count of the inserted graphon, with all cross terms proved
from the actual mixture measure and pullback construction. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section04

private theorem unitMul {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    x*y ∈ Icc (0:ℝ) 1 := by
  refine ⟨mul_nonneg hx.1 hy.1,?_⟩
  calc x*y ≤ 1*1 := mul_le_mul hx.2 hy.2 hy.1 (by norm_num)
       _ = 1 := by ring

/-- The row quadratic form, written as a product integral. -/
def rowQuadratic (U : Graphon) (v : ℝ → ℝ) : ℝ :=
  ∫ p, v p.1*U p*v p.2 ∂squareMeasure

def insertionTriple (U : PointwiseGraphon) (v : VertexProfile) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  attachmentKernel U v (p.1,p.2.1)*attachmentKernel U v (p.2.1,p.2.2)*
    attachmentKernel U v (p.1,p.2.2)

theorem insertionTriple_measurable (U : PointwiseGraphon) (v : VertexProfile) :
    Measurable (insertionTriple U v) := by
  have h := (attachmentKernel U v).measurable
  exact ((h.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
    (h.comp measurable_snd)).mul
    (h.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem insertionTriple_bound (U : PointwiseGraphon) (v : VertexProfile) (p : ℝ × (ℝ × ℝ)) :
    ‖insertionTriple U v p‖ ≤ 1 := by
  have h1 := (attachmentKernel U v).bounded (p.1,p.2.1)
  have h2 := (attachmentKernel U v).bounded (p.2.1,p.2.2)
  have h3 := (attachmentKernel U v).bounded (p.1,p.2.2)
  have hp := unitMul (unitMul h1 h2) h3
  change ‖attachmentKernel U v (p.1,p.2.1)*attachmentKernel U v (p.2.1,p.2.2)*attachmentKernel U v (p.1,p.2.2)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg hp.1]
  exact hp.2

theorem rowQuadratic_pointwise_iterated (U : PointwiseGraphon) (v : VertexProfile) :
    rowQuadratic U.toGraphon v.toFun=
      ∫ x, ∫ y, v x*U (x,y)*v y ∂unitMeasure ∂unitMeasure := by
  apply integral_prod
  apply integrable_of_measurable_bound _
    (((v.measurable.comp measurable_fst).mul U.measurable).mul
      (v.measurable.comp measurable_snd)) (C := 1)
  intro p
  have h := unitMul (unitMul (v.bounded p.1) (U.bounded p)) (v.bounded p.2)
  change ‖v p.1*U p*v p.2‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg h.1]
  exact h.2

theorem insertionTriple_old (U : PointwiseGraphon) (v : VertexProfile) :
    (∫ x, ∫ y, ∫ z, insertionTriple U v (x,y,z) ∂unitMeasure ∂unitMeasure ∂unitMeasure)=
      triangle U.toGraphon := by
  have hm : Measurable (fun p : ℝ × (ℝ × ℝ) => U (p.1,p.2.1)*U p.2*U (p.1,p.2.2)) :=
    ((U.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (U.measurable.comp measurable_snd)).mul
      (U.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hb (p : ℝ × (ℝ × ℝ)) : ‖U (p.1,p.2.1)*U p.2*U (p.1,p.2.2)‖ ≤ 1 := by
    have h := unitMul
      (unitMul (U.bounded (p.1,p.2.1)) (U.bounded p.2)) (U.bounded (p.1,p.2.2))
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2
  change _=∫ p, U (p.1,p.2.1)*U p.2*U (p.1,p.2.2) ∂cubeMeasure
  rw [integral_three_iterated _ _ _ hm hb]
  apply integral_congr_ae
  filter_upwards [unit_ne_insertionAtom] with x hx
  apply integral_congr_ae
  filter_upwards [unit_ne_insertionAtom] with y hy
  apply integral_congr_ae
  filter_upwards [unit_ne_insertionAtom] with z hz
  simp [insertionTriple,attachmentKernel,hx,hy,hz]

/-- Each single-new-vertex triangle has the same row quadratic contribution. -/
theorem insertionTriple_one (U : PointwiseGraphon) (v : VertexProfile) :
    (∫ y, ∫ z, insertionTriple U v (2,y,z) ∂unitMeasure ∂unitMeasure)=rowQuadratic U.toGraphon v.toFun ∧
    (∫ x, ∫ z, insertionTriple U v (x,2,z) ∂unitMeasure ∂unitMeasure)=rowQuadratic U.toGraphon v.toFun ∧
    (∫ x, ∫ y, insertionTriple U v (x,y,2) ∂unitMeasure ∂unitMeasure)=rowQuadratic U.toGraphon v.toFun := by
  rw [rowQuadratic_pointwise_iterated]
  refine ⟨?_,?_,?_⟩
  all_goals
    apply integral_integral_congr_off_atom
    intro x hx y hy
    simp [insertionTriple,attachmentKernel,hx,hy]
    <;> ring

/-- Two or three new vertices make the triangle vanish because their connecting edge is zero. -/
theorem insertionTriple_two (U : PointwiseGraphon) (v : VertexProfile) (x : ℝ) :
    insertionTriple U v (2,2,x)=0 ∧ insertionTriple U v (2,x,2)=0 ∧
      insertionTriple U v (x,2,2)=0 := by
  by_cases hx : x=2 <;> simp [insertionTriple,attachmentKernel,hx]

/-- The exact triangle polynomial from `lem:insertion`. -/
theorem insertedGraphon_triangle (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    triangle (insertedGraphon hSampling U v s hs)=
      (1-s)^3*triangle U.toGraphon+3*s*(1-s)^2*rowQuadratic U.toGraphon v.toFun := by
  have hi := integrable_of_measurable_bound
    ((insertionMeasure s).prod ((insertionMeasure s).prod (insertionMeasure s)))
    (insertionTriple_measurable U v) (insertionTriple_bound U v)
  have hp := insertionSampler_preserving hSampling s hs
  have hmap := Section02.integral_comp_preserving (hp.prod (hp.prod hp)) hi
  change triangle (insertedGraphon hSampling U v s hs)=_ at hmap
  rw [hmap,integral_insertionMeasure_triple hs (insertionTriple_measurable U v)
    (insertionTriple_bound U v),insertionTriple_old,
    (insertionTriple_one U v).1,(insertionTriple_one U v).2.1,(insertionTriple_one U v).2.2]
  simp only [(insertionTriple_two U v _).1,(insertionTriple_two U v _).2.1,
    (insertionTriple_two U v _).2.2,integral_zero,add_zero,mul_zero]
  ring

end SparseLowerTail.Section06

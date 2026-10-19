import SparseLowerTail.Section07.CenteredKernel

/-! The exact codegree expansion in the proof of `lem:rowreduction`, before
separating the leading eigenfunction from the remainder kernel. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- The genuine integral action of the centered kernel. -/
def centeredAction (U : Graphon) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, centeredKernel U (x,y)*f y ∂unitMeasure

/-- The genuine composition kernel K². -/
def centeredSquare (U : Graphon) (x y : ℝ) : ℝ :=
  ∫ z, centeredKernel U (x,z)*centeredKernel U (y,z) ∂unitMeasure

private theorem bounded_rows {f : ℝ × ℝ → ℝ} (hf : BoundedObservable squareMeasure f) :
    ∀ᵐ x ∂unitMeasure, BoundedObservable unitMeasure (fun y => f (x,y)) := by
  obtain ⟨K,hK,hbound⟩ := hf.bound
  filter_upwards [hf.integrable.prod_right_ae,Measure.ae_ae_of_ae_prod hbound] with x hx hb
  exact ⟨hx.aemeasurable,K,hK,hb⟩

private theorem integral_centered_product (a b : ℝ) {D u v : ℝ → ℝ}
    (hD : BoundedObservable unitMeasure D) (hu : BoundedObservable unitMeasure u)
    (hv : BoundedObservable unitMeasure v)
    (hD0 : ∫ x, D x ∂unitMeasure=0) (hu0 : ∫ x, u x ∂unitMeasure=0)
    (hv0 : ∫ x, v x ∂unitMeasure=0) :
    (∫ x, (a+D x-u x)*(b+D x-v x) ∂unitMeasure)=a*b+
      (∫ x, D x^2 ∂unitMeasure)-(∫ x, u x*D x ∂unitMeasure)-
      (∫ x, v x*D x ∂unitMeasure)+(∫ x, u x*v x ∂unitMeasure) := by
  let f := fun x => ((a*b+(a+b)*D x)-b*u x)-a*v x
  let g := fun x => (D x^2-u x*D x)-v x*D x
  have hiD2 : Integrable (fun x => D x^2) unitMeasure := by
    simpa only [pow_two] using (hD.mul hD).integrable
  have hi₁ : Integrable (fun x => a*b+(a+b)*D x) unitMeasure :=
    (integrable_const _).add (hD.integrable.const_mul _)
  have hi₂ : Integrable (fun x => (a*b+(a+b)*D x)-b*u x) unitMeasure := hi₁.sub (hu.integrable.const_mul _)
  have hif : Integrable f unitMeasure := hi₂.sub (hv.integrable.const_mul _)
  have hig₁ : Integrable (fun x => D x^2-u x*D x) unitMeasure := hiD2.sub (hu.mul hD).integrable
  have hig : Integrable g unitMeasure := hig₁.sub (hv.mul hD).integrable
  have hf : (∫ x, f x ∂unitMeasure)=a*b := by
    dsimp [f]
    rw [integral_sub hi₂ (hv.integrable.const_mul _),integral_sub hi₁ (hu.integrable.const_mul _),
      integral_add (integrable_const _) (hD.integrable.const_mul _)]
    simp only [integral_const_mul,hD0,hu0,hv0,integral_const,measureReal_univ_eq_one,one_smul,
      mul_zero,add_zero,sub_zero]
  have hg : (∫ x, g x ∂unitMeasure)=(∫ x, D x^2 ∂unitMeasure)-
      (∫ x, u x*D x ∂unitMeasure)-(∫ x, v x*D x ∂unitMeasure) := by
    exact (integral_sub hig₁ (hv.mul hD).integrable).trans (by rw [integral_sub hiD2 (hu.mul hD).integrable])
  have hfg : Integrable (fun x => f x+g x) unitMeasure := hif.add hig
  calc
    _ = ∫ x, (f x+g x)+u x*v x ∂unitMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp [f,g]; ring
    _ = _ := by
      rw [integral_add hfg (hu.mul hv).integrable,integral_add hif hig,hf,hg]
      ring

/-- The exact actual-graphon identity used in `eq:s7codeg`. -/
theorem codegree_centered_expansion (U : Graphon) :
    ∀ᵐ p ∂squareMeasure, codegree U p.1 p.2=
      rowDegree U p.1*rowDegree U p.2+(∫ z, degreeDeviation U z^2 ∂unitMeasure)-
      centeredAction U (degreeDeviation U) p.1-centeredAction U (degreeDeviation U) p.2+
      centeredSquare U p.1 p.2 := by
  have hrows := bounded_rows (centeredKernel_bounded U)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrows,
    Measure.quasiMeasurePreserving_snd.ae hrows,
    Measure.quasiMeasurePreserving_fst.ae (centeredKernel_row_zero U),
    Measure.quasiMeasurePreserving_snd.ae (centeredKernel_row_zero U)] with p hx hy hx0 hy0
  have h := integral_centered_product (rowDegree U p.1) (rowDegree U p.2)
    (degreeDeviation_bounded U) hx hy (integral_degreeDeviation U) hx0 hy0
  change (∫ z, U (p.1,z)*U (p.2,z) ∂unitMeasure)=_
  convert h using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by unfold centeredKernel degreeDeviation; ring

end SparseLowerTail.Section07

import SparseLowerTail.Section06.InsertionVariation

/-! The insertion inequality for arbitrary a.e. graphon representatives and
measurable bounded vertex profiles. This removes pointwise-representative
restrictions from the constructed first variation. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section04

def profileRepresentative (v : ℝ → ℝ) (hv : AEMeasurable v unitMeasure) : VertexProfile where
  toFun x := clampUnit (hv.mk v x)
  measurable := measurable_clampUnit.comp hv.measurable_mk
  bounded x := clampUnit_mem (hv.mk v x)

theorem profileRepresentative_ae {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure, v x ∈ Icc (0:ℝ) 1) :
    (profileRepresentative v hv).toFun =ᵐ[unitMeasure] v := by
  filter_upwards [hv.ae_eq_mk,hb] with x hx hbx
  change clampUnit (hv.mk v x)=v x
  rw [← hx,clampUnit_eq hbx]

theorem rowQuadratic_congr_ae {U W : Graphon} {v w : ℝ → ℝ}
    (hU : U.toFun =ᵐ[squareMeasure] W.toFun) (hv : v =ᵐ[unitMeasure] w) :
    rowQuadratic U v=rowQuadratic W w := by
  apply integral_congr_ae
  filter_upwards [hU,Measure.quasiMeasurePreserving_fst.ae hv,
    Measure.quasiMeasurePreserving_snd.ae hv] with p hp hx hy
  rw [hp,hx,hy]

theorem rowFunctional_congr_ae {U W : Graphon} {v w : ℝ → ℝ} (μ : ℝ)
    (hU : U.toFun =ᵐ[squareMeasure] W.toFun) (hv : v =ᵐ[unitMeasure] w) :
    rowFunctional U μ v=rowFunctional W μ w := by
  unfold rowFunctional
  rw [rowQuadratic_congr_ae hU hv,integral_congr_ae (hv.mono fun x hx => congrArg entropy hx)]

theorem graphonMultiplier_congr_ae {U W : Graphon}
    (hU : U.toFun =ᵐ[squareMeasure] W.toFun) (r : ℝ) :
    graphonMultiplier U r=graphonMultiplier W r := by
  have he : edgeDensity U=edgeDensity W := integral_congr_ae hU
  unfold graphonMultiplier
  rw [cost_congr_ae hU,he]

theorem vertexMean_congr_ae {U W : Graphon}
    (hU : U.toFun =ᵐ[squareMeasure] W.toFun) (r : ℝ) : vertexMean U r=vertexMean W r := by
  unfold vertexMean
  rw [cost_congr_ae hU,graphonMultiplier_congr_ae hU]

/-- The complete arbitrary-profile inequality in `lem:insertion`. -/
theorem rowFunctional_ge_vertexMean (hSampling : UniformSampling)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure, v x ∈ Icc (0:ℝ) 1) :
    vertexMean U r ≤ rowFunctional U (graphonMultiplier U r) v := by
  let V := pointwiseRepresentative U
  let w := profileRepresentative v hv
  have he : V.toGraphon.toFun =ᵐ[squareMeasure] U.toFun := pointwiseRepresentative_ae U
  have hw : w.toFun =ᵐ[unitMeasure] v := profileRepresentative_ae hv hb
  have hV : IsMinimizer r V.toGraphon := (isMinimizer_congr_ae he).mpr hU
  have h := rowFunctional_ge_vertexMean_pointwise hSampling hr V hV w
  rw [vertexMean_congr_ae he,graphonMultiplier_congr_ae he,
    rowFunctional_congr_ae _ he hw] at h
  exact h

/-- Integral operator applied to a row profile. -/
def rowOperator (U : Graphon) (v : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, U (y,z)*v z ∂unitMeasure

theorem rowOperator_row (U : Graphon) (x y : ℝ) :
    rowOperator U (fun z => U (x,z)) y=codegree U x y := by
  apply integral_congr_ae
  exact Eventually.of_forall fun z => mul_comm _ _

/-- The quadratic form of almost every row is the rooted triangle density. -/
theorem rowQuadratic_row_ae (U : Graphon) :
    ∀ᵐ x ∂unitMeasure, rowQuadratic U (fun y => U (x,y))=rowTriangle U x := by
  filter_upwards [(graphon_integrable U).prod_right_ae,
    Measure.ae_ae_of_ae_prod U.bounded] with x hmeas hb
  have hrow : BoundedObservable unitMeasure (fun y => U (x,y)) := by
    refine ⟨hmeas.aemeasurable,1,by norm_num,?_⟩
    filter_upwards [hb] with y hy
    simpa only [Real.norm_eq_abs,abs_of_nonneg hy.1] using hy.2
  have hi := (((hrow.comp Measure.quasiMeasurePreserving_fst).mul
    (graphon_boundedObservable U)).mul (hrow.comp Measure.quasiMeasurePreserving_snd)).integrable
  unfold rowQuadratic rowTriangle
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change (∫ z, U (x,y)*U (y,z)*U (x,z) ∂unitMeasure)=U (x,y)*codegree U x y
    rw [codegree,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by ring

/-- The remaining two assertions in `lem:insertion`, for actual rows. -/
theorem minimizer_row_functional (hSampling : UniformSampling)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure,
      AEMeasurable (fun y => U (x,y)) unitMeasure ∧
      (∀ᵐ y ∂unitMeasure, U (x,y) ∈ Icc (0:ℝ) 1) ∧
      rowFunctional U (graphonMultiplier U r) (fun y => U (x,y))=vertexMean U r ∧
      (∀ᵐ y ∂unitMeasure, Real.log (U (x,y))+
        graphonMultiplier U r*rowOperator U (fun z => U (x,z)) y=0) := by
  filter_upwards [(graphon_integrable U).prod_right_ae,
    Measure.ae_ae_of_ae_prod U.bounded,rowQuadratic_row_ae U,
    minimizer_vertex_stationary hSampling hr hU,
    Measure.ae_ae_of_ae_prod (minimizer_log_equation hr hU)] with x hm hb hQ hV hEL
  refine ⟨hm.aemeasurable,hb,?_,?_⟩
  · unfold rowFunctional
    rw [hQ]
    exact hV
  · filter_upwards [hEL] with y hy
    rw [rowOperator_row]
    linarith

/-- Almost every minimizer row globally minimizes the row functional over all
measurable [0,1]-valued profiles. -/
theorem minimizer_rows_minimize (hSampling : UniformSampling)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U) :
    ∀ᵐ x ∂unitMeasure, ∀ v : ℝ → ℝ, AEMeasurable v unitMeasure →
      (∀ᵐ y ∂unitMeasure, v y ∈ Icc (0:ℝ) 1) →
      rowFunctional U (graphonMultiplier U r) (fun y => U (x,y)) ≤
        rowFunctional U (graphonMultiplier U r) v := by
  filter_upwards [minimizer_row_functional hSampling hr hU] with x hx
  intro v hv hb
  rw [hx.2.2.1]
  exact rowFunctional_ge_vertexMean hSampling hr hU hv hb

end SparseLowerTail.Section06

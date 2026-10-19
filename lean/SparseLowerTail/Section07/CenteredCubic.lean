import SparseLowerTail.Section07.SpectralQuadratic

/-! The cubic block identity in `lem:spectral`, proved with actual bounded
kernel integrals and Fubini, rather than assumed as a graphon-specific spectral fact. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

/-- The signed cubic integral of the actual centered kernel. -/
def centeredCube (U : Graphon) : ℝ :=
  ∫ p : ℝ × (ℝ × ℝ), centeredKernel U (p.1,p.2.1)*centeredKernel U (p.2.1,p.2.2)*
    centeredKernel U (p.1,p.2.2) ∂cubeMeasure

theorem centeredAction_bounded (U : Graphon) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) : BoundedObservable unitMeasure (centeredAction U f) :=
  ((centeredKernel_bounded U).mul (hf.comp Measure.quasiMeasurePreserving_snd)).integral_left

theorem centeredSquare_bounded (U : Graphon) :
    BoundedObservable squareMeasure (fun p => centeredSquare U p.1 p.2) :=
  (((centeredKernel_bounded U).comp TriangleIntegration.edgeZ_qmp).mul
    ((centeredKernel_bounded U).comp TriangleIntegration.edgeY_qmp)).integral_left

/-- A vertex factor annihilates the square kernel because K1=0. -/
theorem integral_centeredSquare_vertex (U : Graphon) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    (∫ p, f p.1*centeredSquare U p.1 p.2 ∂squareMeasure)=0 := by
  let H := fun p : (ℝ × ℝ) × ℝ => f p.1.1*centeredKernel U (p.1.1,p.2)*centeredKernel U (p.1.2,p.2)
  have hx := hf.comp (Measure.quasiMeasurePreserving_fst.comp TriangleIntegration.edgeX_qmp)
  have hZ := (centeredKernel_bounded U).comp TriangleIntegration.edgeZ_qmp
  have hY := (centeredKernel_bounded U).comp TriangleIntegration.edgeY_qmp
  have hX := (centeredKernel_bounded U).comp TriangleIntegration.edgeX_qmp
  have hH : BoundedObservable TriangleIntegration.tripleMeasure H := (hx.mul hZ).mul hY
  have hstart : (∫ p, f p.1*centeredSquare U p.1 p.2 ∂squareMeasure)=
      ∫ p, H p ∂TriangleIntegration.tripleMeasure := by
    rw [integral_prod _ hH.integrable]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      dsimp [H,centeredSquare]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
  rw [hstart]
  have he : (∫ p, H p ∂TriangleIntegration.tripleMeasure)=
      ∫ p, f p.1.2*centeredKernel U (p.1.1,p.1.2)*centeredKernel U (p.1.1,p.2)
        ∂TriangleIntegration.tripleMeasure := by
    rw [← TriangleIntegration.cycle_preserving.integral_comp
      TriangleIntegration.cycle.measurableEmbedding H]
    apply integral_congr_ae
    filter_upwards [TriangleIntegration.edgeX_qmp.ae (centeredKernel_symmetric U),
      TriangleIntegration.edgeZ_qmp.ae (centeredKernel_symmetric U)] with p hxy hxz
    change centeredKernel U (p.1.2,p.1.1)=centeredKernel U (p.1.1,p.1.2) at hxy
    change centeredKernel U (p.2,p.1.1)=centeredKernel U (p.1.1,p.2) at hxz
    change f p.1.2*centeredKernel U (p.1.2,p.1.1)*centeredKernel U (p.2,p.1.1)=_
    rw [hxy,hxz]
  rw [he]
  have hy := hf.comp (Measure.quasiMeasurePreserving_snd.comp TriangleIntegration.edgeX_qmp)
  have hi : Integrable (fun p : (ℝ × ℝ) × ℝ =>
      f p.1.2*centeredKernel U (p.1.1,p.1.2)*centeredKernel U (p.1.1,p.2))
      TriangleIntegration.tripleMeasure := ((hy.mul hX).mul hZ).integrable
  rw [integral_prod _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (centeredKernel_row_zero U)] with p hp
  rw [integral_const_mul,hp,mul_zero]
  rfl

/-- The square kernel is symmetric pointwise, independently of representatives. -/
theorem centeredSquare_symmetric (U : Graphon) (x y : ℝ) :
    centeredSquare U x y=centeredSquare U y x := by
  apply integral_congr_ae
  exact Eventually.of_forall fun z => mul_comm _ _

theorem integral_centeredSquare_vertex_right (U : Graphon) {f : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) :
    (∫ p, f p.2*centeredSquare U p.1 p.2 ∂squareMeasure)=0 := by
  calc
    _ = ∫ p, f p.swap.1*centeredSquare U p.swap.1 p.swap.2 ∂squareMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only
        rw [centeredSquare_symmetric U p.1 p.2]
        rfl
    _ = ∫ p, f p.1*centeredSquare U p.1 p.2 ∂squareMeasure :=
      Measure.measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
        (fun p => f p.1*centeredSquare U p.1 p.2)
    _ = 0 := integral_centeredSquare_vertex U hf

/-- The contraction of K against K² is its actual cubic integral. -/
theorem centeredCube_eq_integral_square (U : Graphon) :
    centeredCube U=∫ p, centeredKernel U p*centeredSquare U p.1 p.2 ∂squareMeasure := by
  have hX := (centeredKernel_bounded U).comp TriangleIntegration.edgeX_qmp
  have hY := (centeredKernel_bounded U).comp TriangleIntegration.edgeY_qmp
  have hZ := (centeredKernel_bounded U).comp TriangleIntegration.edgeZ_qmp
  unfold centeredCube
  rw [← (measurePreserving_prodAssoc unitMeasure unitMeasure unitMeasure).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun p : ℝ × (ℝ × ℝ) => centeredKernel U (p.1,p.2.1)*centeredKernel U (p.2.1,p.2.2)*
      centeredKernel U (p.1,p.2.2))]
  have he : (fun p : (ℝ × ℝ) × ℝ =>
      centeredKernel U (p.1.1,p.1.2)*centeredKernel U (p.1.2,p.2)*centeredKernel U (p.1.1,p.2))=
      (fun p => centeredKernel U p.1*(centeredKernel U (p.1.1,p.2)*centeredKernel U (p.1.2,p.2))) := by
    funext p; ring
  change (∫ p, centeredKernel U (p.1.1,p.1.2)*centeredKernel U (p.1.2,p.2)*centeredKernel U (p.1.1,p.2)
    ∂TriangleIntegration.tripleMeasure)=_
  rw [he,integral_prod _ ((hX.mul (hZ.mul hY)).integrable)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    dsimp only
    rw [integral_const_mul]
    rfl

/-- Contracting the graphon with K² leaves only the negative cubic K term. -/
theorem integral_graphon_centeredSquare (U : Graphon) :
    (∫ p, U p*centeredSquare U p.1 p.2 ∂squareMeasure)=-centeredCube U := by
  have hS := centeredSquare_bounded U
  have h₁ := (((rowDegree_bounded U).comp Measure.quasiMeasurePreserving_fst).mul hS).integrable
  have h₂ := (((rowDegree_bounded U).comp Measure.quasiMeasurePreserving_snd).mul hS).integrable
  have h₃ := hS.integrable.const_mul (edgeDensity U)
  have h₄ := ((centeredKernel_bounded U).mul hS).integrable
  have h₁₂ : Integrable (fun p => rowDegree U p.1*centeredSquare U p.1 p.2+
      rowDegree U p.2*centeredSquare U p.1 p.2) squareMeasure := h₁.add h₂
  have h₁₂₃ : Integrable (fun p => (rowDegree U p.1*centeredSquare U p.1 p.2+
      rowDegree U p.2*centeredSquare U p.1 p.2)-edgeDensity U*centeredSquare U p.1 p.2)
      squareMeasure := h₁₂.sub h₃
  have hz : (∫ p, centeredSquare U p.1 p.2 ∂squareMeasure)=0 := by
    simpa only [one_mul] using integral_centeredSquare_vertex U (BoundedObservable.const 1)
  calc
    _ = ∫ p, ((rowDegree U p.1*centeredSquare U p.1 p.2+
        rowDegree U p.2*centeredSquare U p.1 p.2)-edgeDensity U*centeredSquare U p.1 p.2)-
        centeredKernel U p*centeredSquare U p.1 p.2 ∂squareMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by unfold centeredKernel; ring
    _ = _ := by
      rw [integral_sub h₁₂₃ h₄,integral_sub h₁₂ h₃,integral_add h₁ h₂,integral_const_mul,
        integral_centeredSquare_vertex U (rowDegree_bounded U),
        integral_centeredSquare_vertex_right U (rowDegree_bounded U),hz,
        ← centeredCube_eq_integral_square U]
      ring

/-- The degree second moment is m² plus the variance. -/
theorem degree_second_moment (U : Graphon) :
    (∫ x, rowDegree U x^2 ∂unitMeasure)=edgeDensity U^2+
      (∫ x, degreeDeviation U x^2 ∂unitMeasure) := by
  have hD := degreeDeviation_bounded U
  have hsq : Integrable (fun x => degreeDeviation U x^2) unitMeasure := by
    simpa only [pow_two] using (hD.mul hD).integrable
  have hi : Integrable (fun x => degreeDeviation U x^2+2*edgeDensity U*degreeDeviation U x)
      unitMeasure := hsq.add (hD.integrable.const_mul _)
  calc
    _ = ∫ x, (degreeDeviation U x^2+2*edgeDensity U*degreeDeviation U x)+edgeDensity U^2 ∂unitMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by unfold degreeDeviation; ring
    _ = _ := by
      rw [integral_add hi (integrable_const _),integral_add hsq (hD.integrable.const_mul _),
        integral_const_mul,integral_degreeDeviation]
      simp only [integral_const,measureReal_univ_eq_one,one_smul,mul_zero,add_zero]
      ring

/-- The first term of the codegree contraction, expanded around the mean degree. -/
theorem integral_graphon_degree_product (U : Graphon) :
    (∫ p, U p*(rowDegree U p.1*rowDegree U p.2) ∂squareMeasure)=
      edgeDensity U^3+2*edgeDensity U*(∫ x, degreeDeviation U x^2 ∂unitMeasure)-
      (∫ p, centeredKernel U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure) := by
  have hd := (rowDegree_bounded U).integrable
  have hD := (degreeDeviation_bounded U).integrable
  have hq := centeredKernel_quadratic U hd
  rw [integral_rowDegree] at hq
  have hsq : (∫ x, rowDegree U x*rowDegree U x ∂unitMeasure)=
      edgeDensity U^2+(∫ x, degreeDeviation U x^2 ∂unitMeasure) := by
    simpa only [pow_two] using degree_second_moment U
  rw [hsq] at hq
  have hc := centeredKernel_quadratic_eq_neg_centered U hd
  rw [integral_rowDegree] at hc
  change (∫ p, centeredKernel U p*(rowDegree U p.1*rowDegree U p.2) ∂squareMeasure)=
    -(∫ p, U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure) at hc
  have hqD := centeredKernel_quadratic U hD
  rw [integral_degreeDeviation] at hqD
  nlinarith

/-- The bilinear contraction of D with K D, expressed as a pair integral. -/
theorem integral_degree_centeredAction (U : Graphon) :
    (∫ x, rowDegree U x*centeredAction U (degreeDeviation U) x ∂unitMeasure)=
      ∫ p, centeredKernel U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure := by
  have hD := degreeDeviation_bounded U
  have hA := centeredAction_bounded U hD
  have hprod := (centeredKernel_bounded U).mul
    ((hD.comp Measure.quasiMeasurePreserving_fst).mul (hD.comp Measure.quasiMeasurePreserving_snd))
  have he : (∫ x, degreeDeviation U x*centeredAction U (degreeDeviation U) x ∂unitMeasure)=
      ∫ p, centeredKernel U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure := by
    rw [integral_prod _ hprod.integrable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [centeredAction]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by ring
  calc
    _ = ∫ x, degreeDeviation U x*centeredAction U (degreeDeviation U) x+
        edgeDensity U*centeredAction U (degreeDeviation U) x ∂unitMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by unfold degreeDeviation; ring
    _ = _ := by
      rw [integral_add (hD.mul hA).integrable (hA.integrable.const_mul _),integral_const_mul,
        integral_centeredAction U hD.integrable,he,mul_zero,add_zero]

/-- The exact cubic block identity in `lem:spectral`, proved directly for
all actual graphons, without a spectral hypothesis. -/
theorem centered_cubic_identity (U : Graphon) :
    triangle U=edgeDensity U^3-centeredCube U+
      3*(edgeDensity U*(∫ x, degreeDeviation U x^2 ∂unitMeasure)-
        (∫ p, centeredKernel U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure)) := by
  let v := ∫ x, degreeDeviation U x^2 ∂unitMeasure
  let A := centeredAction U (degreeDeviation U)
  have hU := graphon_boundedObservable U
  have hd := rowDegree_bounded U
  have hA := centeredAction_bounded U (degreeDeviation_bounded U)
  have h₁ := (hU.mul ((hd.comp Measure.quasiMeasurePreserving_fst).mul
    (hd.comp Measure.quasiMeasurePreserving_snd))).integrable
  have h₂ := (hU.mul_const v).integrable
  have h₃ := (hU.mul (hA.comp Measure.quasiMeasurePreserving_fst)).integrable
  have h₄ := (hU.mul (hA.comp Measure.quasiMeasurePreserving_snd)).integrable
  have h₅ := (hU.mul (centeredSquare_bounded U)).integrable
  have hi₁₂ : Integrable (fun p => U p*(rowDegree U p.1*rowDegree U p.2)+U p*v) squareMeasure := h₁.add h₂
  have hi₁₂₃ : Integrable (fun p => (U p*(rowDegree U p.1*rowDegree U p.2)+U p*v)-U p*A p.1)
      squareMeasure := hi₁₂.sub h₃
  have hi₁₂₃₄ : Integrable (fun p => ((U p*(rowDegree U p.1*rowDegree U p.2)+U p*v)-U p*A p.1)-U p*A p.2)
      squareMeasure := hi₁₂₃.sub h₄
  have hax : (∫ p, U p*A p.1 ∂squareMeasure)=
      ∫ p, centeredKernel U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure :=
    (integral_graphon_vertex_test U hA.integrable).trans (integral_degree_centeredAction U)
  have hay : (∫ p, U p*A p.2 ∂squareMeasure)=
      ∫ p, centeredKernel U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure :=
    (integral_graphon_vertex_test_right U hA.integrable).trans (integral_degree_centeredAction U)
  rw [triangle_eq_integral_codegree]
  calc
    _ = ∫ p, (((U p*(rowDegree U p.1*rowDegree U p.2)+U p*v)-U p*A p.1)-U p*A p.2)+
        U p*centeredSquare U p.1 p.2 ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [codegree_centered_expansion U] with p hp
      rw [hp]
      dsimp [v,A]
      ring
    _ = _ := by
      rw [integral_add hi₁₂₃₄ h₅,integral_sub hi₁₂₃ h₄,integral_sub hi₁₂ h₃,
        integral_add h₁ h₂,integral_mul_const,hax,hay,integral_graphon_centeredSquare U,
        integral_graphon_degree_product U]
      dsimp [v]
      unfold edgeDensity
      ring

/-- Spectral form of the internally proved cubic identity. -/
theorem centered_spectral_cubic_identity (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    triangle U=edgeDensity U^3-(∑' i, S.eigenvalue i^3)+
      3*(edgeDensity U*(∫ x, degreeDeviation U x^2 ∂unitMeasure)-
        (∫ p, centeredKernel U p*(degreeDeviation U p.1*degreeDeviation U p.2) ∂squareMeasure)) := by
  rw [S.cube_sum]
  exact centered_cubic_identity U

/-- The nonnegative correction in the cubic identity gives the spectral lower
bound needed for both inequalities of `eq:s7tail`. -/
theorem centeredSpectrum_cube_lower (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    edgeDensity U^3-triangle U≤(∑' i, S.eigenvalue i^3) := by
  have he := centered_spectral_cubic_identity U S
  have hq := centeredKernel_quadratic_upper U S (degreeDeviation_bounded U)
  linarith

/-- Both actual graphon tail inequalities `eq:s7tail`. -/
theorem centeredSpectrum_tail_inequalities (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) :
    edgeDensity U^3-triangle U≤edgeDensity U*S.eigenvalue 0^2 ∧
    3*edgeDensity U*S.eigenvalue 0*(edgeDensity U-S.eigenvalue 0)≤triangle U := by
  have hlo := centeredSpectrum_cube_lower U S
  have htop := centeredSpectrum_cube_le_top U S
  have htail := centeredSpectrum_cube_le_tail U S
  exact ⟨hlo.trans htop,by linarith⟩

/-- A positive mean-cube gap forces a positive leading eigenvalue. -/
theorem centeredEigenvalue_pos_of_gap (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U)) (hgap : 0<edgeDensity U^3-triangle U) :
    0<S.eigenvalue 0 := by
  have hh := (centeredSpectrum_tail_inequalities U S).1
  have hn := S.eigenvalue_nonneg 0
  by_contra hc
  have hz : S.eigenvalue 0=0 := le_antisymm (le_of_not_gt hc) hn
  rw [hz] at hh
  nlinarith

/-- The small-target optimizer has a strictly positive mean-cube gap, so its
leading centered eigenvalue is nonzero. -/
theorem smallTarget_centeredEigenvalue_pos (external : KP26PenalizedReduction)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) {U : Graphon} (hU : IsMinimizer r U)
    (S : KernelSpectralExpansion (centeredKernel U)) : 0<S.eigenvalue 0 := by
  have hdata := smallTarget_optimizer_data external hr hU
  obtain ⟨hz,_,_,ht⟩ := smallTarget_support hr
  have hz01 : leftBranch r∈Ioo (0:ℝ) 1 :=
    ⟨hz.1,hz.2.trans_lt penalizedCrossing_mem_unit.2⟩
  apply centeredEigenvalue_pos_of_gap U S
  rw [hdata.1,hdata.2.2.2,← ht,mean_cube_sub_balancedTriangle]
  exact div_pos (pow_pos (sub_pos.mpr (branch_spec hz01.1 hz01.2).2.1) 3) (by norm_num)

/-- A genuine spectrum with a positive leading eigenvalue exists for every
small-target minimizer, from only the named classical external inputs. -/
theorem smallTarget_spectral_data (external : KP26PenalizedReduction)
    (hSpectral : PositiveKernelSpectralTheorem) (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) {U : Graphon} (hU : IsMinimizer r U) :
    ∃ S : KernelSpectralExpansion (centeredKernel U),
      0<S.eigenvalue 0 ∧ Summable S.eigenvalue ∧ (∑' i, S.eigenvalue i)≤edgeDensity U ∧
      (∫ x, S.eigenfunction 0 x ∂unitMeasure)=0 ∧
      (∀ᵐ x ∂unitMeasure, 0≤spectralDiagonal S x ∧
        spectralDiagonal S x≤2*rowDegree U x-edgeDensity U) ∧
      edgeDensity U^3-triangle U≤edgeDensity U*S.eigenvalue 0^2 ∧
      3*edgeDensity U*S.eigenvalue 0*(edgeDensity U-S.eigenvalue 0)≤triangle U := by
  have hdata := (smallTarget_data external hr).2 U hU
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hs := smallTarget_support hr
  have hz01 : leftBranch r∈Ioo (0:ℝ) 1 :=
    ⟨hs.1.1,hs.1.2.trans_lt penalizedCrossing_mem_unit.2⟩
  have hγ : 0≤branchMu (leftBranch r)/3 :=
    (div_pos (branchMu_pos hz01.1 hz01.2) (by norm_num)).le
  obtain ⟨S⟩ := centeredKernel_spectral_expansion hSpectral hSampling hr01 hγ hU hdata.2.2
  have hpos := smallTarget_centeredEigenvalue_pos external hr hU S
  refine ⟨S,hpos,(centeredKernel_trace_bound U S).1,(centeredKernel_trace_bound U S).2,
    centeredEigenfunction_mean_zero U S hpos,?_,(centeredSpectrum_tail_inequalities U S).1,
    (centeredSpectrum_tail_inequalities U S).2⟩
  filter_upwards [centeredKernel_diagonal_bound U S] with x hx
  exact hx.2

end SparseLowerTail.Section07

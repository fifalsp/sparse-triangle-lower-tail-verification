import SparseLowerTail.Section07.SetAverageCalculus
import SparseLowerTail.Section06.TwoWellRows

/-! The Jensen vertex bound eq:s7approxk for the actual eigenfunction sign blocks. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04 Section06

theorem vertexEntropy_eq_entropy (u : ℝ) : vertexEntropy u=entropy u+1-u := by
  unfold vertexEntropy entropy
  ring

theorem vertexEntropy_mem_Icc {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    vertexEntropy u∈Icc (0:ℝ) 2 := by
  rw [vertexEntropy_eq_entropy]
  have h0 := entropy_nonneg hu.1
  have h1 := entropy_le_one hu
  constructor <;> linarith [hu.1,hu.2]

theorem profile_vertexEntropy_integrable {v : ℝ→ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    Integrable (fun x => vertexEntropy (v x)) unitMeasure := by
  simp_rw [vertexEntropy_eq_entropy]
  exact (((profile_entropy_boundedObservable hv hb).integrable).add (integrable_const _)).sub
    (profile_boundedObservable hv hb).integrable

theorem setAverage_mem_unit {v : ℝ→ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) {P : Set ℝ}
    (hp : 0<unitMeasure.real P) : setAverage P v∈Icc (0:ℝ) 1 := by
  refine ⟨div_nonneg (integral_nonneg_of_ae (ae_restrict_of_ae (hb.mono fun _ hx => hx.1))) hp.le,?_⟩
  exact setAverage_le_const hp (profile_boundedObservable hv hb).integrable
    (ae_restrict_of_ae (hb.mono fun _ hx => hx.2))

/-- Weighted Jensen for vertex entropy, derived from entropy Jensen and linearity. -/
theorem weighted_vertexEntropy_jensen {v : ℝ→ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) {P : Set ℝ}
    (hp : 0<unitMeasure.real P) :
    unitMeasure.real P*vertexEntropy (setAverage P v)≤∫ x in P,vertexEntropy (v x) ∂unitMeasure := by
  have hi := (profile_boundedObservable hv hb).integrable
  have he := (profile_entropy_boundedObservable hv hb).integrable
  have hn : unitMeasure P≠0 := by
    intro hn
    simp [measureReal_def,hn] at hp
  have hj := strictConvexOn_entropy.convexOn.map_set_average_le continuous_entropy.continuousOn
    isClosed_Ici hn (measure_ne_top _ _)
    (ae_restrict_of_ae (hb.mono fun _ hx => hx.1)) hi.integrableOn he.integrableOn
  rw [MeasureTheory.setAverage_eq,MeasureTheory.setAverage_eq] at hj
  simp only [smul_eq_mul] at hj
  have hmean : (unitMeasure.real P)⁻¹*(∫ x in P,v x ∂unitMeasure)=setAverage P v := by
    dsimp [setAverage]
    ring
  rw [hmean] at hj
  have hj' := mul_le_mul_of_nonneg_left hj hp.le
  have hcancel : unitMeasure.real P*(unitMeasure.real P)⁻¹=1 := mul_inv_cancel₀ hp.ne'
  have hvi : unitMeasure.real P*setAverage P v=∫ x in P,v x ∂unitMeasure := by
    dsimp [setAverage]
    field_simp
  simp_rw [vertexEntropy_eq_entropy]
  rw [integral_sub (f := fun x => entropy (v x)+1) (g := v) (he.add (integrable_const _)).integrableOn hi.integrableOn,
    integral_add (f := fun x => entropy (v x)) (g := fun _ => (1:ℝ)) he.integrableOn (integrable_const _),setIntegral_const,smul_eq_mul]
  rw [←mul_assoc,hcancel,one_mul] at hj'
  nlinarith

/-- Passing from mass-weighted to equal-weighted averages costs at most 1−2p₀. -/
theorem unweighted_vertex_bound {p p₀ a b K : ℝ} (hp : p₀≤p) (hp' : p≤1-p₀)
    (ha : a∈Icc (0:ℝ) 2) (hb : b∈Icc (0:ℝ) 2)
    (hweighted : p*a+(1-p)*b≤K) : (a+b)/2≤K+1-2*p₀ := by
  rcases le_total p (1/2) with h | h
  · have h1 := mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr h)
    have h2 := mul_nonneg (sub_nonneg.mpr h) hb.1
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr h)
    have h2 := mul_nonneg (sub_nonneg.mpr h) ha.1
    nlinarith

/-- The profile form of eq:s7approxk, before inserting an actual minimizer row. -/
theorem profile_vertex_block_bound {v : ℝ→ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) {P : Set ℝ} (hP : MeasurableSet P)
    {p₀ K : ℝ} (hp₀ : 0<p₀) (hp : p₀≤unitMeasure.real P)
    (hp' : p₀≤unitMeasure.real Pᶜ) (hrow : (∫ x,vertexEntropy (v x) ∂unitMeasure)=K) :
    (vertexEntropy (setAverage P v)+vertexEntropy (setAverage Pᶜ v))/2≤K+1-2*p₀ := by
  have hmass : unitMeasure.real P+unitMeasure.real Pᶜ=1 := by
    simpa using measureReal_add_measureReal_compl (μ:=unitMeasure) hP
  have hpos := hp₀.trans_le hp
  have hpos' := hp₀.trans_le hp'
  have hsum := integral_add_compl hP (profile_vertexEntropy_integrable hv hb)
  have h1 := weighted_vertexEntropy_jensen hv hb hpos
  have h2 := weighted_vertexEntropy_jensen hv hb hpos'
  apply unweighted_vertex_bound hp (by linarith)
    (vertexEntropy_mem_Icc (setAverage_mem_unit hv hb hpos))
    (vertexEntropy_mem_Icc (setAverage_mem_unit hv hb hpos'))
  rw [hrow] at hsum
  have hc : unitMeasure.real Pᶜ=1-unitMeasure.real P := by linarith
  rw [hc] at h2
  linarith

/-- Full actual Jensen/vertex conclusion on the sign blocks of the leading eigenfunction. -/
theorem smallTarget_rowVertex_bound (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ x ∂unitMeasure,
      (vertexEntropy (setAverage P (fun y => U (x,y)))+
       vertexEntropy (setAverage Pᶜ (fun y => U (x,y))))/2≤vertexMean U r+1-(M^2)⁻¹ := by
  let M := Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0)
  let P := positiveSignBlock (S.eigenfunction 0)
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hM : 0<M := lt_of_lt_of_le zero_lt_one hblocks.1
  have hP : MeasurableSet P := positiveSignBlock_measurable (S.eigenfunction_measurable 0)
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  filter_upwards [(graphon_integrable U).prod_right_ae,Measure.ae_ae_of_ae_prod U.bounded,
    minimizer_vertex_stationary hSampling hr01 hU,minimizer_row_vertexEntropy hr01 hU]
      with x hx hb hs hk
  have hh := profile_vertex_block_bound hx.aemeasurable hb hP
    (by positivity : (0:ℝ)<1/(2*M^2)) hblocks.2.1 hblocks.2.2.2.1 (hk.trans hs)
  have he : 2*(1/(2*M^2))=(M^2)⁻¹ := by field_simp
  rwa [he] at hh

end SparseLowerTail.Section07

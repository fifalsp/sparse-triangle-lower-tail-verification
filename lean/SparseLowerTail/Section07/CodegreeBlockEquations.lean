import SparseLowerTail.Section07.ExponentialRowEstimate

/-! Averaged Euler equations at the nonnegative surrogate codegrees c₊,c₋. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- Codegree approximation with the constant sign on each actual block. -/
theorem smallTarget_codegree_block_errors (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let m := edgeDensity U
    let A := m+graphonMultiplier U r*r^3
    let M := Real.sqrt (A/S.eigenvalue 0)
    let E := rowCodegreeError (graphonMultiplier U r*r^3/2) m (S.eigenvalue 0) M (m-S.eigenvalue 0) A
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ x ∂unitMeasure,
      setAverage P (fun y => |codegree U x y-(m*rowDegree U x+S.eigenvalue 0^2*S.eigenfunction 0 x)|)≤E ∧
      setAverage Pᶜ (fun y => |codegree U x y-(m*rowDegree U x-S.eigenvalue 0^2*S.eigenfunction 0 x)|)≤E := by
  dsimp only
  have hmeas := positiveSignBlock_measurable (S.eigenfunction_measurable 0)
  filter_upwards [smallTarget_codegree_average_error external hSampling hr hU S (Or.inl rfl),
    smallTarget_codegree_average_error external hSampling hr hU S (Or.inr rfl)] with x hx hy
  constructor
  · convert hx using 1
    apply congrArg (fun v : ℝ => v/unitMeasure.real (positiveSignBlock (S.eigenfunction 0)))
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas] with y hy
    simp [signBlockFunction,show 0≤S.eigenfunction 0 y from hy]
  · convert hy using 1
    apply congrArg (fun v : ℝ => v/unitMeasure.real (positiveSignBlock (S.eigenfunction 0))ᶜ)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hmeas.compl] with y hy
    simp [signBlockFunction,show ¬0≤S.eigenfunction 0 y from hy,sub_eq_add_neg]

/-- The actual averaged exponential equation at c₊ and c₋. -/
theorem smallTarget_surrogate_exponential_errors (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let μ := graphonMultiplier U r
    let m := edgeDensity U
    let A := m+μ*r^3
    let M := Real.sqrt (A/S.eigenvalue 0)
    let E := rowCodegreeError (μ*r^3/2) m (S.eigenvalue 0) M (m-S.eigenvalue 0) A
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ x ∂unitMeasure,
      |setAverage P (fun y => U (x,y))-Real.exp (-μ*(m*rowDegree U x+S.eigenvalue 0^2*S.eigenfunction 0 x))|≤μ*E ∧
      |setAverage Pᶜ (fun y => U (x,y))-Real.exp (-μ*(m*rowDegree U x-S.eigenvalue 0^2*S.eigenfunction 0 x))|≤μ*E := by
  dsimp only
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hμ := minimizer_multiplier_pos hr01 hU
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hMpos : 0<Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0) :=
    lt_of_lt_of_le zero_lt_one hblocks.1
  have hp : 0<unitMeasure.real (positiveSignBlock (S.eigenfunction 0)) :=
    (by positivity : (0:ℝ)<1/(2*(Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0))^2)).trans_le hblocks.2.1
  have hn : 0<unitMeasure.real (positiveSignBlock (S.eigenfunction 0))ᶜ :=
    (by positivity : (0:ℝ)<1/(2*(Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0))^2)).trans_le hblocks.2.2.2.1
  filter_upwards [smallTarget_codegree_block_errors external hSampling hr hU S,
    centered_surrogate_codegrees_nonneg U S,
    boundedObservable_sections (graphon_boundedObservable U),
    boundedObservable_sections (codegree_boundedObservable U),
    Measure.ae_ae_of_ae_prod (minimizer_exp_equation hr01 hU),
    Measure.ae_ae_of_ae_prod (codegree_mem_Icc_ae U)] with x hx hc hu hC he hpos
  have hCpos : ∀ᵐ y ∂unitMeasure, 0≤codegree U x y := hpos.mono fun y hy => hy.1
  constructor
  · exact (setAverage_exp_equation_error hu.integrable hC.integrable hp hμ.le hc.1
      (ae_restrict_of_ae hCpos) (ae_restrict_of_ae he)).trans
      (mul_le_mul_of_nonneg_left hx.1 hμ.le)
  · exact (setAverage_exp_equation_error hu.integrable hC.integrable hn hμ.le hc.2
      (ae_restrict_of_ae hCpos) (ae_restrict_of_ae he)).trans
      (mul_le_mul_of_nonneg_left hx.2 hμ.le)

end SparseLowerTail.Section07

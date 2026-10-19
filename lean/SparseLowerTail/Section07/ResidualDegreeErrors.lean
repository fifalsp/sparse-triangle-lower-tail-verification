import SparseLowerTail.Section07.SetAverageCalculus

/-! The third, fifth, and seventh terms of the codegree error E_C, proved
from actual residual actions and their row and L² estimates. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- Small-target degree bounds, with the supporting penalty discharged. -/
theorem smallTarget_degree_data (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) :
    (∀ᵐ x ∂unitMeasure, edgeDensity U/2≤rowDegree U x ∧
      rowDegree U x≤edgeDensity U+graphonMultiplier U r*r^3/2) ∧
    (∫ x, |degreeDeviation U x| ∂unitMeasure)≤graphonMultiplier U r*r^3 ∧
    (∫ x, degreeDeviation U x^2 ∂unitMeasure)≤(graphonMultiplier U r*r^3/2)*edgeDensity U/2 := by
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hμ := minimizer_multiplier_pos hr01 hU
  have hμeq := (smallTarget_optimizer_data external hr hU).2.2.1
  have hγ : 0≤branchMu (leftBranch r)/3 := by rw [← hμeq]; positivity
  exact penalized_degree_estimates hSampling hr01 hγ hU ((smallTarget_data external hr).2 U hU).2.2

/-- Three residual-error bounds used in the actual codegree estimate. -/
theorem smallTarget_residual_degree_errors (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U))
    {P : Set ℝ} (hP : P=positiveSignBlock (S.eigenfunction 0) ∨ P=(positiveSignBlock (S.eigenfunction 0))ᶜ) :
    let m := edgeDensity U
    let η := graphonMultiplier U r*r^3/2
    let A := m+graphonMultiplier U r*r^3
    let s := m-S.eigenvalue 0
    let M := Real.sqrt (A/S.eigenvalue 0)
    (∀ᵐ x ∂unitMeasure, |kernelAction (spectralRemainder U S) (degreeDeviation U) x|≤
      Real.sqrt (A*s*η*m/2)) ∧
    setAverage P (fun x => |kernelAction (spectralRemainder U S) (degreeDeviation U) x|)≤
      2*M^2*s*Real.sqrt (η*m/2) ∧
    (∀ᵐ x ∂unitMeasure, setAverage P (fun y => |residualSquare U S x y|)≤
      2*M^2*s*Real.sqrt (s*A)) := by
  dsimp only
  let m := edgeDensity U
  let η := graphonMultiplier U r*r^3/2
  let A := m+graphonMultiplier U r*r^3
  let s := m-S.eigenvalue 0
  let M := Real.sqrt (A/S.eigenvalue 0)
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hev := smallTarget_centeredEigenvalue_pos external hr hU S
  have hψ := minimizer_eigenfunction_bounded hSampling hr01 hU S hev
  have hR := spectralRemainder_bounded S hψ
  have hD := degreeDeviation_bounded U
  have hRD := kernelAction_bounded hR hD
  have hμ := minimizer_multiplier_pos hr01 hU
  have hrpos := hr.1
  have hm : 0≤m := (Section02.edgeDensity_mem_Icc U).1
  have hη : 0≤η := by dsimp [η]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hs : 0≤s := sub_nonneg.mpr (centeredEigenvalue_le_mean U S 0)
  have hV : 0≤η*m/2 := by positivity
  have hsA : 0≤s*A := mul_nonneg hs hA
  have hdegree := (smallTarget_degree_data external hSampling hr hU).2.2
  change (∫ x, degreeDeviation U x^2 ∂unitMeasure)≤η*m/2 at hdegree
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hM : 1≤M := hblocks.1
  have hMpos : 0<M := by linarith
  have hmass : 1/(2*M^2)≤unitMeasure.real P := by
    rcases hP with rfl | rfl
    · exact hblocks.2.1
    · exact hblocks.2.2.2.1
  obtain ⟨CD,_,hCD⟩ := hD.bound
  have hDlp := MemLp.of_bound (p := (2:ENNReal)) hD.measurable.aestronglyMeasurable CD hCD
  constructor
  · filter_upwards [minimizer_residualAction_bound hSampling hr01 hU S hDlp] with x hx
    have hh := hx.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdegree) (Real.sqrt_nonneg _))
    change _≤Real.sqrt (A*s*η*m/2)
    change _≤Real.sqrt (s*A)*Real.sqrt (η*m/2) at hh
    rw [← Real.sqrt_mul hsA] at hh
    convert hh using 1; congr 1; ring
  constructor
  · obtain ⟨CRD,_,hCRD⟩ := hRD.bound
    have hRDlp := MemLp.of_bound (p := (2:ENNReal)) hRD.measurable.aestronglyMeasurable CRD hCRD
    have hsq := (spectralRemainder_action_sq_le U S hψ hD).trans
      (mul_le_mul_of_nonneg_left hdegree (sq_nonneg s))
    have hBsq : (s*Real.sqrt (η*m/2))^2=s^2*(η*m/2) := by rw [mul_pow,Real.sq_sqrt hV]
    rw [← hBsq] at hsq
    have hh := setAverage_abs_le_of_square hRDlp hMpos
      (mul_nonneg hs (Real.sqrt_nonneg _)) hmass hsq
    convert hh using 1; ring
  · filter_upwards [boundedObservable_sections hR,
      minimizer_residualSquare_row_bound hSampling hr01 hU S hev] with x hx hsq
    have hrow : BoundedObservable unitMeasure (fun y => residualSquare U S x y) := by
      simpa only [residualSquare_eq_action] using kernelAction_bounded hR hx
    obtain ⟨C,_,hC⟩ := hrow.bound
    have hlp := MemLp.of_bound (p := (2:ENNReal)) hrow.measurable.aestronglyMeasurable C hC
    have hBsq : (s*Real.sqrt (s*A))^2=s^2*(s*A) := by rw [mul_pow,Real.sq_sqrt hsA]
    change (∫ y, residualSquare U S x y^2 ∂unitMeasure)≤s^2*(s*A) at hsq
    rw [← hBsq] at hsq
    have hh := setAverage_abs_le_of_square hlp hMpos
      (mul_nonneg hs (Real.sqrt_nonneg _)) hmass hsq
    convert hh using 1; ring

end SparseLowerTail.Section07

import SparseLowerTail.Section07.ResidualDegreeErrors

/-! The seven-term codegree average bound `eq:s7EC`. Every input is derived
from the actual minimizing graphon and its explicit classical spectral data. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section07
open Section04

set_option maxHeartbeats 1000000 in
theorem smallTarget_codegree_average_error (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U))
    {P : Set ℝ} (hP : P=positiveSignBlock (S.eigenfunction 0) ∨ P=(positiveSignBlock (S.eigenfunction 0))ᶜ) :
    let m := edgeDensity U
    let η := graphonMultiplier U r*r^3/2
    let A := m+graphonMultiplier U r*r^3
    let s := m-S.eigenvalue 0
    let M := Real.sqrt (A/S.eigenvalue 0)
    ∀ᵐ x ∂unitMeasure,
      setAverage P (fun y => |codegree U x y-(m*rowDegree U x+
        S.eigenvalue 0^2*S.eigenfunction 0 x*signBlockFunction (S.eigenfunction 0) y)|)≤
      rowCodegreeError η m (S.eigenvalue 0) M s A := by
  dsimp only
  let m := edgeDensity U
  let η := graphonMultiplier U r*r^3/2
  let A := m+graphonMultiplier U r*r^3
  let s := m-S.eigenvalue 0
  let M := Real.sqrt (A/S.eigenvalue 0)
  let ev := S.eigenvalue 0
  let ψ := S.eigenfunction 0
  let D := degreeDeviation U
  let R := spectralRemainder U S
  let RD := kernelAction R D
  let β := degreeEigenfunctionPair U S
  let V := ∫ y, D y^2 ∂unitMeasure
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hev : 0<ev := smallTarget_centeredEigenvalue_pos external hr hU S
  have hψ := minimizer_eigenfunction_bounded hSampling hr01 hU S hev
  have hR := spectralRemainder_bounded S hψ
  have hRD := kernelAction_bounded hR (degreeDeviation_bounded U)
  have hD := degreeDeviation_bounded U
  have hσ := signBlockFunction_bounded (S.eigenfunction_measurable 0)
  have hσdiff : BoundedObservable unitMeasure (fun y => ψ y-signBlockFunction ψ y) := by
    convert hψ.add (hσ.const_mul (-1)) using 1
    funext y; ring
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have hM : 1≤M := hblocks.1
  have hMp : 0<M := by linarith
  have hmass : 1/(2*M^2)≤unitMeasure.real P := by
    rcases hP with rfl | rfl
    · exact hblocks.2.1
    · exact hblocks.2.2.2.1
  have hp : 0<unitMeasure.real P := (by positivity : (0:ℝ)<1/(2*M^2)).trans_le hmass
  have hmeas : MeasurableSet P := by
    rcases hP with rfl | rfl
    · exact positiveSignBlock_measurable (S.eigenfunction_measurable 0)
    · exact (positiveSignBlock_measurable (S.eigenfunction_measurable 0)).compl
  have hμ := minimizer_multiplier_pos hr01 hU
  have hrpos := hr.1
  have hm : 0≤m := (Section02.edgeDensity_mem_Icc U).1
  have hη : 0≤η := by dsimp [η]; positivity
  have hV : 0≤V := integral_nonneg fun y => sq_nonneg _
  have hdeg := smallTarget_degree_data external hSampling hr hU
  have hVbound : V≤η*m/2 := hdeg.2.2
  have hDbound := (smallTarget_degree_block_averages external hSampling hr hU S P hP).2
  change setAverage P (fun y => |D y|)≤4*M^2*η at hDbound
  have hψbound : ∀ᵐ y ∂unitMeasure, |ψ y|≤M := minimizer_eigenfunction_bound hSampling hr01 hU S hev
  have hψavg := (signBlock_average_estimates hMp (S.eigenfunction_measurable 0) hψbound
    (centeredEigenfunction_mean_zero U S hev)
    (show (∫ y, ψ y^2 ∂unitMeasure)=1 from by
      simpa only [pow_two,if_pos rfl] using S.orthonormal_integral 0 0) hP).2
  have hβ : |β|≤M*η := minimizer_degreeEigenfunctionPair_bound hSampling hr01 hU S hev
  have hres := smallTarget_residual_degree_errors external hSampling hr hU S hP
  have hRDavg : setAverage P (fun y => |RD y|)≤2*M^2*s*Real.sqrt (η*m/2) := hres.2.1
  filter_upwards [Measure.ae_ae_of_ae_prod (codegree_spectral_error_identity U S hψ),
    hψbound,hdeg.1,hres.1,hres.2.2,boundedObservable_sections hR] with x hx hψx hdx hRDx hR2x hRx
  have hdnonneg : 0≤rowDegree U x := by linarith [hdx.1]
  have hdup : rowDegree U x≤m+η := hdx.2
  change |RD x|≤Real.sqrt (A*s*η*m/2) at hRDx
  change setAverage P (fun y => |residualSquare U S x y|)≤2*M^2*s*Real.sqrt (s*A) at hR2x
  have hR2 : BoundedObservable unitMeasure (fun y => residualSquare U S x y) := by
    simpa only [residualSquare_eq_action] using kernelAction_bounded hR hRx
  let F : Fin 7 → ℝ → ℝ := ![
    (fun _ => V),
    (fun y => -(ev*β*(ψ x+ψ y))),
    (fun _ => -RD x),
    (fun y => rowDegree U x*D y),
    (fun y => -RD y),
    (fun y => ev^2*ψ x*(ψ y-signBlockFunction ψ y)),
    (fun y => residualSquare U S x y)]
  have hFi (i : Fin 7) : Integrable (F i) unitMeasure := by
    fin_cases i
    · exact integrable_const _
    · exact (((integrable_const (ψ x)).add hψ.integrable).const_mul (ev*β)).neg
    · exact integrable_const _
    · exact hD.integrable.const_mul _
    · exact hRD.integrable.neg
    · exact hσdiff.integrable.const_mul _
    · exact hR2.integrable
  have he : setAverage P (fun y => |codegree U x y-(m*rowDegree U x+ev^2*ψ x*signBlockFunction ψ y)|)=
      setAverage P (fun y => |∑ i : Fin 7, F i y|) := by
    apply congrArg (fun v : ℝ => v/unitMeasure.real P)
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hx] with y hy
    rw [hy]
    simp only [Fin.sum_univ_succ,F,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
    congr 1
    dsimp [V,D,RD,R,β,ev,ψ]
    ring
  have hsum := setAverage_abs_sum Finset.univ P F (fun i _ => hFi i)
  have h₀ : setAverage P (fun y => |F 0 y|)≤η*m/2 := by
    change setAverage P (fun _ => |V|)≤_
    rw [setAverage_const P hp,abs_of_nonneg hV]
    exact hVbound
  have h₁ : setAverage P (fun y => |F 1 y|)≤2*ev*M^2*η := by
    apply setAverage_le_const hp (hFi 1).norm
    filter_upwards [ae_restrict_of_ae hψbound] with y hψy
    change |-(ev*β*(ψ x+ψ y))|≤_
    rw [abs_neg,abs_mul,abs_mul,abs_of_nonneg hev.le]
    have hsumψ : |ψ x+ψ y|≤2*M := by
      have hh := abs_add_le (ψ x) (ψ y)
      linarith
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hβ hev.le) hsumψ
      (abs_nonneg _) (mul_nonneg hev.le (mul_nonneg hMp.le hη))
    nlinarith
  have h₂ : setAverage P (fun y => |F 2 y|)≤Real.sqrt (A*s*η*m/2) := by
    change setAverage P (fun _ => |-RD x|)≤_
    rw [setAverage_const P hp,abs_neg]
    exact hRDx
  have h₃ : setAverage P (fun y => |F 3 y|)≤4*M^2*(m+η)*η := by
    change setAverage P (fun y => |rowDegree U x*D y|)≤_
    rw [setAverage_abs_const_mul,abs_of_nonneg hdnonneg]
    have hh := mul_le_mul_of_nonneg_left hDbound hdnonneg
    have hh' := mul_le_mul_of_nonneg_right hdup (show 0≤4*M^2*η by positivity)
    nlinarith
  have h₄ : setAverage P (fun y => |F 4 y|)≤2*M^2*s*Real.sqrt (η*m/2) := by
    change setAverage P (fun y => |-RD y|)≤_
    rw [setAverage_abs_neg]
    exact hRDavg
  have h₅ : setAverage P (fun y => |F 5 y|)≤5*ev^2*M*(M-1) := by
    change setAverage P (fun y => |ev^2*ψ x*(ψ y-signBlockFunction ψ y)|)≤_
    rw [setAverage_abs_const_mul,abs_mul,abs_of_nonneg (sq_nonneg ev)]
    have hfac := mul_le_mul_of_nonneg_left hψx (sq_nonneg ev)
    have hh := mul_le_mul hfac hψavg
      (div_nonneg (integral_nonneg fun y => abs_nonneg _) measureReal_nonneg)
      (mul_nonneg (sq_nonneg ev) hMp.le)
    nlinarith
  have h₆ : setAverage P (fun y => |F 6 y|)≤2*M^2*s*Real.sqrt (s*A) := hR2x
  change _≤rowCodegreeError η m ev M s A
  rw [he]
  apply hsum.trans
  norm_num [Fin.sum_univ_succ]
  change setAverage P (fun y => |F 0 y|)+(setAverage P (fun y => |F 1 y|)+
    (setAverage P (fun y => |F 2 y|)+(setAverage P (fun y => |F 3 y|)+
    (setAverage P (fun y => |F 4 y|)+(setAverage P (fun y => |F 5 y|)+
    setAverage P (fun y => |F 6 y|))))))≤_
  dsimp only [rowCodegreeError]
  linarith only [h₀,h₁,h₂,h₃,h₄,h₅,h₆]

end SparseLowerTail.Section07

import SparseLowerTail.Section07.CodegreeBlockEquations

/-! The approximate two-variable Euler system `eq:s7approxeuler`, for the
actual block averages of almost every minimizing graphon row. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- The scalar base-error estimate E₀, used with ψ and −ψ. -/
theorem rowBase_error_bound {m η ev M d ψ : ℝ} (hev : 0≤ev) (hd : 0≤d)
    (hdup : d≤m+η) (hψ : |ψ|≤M) :
    |m*d+ev^2*ψ-(d+ev*ψ)/2|≤rowBaseError m η ev M := by
  have he : m*d+ev^2*ψ-(d+ev*ψ)/2=(m-1/2)*d+ev*(ev-1/2)*ψ := by ring
  rw [he]
  have hh := abs_add_le ((m-1/2)*d) (ev*(ev-1/2)*ψ)
  rw [abs_mul,abs_of_nonneg hd,abs_mul,abs_mul,abs_of_nonneg hev] at hh
  have h₁ := mul_le_mul_of_nonneg_left hdup (abs_nonneg (m-1/2))
  have h₂ := mul_le_mul_of_nonneg_left hψ (mul_nonneg hev (abs_nonneg (ev-1/2)))
  dsimp only [rowBaseError]
  linarith

/-- Elementary transfer from a surrogate codegree to half the opposite row mean. -/
theorem exponential_surrogate_transfer {μ u v c w EC E0 Em : ℝ}
    (hμ : 0≤μ) (hc : 0≤c) (hv : 0≤v)
    (hu : |u-Real.exp (-μ*c)|≤μ*EC)
    (hbase : |c-w/2|≤E0) (hmean : |v-w|≤Em) :
    |u-Real.exp (-μ*v/2)|≤μ*(EC+E0+Em/2) := by
  have hhalf : |w/2-v/2|≤Em/2 := by
    rw [← sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_sub_comm]
    exact div_le_div_of_nonneg_right hmean (by norm_num)
  have hdist : |c-v/2|≤E0+Em/2 := by
    exact (abs_sub_le c (w/2) (v/2)).trans (add_le_add hbase hhalf)
  have hexp := (abs_exp_neg_mul_sub_le hμ hc (div_nonneg hv (by norm_num))).trans
    (mul_le_mul_of_nonneg_left hdist hμ)
  have hh := abs_sub_le u (Real.exp (-μ*c)) (Real.exp (-μ*(v/2)))
  have he : -μ*(v/2)=-μ*v/2 := by ring
  rw [he] at hexp hh
  linarith

/-- The two actual averaged Euler equations, with the paper's explicit ε. -/
theorem smallTarget_approximateEuler (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let μ := graphonMultiplier U r
    let m := edgeDensity U
    let η := μ*r^3/2
    let A := m+μ*r^3
    let ev := S.eigenvalue 0
    let M := Real.sqrt (A/ev)
    let ε := rowEulerError μ η m ev M (m-ev) A
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ x ∂unitMeasure,
      |setAverage P (fun y => U (x,y))-Real.exp (-μ*setAverage Pᶜ (fun y => U (x,y))/2)|≤ε ∧
      |setAverage Pᶜ (fun y => U (x,y))-Real.exp (-μ*setAverage P (fun y => U (x,y))/2)|≤ε := by
  dsimp only
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hμ := minimizer_multiplier_pos hr01 hU
  have hev := smallTarget_centeredEigenvalue_pos external hr hU S
  filter_upwards [smallTarget_surrogate_exponential_errors external hSampling hr hU S,
    smallTarget_rowMeans external hSampling hr hU S,
    minimizer_eigenfunction_bound hSampling hr01 hU S hev,
    minimizer_degree_upper hSampling hr01 hU,centered_surrogate_codegrees_nonneg U S,
    rowDegree_mem_Icc_ae U,Measure.ae_ae_of_ae_prod U.bounded] with x he hm hψ hd hc hd01 hub
  have hupos : ∀ P : Set ℝ, 0≤setAverage P (fun y => U (x,y)) := by
    intro P
    apply div_nonneg _ measureReal_nonneg
    exact integral_nonneg_of_ae ((ae_restrict_of_ae hub).mono fun y hy => hy.1)
  have hbase := rowBase_error_bound hev.le hd01.1 hd hψ
  have hbase' := rowBase_error_bound hev.le hd01.1 hd
    (show |-(S.eigenfunction 0 x)|≤Real.sqrt ((edgeDensity U+graphonMultiplier U r*r^3)/S.eigenvalue 0) from by
      simpa only [abs_neg] using hψ)
  constructor
  · exact exponential_surrogate_transfer hμ.le hc.1 (hupos _) he.1 hbase hm.2
  · apply exponential_surrogate_transfer hμ.le hc.2 (hupos _) he.2 _ hm.1
    convert hbase' using 1; congr 1; ring

end SparseLowerTail.Section07

import SparseLowerTail.Section07.ApproximateEuler
import SparseLowerTail.Section07.RowVertexBound
import SparseLowerTail.Section07.SmallParameterErrors
import SparseLowerTail.Section07.ScalarExclusion

/-! Structural Steps 1--2: the actual row means separate, and the leading
eigenfunction determines which block has the larger mean. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- The exact decomposition of a row degree into its two block means. -/
theorem degree_block_means {P : Set ℝ} (hP : MeasurableSet P)
    (hp : 0<unitMeasure.real P) (hq : 0<unitMeasure.real Pᶜ)
    {U : Graphon} {x : ℝ} (hi : Integrable (fun y => U (x,y)) unitMeasure) :
    rowDegree U x=unitMeasure.real P*setAverage P (fun y => U (x,y))+
      unitMeasure.real Pᶜ*setAverage Pᶜ (fun y => U (x,y)) := by
  have hh := integral_add_compl hP hi
  dsimp [setAverage,rowDegree]
  rw [mul_div_cancel₀ _ (ne_of_gt hp),mul_div_cancel₀ _ (ne_of_gt hq)]
  exact hh.symm

private theorem scalar_means_separate {u v p q d μ ε : ℝ}
    (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1)
    (hp : (498/1000:ℝ)<p) (hq : (498/1000:ℝ)<q)
    (hd : d=p*u+q*v) (hdmax : d≤5006/10000)
    (hμ : 186/10≤μ) (hε : ε<114/1000)
    (hkuv : (vertexEntropy u+vertexEntropy v)/2<1005/1000)
    (hEu : |u-Real.exp (-μ*v/2)|≤ε) (hEv : |v-Real.exp (-μ*u/2)|≤ε) :
    (u<231/1000 ∧ 775/1000<v) ∨ (775/1000<u ∧ v<231/1000) := by
  have hstep {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
      (hab : a≤b) (hk : (vertexEntropy a+vertexEntropy b)/2<1005/1000)
      (hE : |b-Real.exp (-μ*a/2)|≤ε) : 775/1000<b := by
    apply scalar_exclusion ha.1 hab hb.2 hk.le
    have hexp : Real.exp (-μ*a/2)≤Real.exp (-(93/10)*a) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hμ ha.1])
    have hh := (abs_le.mp hE).2
    linarith
  rcases le_total u v with huv | hvu
  · have hvbig := hstep hu hv huv hkuv hEv
    have hqu := mul_le_mul_of_nonneg_right hp.le hu.1
    have hqv := mul_lt_mul hq hvbig.le (by norm_num : (0:ℝ)<775/1000) (by linarith : 0≤q)
    left
    constructor
    · nlinarith
    · exact hvbig
  · have hubig := hstep hv hu hvu (by simpa only [add_comm] using hkuv) hEu
    have hpv := mul_le_mul_of_nonneg_right hq.le hv.1
    have hpu := mul_lt_mul hp hubig.le (by norm_num : (0:ℝ)<775/1000) (by linarith : 0≤p)
    right
    constructor
    · exact hubig
    · nlinarith

private theorem separated_row_sign {u v d ev ψ E : ℝ} (hev : 0<ev)
    (hE : E<3/1000) (hu : |u-(d-ev*ψ)|≤E) (hv : |v-(d+ev*ψ)|≤E)
    (hsep : (u<231/1000 ∧ 775/1000<v) ∨ (775/1000<u ∧ v<231/1000)) :
    ψ≠0 ∧ (0≤ψ → 775/1000<v) ∧ (ψ<0 → 775/1000<u) := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  rcases hsep with hs | hs
  · have hψ : 0<ψ := by nlinarith
    exact ⟨ne_of_gt hψ,fun _ => hs.2,fun h => False.elim (not_lt_of_ge hψ.le h)⟩
  · have hψ : ψ<0 := by nlinarith
    exact ⟨ne_of_lt hψ,fun h => False.elim (not_lt_of_ge h hψ),fun _ => hs.1⟩

/-- The two actual row block averages lie in opposite separated ranges. -/
theorem smallTarget_row_means_separate (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ x ∂unitMeasure,
      (setAverage P (fun y => U (x,y))<231/1000 ∧ 775/1000<setAverage Pᶜ (fun y => U (x,y))) ∨
      (775/1000<setAverage P (fun y => U (x,y)) ∧ setAverage Pᶜ (fun y => U (x,y))<231/1000) := by
  dsimp only
  let P := positiveSignBlock (S.eigenfunction 0)
  have hP : MeasurableSet P := positiveSignBlock_measurable (S.eigenfunction_measurable 0)
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have herr := smallTarget_error_bounds external hSampling hr hU S
  have hp : (498/1000:ℝ)<unitMeasure.real P := by linarith [hblocks.2.1,herr.2.2.2.1]
  have hq : (498/1000:ℝ)<unitMeasure.real Pᶜ := by linarith [hblocks.2.2.2.1,herr.2.2.2.1]
  have hp0 : 0<unitMeasure.real P := by linarith
  have hq0 : 0<unitMeasure.real Pᶜ := by linarith
  have hμ := (smallTargetErrorData external hr hU S).mu_lower
  filter_upwards [smallTarget_approximateEuler external hSampling hr hU S,
    smallTarget_rowVertex_bound external hSampling hr hU S,herr.2.2.2.2,
    boundedObservable_sections (graphon_boundedObservable U),Measure.ae_ae_of_ae_prod U.bounded] with x hE hk hd hi hb
  have hu := setAverage_mem_unit hi.measurable hb hp0
  have hv := setAverage_mem_unit hi.measurable hb hq0
  apply scalar_means_separate hu hv hp hq (degree_block_means hP hp0 hq0 hi.integrable)
    hd hμ herr.1 _ hE.1 hE.2
  exact hk.trans_lt herr.2.2.1

/-- The sign of ψ determines the large opposite-block mean. -/
theorem smallTarget_oppositeBlock_means (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ x ∂unitMeasure, S.eigenfunction 0 x≠0 ∧
      (x∈P → 775/1000<setAverage Pᶜ (fun y => U (x,y))) ∧
      (x∉P → 775/1000<setAverage P (fun y => U (x,y))) := by
  dsimp only
  have hev := smallTarget_centeredEigenvalue_pos external hr hU S
  have hE := (smallTarget_error_bounds external hSampling hr hU S).2.1
  filter_upwards [smallTarget_row_means_separate external hSampling hr hU S,
    smallTarget_rowMeans external hSampling hr hU S] with x hx hm
  have hh := separated_row_sign hev hE hm.1 hm.2 hx
  exact ⟨hh.1,hh.2.1,fun hy => hh.2.2 (lt_of_not_ge hy)⟩

end SparseLowerTail.Section07

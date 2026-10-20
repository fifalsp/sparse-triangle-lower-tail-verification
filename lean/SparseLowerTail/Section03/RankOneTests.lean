import SparseLowerTail.Section03.CellAverages

/-! The signed-test proof of quantitative cell-projection error for a two-block kernel. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section03
open Section02

def signedRankOneKernel (ℓ μ : ℝ) (g : ℝ → ℝ) (p : ℝ×ℝ) : ℝ := ℓ+μ*g p.1*g p.2

theorem boundedTest_product_integrable {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x|≤1) (hc : ∀ x, |g x|≤1) :
    Integrable (fun x => f x*g x) unitMeasure := by
  apply unitBound_integrable (hf.mul hg)
  intro x
  rw [abs_mul]
  exact (mul_le_mul (hb x) (hc x) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem signedRankOneKernel_integrable (ℓ μ : ℝ) {g : ℝ → ℝ}
    (hg : Measurable g) (hb : ∀ x, |g x|≤1) :
    Integrable (signedRankOneKernel ℓ μ g) squareMeasure := by
  have hi := ((unitBound_integrable hg hb).mul_prod (unitBound_integrable hg hb)).const_mul μ
  have he : signedRankOneKernel ℓ μ g=(fun p : ℝ×ℝ => ℓ+μ*(g p.1*g p.2)) := by funext p; dsimp [signedRankOneKernel]; ring
  rw [he]
  exact (integrable_const ℓ).add hi

/-- Every bounded signed test of the two-block kernel has an exact moment formula. -/
theorem signedRankOneKernel_test (ℓ μ : ℝ) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hb : ∀ x, |f x|≤1) (hc : ∀ x, |g x|≤1) :
    (∫ p, f p.1*f p.2*signedRankOneKernel ℓ μ g p ∂squareMeasure)=
      ℓ*(∫ x, f x ∂unitMeasure)^2+μ*(∫ x, f x*g x ∂unitMeasure)^2 := by
  have hi := ((unitBound_integrable hf hb).mul_prod (unitBound_integrable hf hb)).const_mul ℓ
  have hj := ((boundedTest_product_integrable hf hg hb hc).mul_prod
    (boundedTest_product_integrable hf hg hb hc)).const_mul μ
  have he : (fun p : ℝ×ℝ => f p.1*f p.2*signedRankOneKernel ℓ μ g p)=
      (fun p => ℓ*(f p.1*f p.2)+μ*((f p.1*g p.1)*(f p.2*g p.2))) := by
    funext p; dsimp [signedRankOneKernel]; ring
  rw [he,integral_add hi hj,integral_const_mul,integral_const_mul]
  change ℓ*(∫ p, f p.1*f p.2 ∂unitMeasure.prod unitMeasure)+
    μ*(∫ p, (f p.1*g p.1)*(f p.2*g p.2) ∂unitMeasure.prod unitMeasure)=_
  rw [integral_prod_mul f f,integral_prod_mul (fun x => f x*g x) (fun x => f x*g x)]
  ring

/-- The squared norm of a bounded cell average lies in [0,1]. -/
theorem projectedVertexTest_square_bounds {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    {g : ℝ → ℝ} (hg : Measurable g) (hb : ∀ x, |g x|≤1) :
    (∫ x, (projectedVertexTest P g x)^2 ∂unitMeasure)∈Icc (0:ℝ) 1 := by
  have hp := projectedVertexTest_measurable P g
  have hpb := projectedVertexTest_abs_le hn P hmass hg hb
  have hi := boundedTest_product_integrable hp hp hpb hpb
  have hisq : Integrable (fun x => (projectedVertexTest P g x)^2) unitMeasure := by simpa only [pow_two] using hi
  refine ⟨integral_nonneg (fun x => sq_nonneg _),?_⟩
  have he := integral_mono_ae hisq (integrable_const (1:ℝ))
    (Eventually.of_forall fun x => (sq_le_one_iff_abs_le_one _).mpr (hpb x))
  simpa using he

/-- The manuscript's projection deficit follows directly from two signed tests.
This proves the needed estimate without assuming cut-norm contraction of cell averaging. -/
theorem signed_projection_defect {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    (M : Fin n → Fin n → ℝ) {g : ℝ → ℝ} (hg : Measurable g) (hb : ∀ x, |g x|≤1)
    (hmean : (∫ x, g x ∂unitMeasure)=0) (hsquare : (∫ x, g x*g x ∂unitMeasure)=1)
    (ℓ μ δ : ℝ) (hnear : cutNorm (fun p => matrixStepKernel P M p-signedRankOneKernel ℓ μ g p)≤δ) :
    |μ| * (1-∫ x, (projectedVertexTest P g x)^2 ∂unitMeasure)≤8*δ := by
  change cutNorm (matrixStepKernel P M-signedRankOneKernel ℓ μ g)≤δ at hnear
  let c := projectedVertexTest P g
  let q := ∫ x, (c x)^2 ∂unitMeasure
  have hcm := projectedVertexTest_measurable P g
  have hcb := projectedVertexTest_abs_le hn P hmass hg hb
  have hcmean : (∫ x, c x ∂unitMeasure)=0 := (projectedVertexTest_integral hn P hmass (unitBound_integrable hg hb)).trans hmean
  have hcorr : (∫ x, c x*g x ∂unitMeasure)=q := by
    simpa only [mul_comm] using projectedVertexTest_correlation hn P hmass (unitBound_integrable hg hb)
  have hq := projectedVertexTest_square_bounds hn P hmass hg hb
  change q∈Icc (0:ℝ) 1 at hq
  have hM := matrixStepKernel_integrable P M
  have hB := signedRankOneKernel_integrable ℓ μ hg hb
  have hgtest := abs_signed_integral_le_four_cutNorm (hM.sub hB) hg hg hb hb
  have hctest := abs_signed_integral_le_four_cutNorm (hM.sub hB) hcm hcm hcb hcb
  have split (f : ℝ → ℝ) (hf : Measurable f) (hfb : ∀ x, |f x|≤1) :
      (∫ p, f p.1*f p.2*(matrixStepKernel P M p-signedRankOneKernel ℓ μ g p) ∂squareMeasure)=
      (∫ p, f p.1*f p.2*matrixStepKernel P M p ∂squareMeasure)-
      (∫ p, f p.1*f p.2*signedRankOneKernel ℓ μ g p ∂squareMeasure) := by
    simpa only [mul_sub] using integral_sub (weightedKernel_integrable hM hf hf hfb hfb)
      (weightedKernel_integrable hB hf hf hfb hfb)
  simp only [Pi.sub_apply] at hgtest hctest
  rw [split g hg hb,signedRankOneKernel_test ℓ μ hg hg hb hb,hmean,hsquare] at hgtest
  rw [split c hcm hcb,signedRankOneKernel_test ℓ μ hcm hg hcb hb,hcmean,hcorr] at hctest
  have hcancel := matrixStepKernel_projected_test hn P hmass M hg hb
  change (∫ p, g p.1*g p.2*matrixStepKernel P M p ∂squareMeasure)=
    ∫ p, c p.1*c p.2*matrixStepKernel P M p ∂squareMeasure at hcancel
  rw [hcancel] at hgtest
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),one_pow,mul_zero,mul_one,zero_add] at hgtest hctest
  have hbound : |μ * (1-q^2)|≤8*δ := by
    have he : ((∫ p, c p.1*c p.2*matrixStepKernel P M p ∂squareMeasure)-μ*q^2)-
      ((∫ p, c p.1*c p.2*matrixStepKernel P M p ∂squareMeasure)-μ)=μ*(1-q^2) := by ring
    have hab := abs_sub ((∫ p, c p.1*c p.2*matrixStepKernel P M p ∂squareMeasure)-μ*q^2)
      ((∫ p, c p.1*c p.2*matrixStepKernel P M p ∂squareMeasure)-μ)
    rw [he] at hab
    exact hab.trans (by linarith [mul_le_mul_of_nonneg_left hnear (by norm_num : (0:ℝ)≤4)])
  have hq2 : q^2≤q := by nlinarith [hq.1,hq.2]
  have hnonneg : 0≤1-q^2 := by nlinarith [hq.2,hq2]
  rw [abs_mul,abs_of_nonneg hnonneg] at hbound
  exact (mul_le_mul_of_nonneg_left (by linarith : 1-q≤1-q^2) (abs_nonneg μ)).trans hbound

end SparseLowerTail.Section03

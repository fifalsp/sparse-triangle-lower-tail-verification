import SparseLowerTail.Section02.WeightedCut

/-! Signed tests for the actual measurable rectangle cut norm. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section03
open Section02

/-- Multiplication by two bounded measurable tests preserves integrability. -/
theorem weightedKernel_integrable {K : ℝ×ℝ → ℝ} (hK : Integrable K squareMeasure)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x|≤1) (hgb : ∀ x, |g x|≤1) :
    Integrable (fun p => f p.1*g p.2*K p) squareMeasure := by
  have hi := hK.bdd_mul' ((hf.comp measurable_fst).aestronglyMeasurable)
    (Eventually.of_forall fun p => (show ‖f p.1‖≤1 by simpa only [Real.norm_eq_abs] using hfb p.1))
  have hj := hi.bdd_mul' ((hg.comp measurable_snd).aestronglyMeasurable)
    (Eventually.of_forall fun p => (show ‖g p.2‖≤1 by simpa only [Real.norm_eq_abs] using hgb p.2))
  convert hj using 1
  funext p; simp only [Function.comp_apply]; ring

/-- The factor four for arbitrary signed tests in [-1,1]. -/
theorem abs_signed_integral_le_four_cutNorm {K : ℝ×ℝ → ℝ} (hK : Integrable K squareMeasure)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x|≤1) (hgb : ∀ x, |g x|≤1) :
    |∫ p, f p.1*g p.2*K p ∂squareMeasure|≤4*cutNorm K := by
  let fp := fun x => (1+f x)/2
  let fm := fun x => (1-f x)/2
  let gp := fun x => (1+g x)/2
  let gm := fun x => (1-g x)/2
  have hfp : Measurable fp := (measurable_const.add hf).div_const 2
  have hfm : Measurable fm := (measurable_const.sub hf).div_const 2
  have hgp : Measurable gp := (measurable_const.add hg).div_const 2
  have hgm : Measurable gm := (measurable_const.sub hg).div_const 2
  have bp : ∀ x, fp x∈Icc (0:ℝ) 1 := fun x => by dsimp only [fp]; have h:=abs_le.mp (hfb x); constructor <;> linarith
  have bm : ∀ x, fm x∈Icc (0:ℝ) 1 := fun x => by dsimp only [fm]; have h:=abs_le.mp (hfb x); constructor <;> linarith
  have cp : ∀ x, gp x∈Icc (0:ℝ) 1 := fun x => by dsimp only [gp]; have h:=abs_le.mp (hgb x); constructor <;> linarith
  have cm : ∀ x, gm x∈Icc (0:ℝ) 1 := fun x => by dsimp only [gm]; have h:=abs_le.mp (hgb x); constructor <;> linarith
  have bpa : ∀ x, |fp x|≤1 := fun x => (abs_of_nonneg (bp x).1).trans_le (bp x).2
  have bma : ∀ x, |fm x|≤1 := fun x => (abs_of_nonneg (bm x).1).trans_le (bm x).2
  have cpa : ∀ x, |gp x|≤1 := fun x => (abs_of_nonneg (cp x).1).trans_le (cp x).2
  have cma : ∀ x, |gm x|≤1 := fun x => (abs_of_nonneg (cm x).1).trans_le (cm x).2
  have ipp := weightedKernel_integrable hK hfp hgp bpa cpa
  have ipm := weightedKernel_integrable hK hfp hgm bpa cma
  have imp := weightedKernel_integrable hK hfm hgp bma cpa
  have imm := weightedKernel_integrable hK hfm hgm bma cma
  have hpp := abs_weighted_integral_le_cutNorm hK hfp.aemeasurable hgp.aemeasurable
    (Eventually.of_forall bp) (Eventually.of_forall cp)
  have hpm := abs_weighted_integral_le_cutNorm hK hfp.aemeasurable hgm.aemeasurable
    (Eventually.of_forall bp) (Eventually.of_forall cm)
  have hmp := abs_weighted_integral_le_cutNorm hK hfm.aemeasurable hgp.aemeasurable
    (Eventually.of_forall bm) (Eventually.of_forall cp)
  have hmm := abs_weighted_integral_le_cutNorm hK hfm.aemeasurable hgm.aemeasurable
    (Eventually.of_forall bm) (Eventually.of_forall cm)
  have he : (fun p : ℝ×ℝ => f p.1*g p.2*K p)=
      (fun p => (fp p.1*gp p.2*K p-fp p.1*gm p.2*K p)-
        (fm p.1*gp p.2*K p-fm p.1*gm p.2*K p)) := by
    funext p; dsimp only [fp,fm,gp,gm]; ring
  have houter := integral_sub (ipp.sub ipm) (imp.sub imm)
  simp only [Pi.sub_apply] at houter
  rw [he,houter,integral_sub ipp ipm,integral_sub imp imm]
  exact (abs_sub _ _).trans ((add_le_add (abs_sub _ _) (abs_sub _ _)).trans (by linarith))

end SparseLowerTail.Section03

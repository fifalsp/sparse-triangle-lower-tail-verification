import SparseLowerTail.Section02.CutDistanceIdentities

/-! Weighted tests for the actual rectangle cut norm. A linear test with values
in [0,1] can be replaced by the indicator of the positive part of its integrand.
Applying this twice proves the sharp constant without a layer-cake expansion. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section02

private theorem integrable_mul_unit {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f h : α → ℝ} (hh : Integrable h μ)
    (hf : AEMeasurable f μ) (hb : ∀ᵐ x ∂μ, f x∈Icc (0:ℝ) 1) :
    Integrable (fun x => f x*h x) μ := by
  apply hh.bdd_mul' hf.aestronglyMeasurable
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2

/-- A unit-valued linear test is bounded by an actual measurable indicator test. -/
theorem exists_indicator_integral_ge {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f h : α → ℝ} (hh : Integrable h μ)
    (hf : AEMeasurable f μ) (hb : ∀ᵐ x ∂μ, f x∈Icc (0:ℝ) 1) :
    ∃ S : Set α, MeasurableSet S ∧
      (∫ x, f x*h x ∂μ)≤∫ x, S.indicator h x ∂μ := by
  let S := {x | 0≤hh.aemeasurable.mk h x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hh.aemeasurable.measurable_mk
  refine ⟨S,hS,integral_mono_ae (integrable_mul_unit hh hf hb) (hh.indicator hS) ?_⟩
  filter_upwards [hb,hh.aemeasurable.ae_eq_mk] with x hx hrep
  by_cases hs : x∈S
  · rw [indicator_of_mem hs]
    have hp : 0≤h x := by simpa only [S,mem_setOf_eq,← hrep] using hs
    exact mul_le_of_le_one_left hp hx.2
  · rw [indicator_of_notMem hs]
    have hn : h x≤0 := by
      have : ¬0≤h x := by simpa only [S,mem_setOf_eq,← hrep] using hs
      exact (lt_of_not_ge this).le
    exact mul_nonpos_of_nonneg_of_nonpos hx.1 hn

private theorem weighted_integral_le {K : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) {f g : ℝ → ℝ}
    (hf : AEMeasurable f unitMeasure) (hg : AEMeasurable g unitMeasure)
    (hfb : ∀ᵐ x ∂unitMeasure, f x∈Icc (0:ℝ) 1)
    (hgb : ∀ᵐ y ∂unitMeasure, g y∈Icc (0:ℝ) 1) :
    (∫ p, f p.1*g p.2*K p ∂squareMeasure)≤cutNorm K := by
  have hgm : AEMeasurable (fun p : ℝ × ℝ => g p.2) squareMeasure := hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hfm : AEMeasurable (fun p : ℝ × ℝ => f p.1) squareMeasure := hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hgB : ∀ᵐ p : ℝ × ℝ ∂squareMeasure, g p.2∈Icc (0:ℝ) 1 := Measure.quasiMeasurePreserving_snd.ae hgb
  have hfB : ∀ᵐ p : ℝ × ℝ ∂squareMeasure, f p.1∈Icc (0:ℝ) 1 := Measure.quasiMeasurePreserving_fst.ae hfb
  have hKg := integrable_mul_unit hK hgm hgB
  have hfg := integrable_mul_unit hKg hfm hfB
  obtain ⟨S,hS,hfirst⟩ := exists_indicator_integral_ge hKg.integral_prod_left hf hfb
  let L : ℝ × ℝ → ℝ := fun p => S.indicator (fun x => K (x,p.2)) p.1
  have hL : Integrable L squareMeasure := by
    have he : L=(S ×ˢ univ).indicator K := by ext p; by_cases h:p.1∈S <;> simp [L,h]
    rw [he]
    exact hK.indicator (hS.prod MeasurableSet.univ)
  obtain ⟨T,hT,hsecond⟩ := exists_indicator_integral_ge hL.integral_prod_right hg hgb
  have hleft : (∫ p, f p.1*g p.2*K p ∂squareMeasure)=
      ∫ x, f x*(∫ y,g y*K (x,y) ∂unitMeasure) ∂unitMeasure := by
    have he : (fun p : ℝ × ℝ => f p.1*g p.2*K p)=
        (fun p => f p.1*(g p.2*K p)) := by ext p;ring
    rw [he,integral_prod _ hfg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => integral_const_mul (μ:=unitMeasure) (f x) (fun y => g y*K (x,y))
  have hmid : (∫ x,S.indicator (fun x => ∫ y,g y*K (x,y) ∂unitMeasure) x ∂unitMeasure)=
      ∫ y,g y*(∫ x,L (x,y) ∂unitMeasure) ∂unitMeasure := by
    have hLg := integrable_mul_unit hL hgm hgB
    calc
      _ = ∫ p,g p.2*L p ∂squareMeasure := by
        rw [integral_prod _ hLg]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          by_cases hx:x∈S <;> simp [L,hx]
      _ = _ := by
        rw [integral_prod_symm _ hLg]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => integral_const_mul (μ:=unitMeasure) (g y) (fun x => L (x,y))
  have hright : (∫ y,T.indicator (fun y => ∫ x,L (x,y) ∂unitMeasure) y ∂unitMeasure)=
      rectangleIntegral K S T := by
    have he : (S ×ˢ T).indicator K=(fun p : ℝ × ℝ => T.indicator (fun y => L (p.1,y)) p.2) := by
      ext p; by_cases hx:p.1∈S <;> by_cases hy:p.2∈T <;> simp [L,hx,hy]
    rw [rectangleIntegral,← integral_indicator (hS.prod hT),he,
      integral_prod_symm _ ((hK.indicator (hS.prod hT)).congr (Eventually.of_forall fun p => congrFun he p))]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by by_cases hy:y∈T <;> simp [hy]
  rw [← hleft,hmid] at hfirst
  rw [hright] at hsecond
  exact (hfirst.trans hsecond).trans ((le_abs_self _).trans (abs_rectangleIntegral_le_cutNorm hK hS hT))

/-- `lem:cut(a)`, with the stronger assumption that the kernel need only be integrable. -/
theorem abs_weighted_integral_le_cutNorm {K : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) {f g : ℝ → ℝ}
    (hf : AEMeasurable f unitMeasure) (hg : AEMeasurable g unitMeasure)
    (hfb : ∀ᵐ x ∂unitMeasure, f x∈Icc (0:ℝ) 1)
    (hgb : ∀ᵐ y ∂unitMeasure, g y∈Icc (0:ℝ) 1) :
    |∫ p, f p.1*g p.2*K p ∂squareMeasure|≤cutNorm K := by
  apply abs_le.mpr
  refine ⟨?_,weighted_integral_le hK hf hg hfb hgb⟩
  have h := weighted_integral_le hK.neg hf hg hfb hgb
  change (∫ p, f p.1*g p.2*(-K p) ∂squareMeasure)≤cutNorm (fun p => -K p) at h
  simp only [mul_neg,integral_neg,cutNorm_neg] at h
  linarith

end SparseLowerTail.Section02

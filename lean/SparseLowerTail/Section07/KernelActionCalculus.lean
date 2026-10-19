import SparseLowerTail.Section07.SpectralRemainder
import Mathlib.Algebra.QuadraticDiscriminant

/-! Elementary L² action bounds for positive bounded symmetric kernels.
This module derives the norm estimate from quadratic-form bounds; no operator
norm statement is included in the external spectral input. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

def kernelPair (K : ℝ × ℝ → ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ p, K p*(f p.1*g p.2) ∂squareMeasure

def kernelAction (K : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, K (x,y)*f y ∂unitMeasure

theorem kernelPair_integrable {K : ℝ × ℝ → ℝ} {f g : ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hf : BoundedObservable unitMeasure f)
    (hg : BoundedObservable unitMeasure g) :
    Integrable (fun p => K p*(f p.1*g p.2)) squareMeasure :=
  (hK.mul ((hf.comp Measure.quasiMeasurePreserving_fst).mul
    (hg.comp Measure.quasiMeasurePreserving_snd))).integrable

theorem kernelAction_bounded {K : ℝ × ℝ → ℝ} {f : ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hf : BoundedObservable unitMeasure f) :
    BoundedObservable unitMeasure (kernelAction K f) :=
  (hK.mul (hf.comp Measure.quasiMeasurePreserving_snd)).integral_left

theorem kernelPair_symmetric {K : ℝ × ℝ → ℝ} (hS : ∀ᵐ p ∂squareMeasure, K p.swap=K p)
    (f g : ℝ → ℝ) : kernelPair K f g=kernelPair K g f := by
  unfold kernelPair
  calc
    _ = ∫ p, K p.swap*(g p.swap.1*f p.swap.2) ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [hS] with p hp
      dsimp only [Prod.fst_swap,Prod.snd_swap]
      rw [hp,mul_comm (g p.2)]
    _ = _ := Measure.measurePreserving_swap.integral_comp
      MeasurableEquiv.prodComm.measurableEmbedding (fun p => K p*(g p.1*f p.2))

theorem kernelPair_add_left {K : ℝ × ℝ → ℝ} {f g h : ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hf : BoundedObservable unitMeasure f)
    (hg : BoundedObservable unitMeasure g) (hh : BoundedObservable unitMeasure h) :
    kernelPair K (fun x => f x+g x) h=kernelPair K f h+kernelPair K g h := by
  unfold kernelPair
  rw [← integral_add (kernelPair_integrable hK hf hh) (kernelPair_integrable hK hg hh)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by dsimp; ring

theorem kernelPair_const_mul_left (K : ℝ × ℝ → ℝ) (f g : ℝ → ℝ) (c : ℝ) :
    kernelPair K (fun x => c*f x) g=c*kernelPair K f g := by
  unfold kernelPair
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by dsimp; ring

theorem kernelPair_add_right {K : ℝ × ℝ → ℝ} {f g h : ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hf : BoundedObservable unitMeasure f)
    (hg : BoundedObservable unitMeasure g) (hh : BoundedObservable unitMeasure h) :
    kernelPair K f (fun x => g x+h x)=kernelPair K f g+kernelPair K f h := by
  unfold kernelPair
  rw [← integral_add (kernelPair_integrable hK hf hg) (kernelPair_integrable hK hf hh)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by dsimp; ring

theorem kernelPair_const_mul_right (K : ℝ × ℝ → ℝ) (f g : ℝ → ℝ) (c : ℝ) :
    kernelPair K f (fun x => c*g x)=c*kernelPair K f g := by
  unfold kernelPair
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by dsimp; ring

/-- Cauchy--Schwarz for the positive quadratic form of an actual kernel. -/
theorem kernelPair_sq_le {K : ℝ × ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K)
    (hS : ∀ᵐ p ∂squareMeasure, K p.swap=K p)
    (hpos : ∀ f, BoundedObservable unitMeasure f → 0≤kernelPair K f f)
    {f g : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) (hg : BoundedObservable unitMeasure g) :
    kernelPair K f g^2≤kernelPair K f f*kernelPair K g g := by
  have hpoly (c : ℝ) : 0≤kernelPair K g g*(c*c)+(2*kernelPair K f g)*c+kernelPair K f f := by
    have h := hpos (fun x => f x+c*g x) (hf.add (hg.const_mul c))
    rw [kernelPair_add_left hK hf (hg.const_mul c) (hf.add (hg.const_mul c)),
      kernelPair_add_right hK hf hf (hg.const_mul c),
      kernelPair_add_right hK (hg.const_mul c) hf (hg.const_mul c),
      kernelPair_const_mul_left,kernelPair_const_mul_left,
      kernelPair_const_mul_right,kernelPair_const_mul_right,kernelPair_symmetric hS g f] at h
    nlinarith [h]
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  nlinarith

/-- Fubini identifies the bilinear form with the actual integral-kernel action. -/
theorem kernelPair_action {K : ℝ × ℝ → ℝ} {f g : ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hf : BoundedObservable unitMeasure f)
    (hg : BoundedObservable unitMeasure g) :
    kernelPair K f g=∫ x, f x*kernelAction K g x ∂unitMeasure := by
  unfold kernelPair
  rw [integral_prod _ (kernelPair_integrable hK hf hg)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp [kernelAction]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by dsimp; ring

/-- A positive bounded symmetric kernel with quadratic form at most sI has
actual L² action norm at most s, proved without an operator API. -/
theorem kernelAction_sq_le {K : ℝ × ℝ → ℝ} {s : ℝ}
    (hK : BoundedObservable squareMeasure K)
    (hS : ∀ᵐ p ∂squareMeasure, K p.swap=K p) (hs : 0≤s)
    (hpos : ∀ f, BoundedObservable unitMeasure f → 0≤kernelPair K f f)
    (hupper : ∀ f, BoundedObservable unitMeasure f →
      kernelPair K f f≤s*(∫ x, f x^2 ∂unitMeasure))
    {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    (∫ x, kernelAction K f x^2 ∂unitMeasure)≤s^2*(∫ x, f x^2 ∂unitMeasure) := by
  have hg := kernelAction_bounded hK hf
  have hc := kernelPair_sq_le hK hS hpos hg hf
  rw [kernelPair_action hK hg hf] at hc
  have he : (∫ x, kernelAction K f x*kernelAction K f x ∂unitMeasure)=
      ∫ x, kernelAction K f x^2 ∂unitMeasure := by simp only [pow_two]
  rw [he] at hc
  have hu := mul_le_mul (hupper (kernelAction K f) hg) (hupper f hf)
    (hpos f hf) (mul_nonneg hs (integral_nonneg fun x => sq_nonneg _))
  have hnonneg : 0≤∫ x, kernelAction K f x^2 ∂unitMeasure := integral_nonneg fun x => sq_nonneg _
  rcases eq_or_lt_of_le hnonneg with hz | hp
  · rw [← hz]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  · apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [hc.trans hu]

end SparseLowerTail.Section07

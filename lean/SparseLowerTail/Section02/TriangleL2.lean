import SparseLowerTail.Section02.MeanGap
import SparseLowerTail.Section08.GraphonIntegration
import Mathlib.Algebra.QuadraticDiscriminant

/-! Actual integral Cauchy--Schwarz and signed triangle estimates for Section 2. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace SparseLowerTail.Section02
open TriangleIntegration

/-- Integral Cauchy--Schwarz, squared, for bounded real observables. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : BoundedObservable μ f) (hg : BoundedObservable μ g) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have hff : Integrable (fun x => (f x)^2) μ := by simpa only [pow_two] using (hf.mul hf).integrable
  have hgg : Integrable (fun x => (g x)^2) μ := by simpa only [pow_two] using (hg.mul hg).integrable
  have hfg := (hf.mul hg).integrable
  have hpoly : ∀ t : ℝ, 0 ≤ (∫ x, (g x)^2 ∂μ)*(t*t) +
      (-2*(∫ x, f x*g x ∂μ))*t + (∫ x, (f x)^2 ∂μ) := by
    intro t
    have hn : 0 ≤ ∫ x, (g x)^2*(t*t)+(-2*(f x*g x))*t+(f x)^2 ∂μ := by
      apply integral_nonneg
      intro x
      change 0 ≤ (g x)^2*(t*t)+(-2*(f x*g x))*t+(f x)^2
      nlinarith [sq_nonneg (f x-t*g x)]
    rw [integral_add (f := fun x => (g x)^2*(t*t)+(-2*(f x*g x))*t) (g := fun x => (f x)^2)
      ((hgg.mul_const _).add ((hfg.const_mul _).mul_const _)) hff,
      integral_add (f := fun x => (g x)^2*(t*t)) (g := fun x => (-2*(f x*g x))*t)
      (hgg.mul_const _) ((hfg.const_mul _).mul_const _),
      integral_mul_const, integral_mul_const, integral_const_mul] at hn
    exact hn
  have hd := discrim_le_zero hpoly
  simp only [discrim] at hd
  nlinarith

/-- Row square integral of a signed kernel. -/
def rowSquare (K : ℝ × ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, (K (x,y))^2 ∂unitMeasure
/-- Codegree of a signed kernel. -/
def signedCodegree (K : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ z, K (p.1,z)*K (p.2,z) ∂unitMeasure
/-- Triangle integral of a signed kernel. -/
def signedTriangle (K : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : (ℝ × ℝ) × ℝ, K p.1*K (p.1.2,p.2)*K (p.1.1,p.2) ∂tripleMeasure

theorem boundedObservable_slices {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    ∀ᵐ x ∂unitMeasure, BoundedObservable unitMeasure (fun y => K (x,y)) := by
  obtain ⟨B, hB, hb⟩ := hK.bound
  filter_upwards [hK.integrable.prod_right_ae, Measure.ae_ae_of_ae_prod hb] with x hm hx
  exact ⟨hm.aemeasurable, B, hB, hx⟩

theorem rowSquare_bounded {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    BoundedObservable unitMeasure (rowSquare K) := by
  change BoundedObservable unitMeasure (fun x => ∫ y, (K (x,y))^2 ∂unitMeasure)
  simpa only [pow_two] using (hK.mul hK).integral_left

theorem signedCodegree_bounded {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    BoundedObservable squareMeasure (signedCodegree K) :=
  ((hK.comp edgeZ_qmp).mul (hK.comp edgeY_qmp)).integral_left

theorem signedCodegree_sq_le {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    ∀ᵐ p ∂squareMeasure, (signedCodegree K p)^2 ≤ rowSquare K p.1*rowSquare K p.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (boundedObservable_slices hK),
    Measure.quasiMeasurePreserving_snd.ae (boundedObservable_slices hK)] with p hx hy
  exact integral_mul_sq_le hx hy

theorem integral_rowSquare {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    (∫ x, rowSquare K x ∂unitMeasure) = ∫ p, (K p)^2 ∂squareMeasure := by
  symm
  exact integral_prod _ (by simpa only [pow_two] using (hK.mul hK).integrable)

theorem integral_signedCodegree_sq_le {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    (∫ p, (signedCodegree K p)^2 ∂squareMeasure) ≤ (∫ p, (K p)^2 ∂squareMeasure)^2 := by
  have hc := signedCodegree_bounded hK
  have hr := rowSquare_bounded hK
  have hprod := (hr.comp Measure.quasiMeasurePreserving_fst).mul
    (hr.comp Measure.quasiMeasurePreserving_snd)
  have h := integral_mono_ae
    (show Integrable (fun p => (signedCodegree K p)^2) squareMeasure by simpa only [pow_two] using (hc.mul hc).integrable)
    hprod.integrable (signedCodegree_sq_le hK)
  calc
    _ ≤ ∫ p, rowSquare K p.1*rowSquare K p.2 ∂squareMeasure := h
    _ = (∫ x, rowSquare K x ∂unitMeasure)^2 := by
      rw [integral_prod _ hprod.integrable]
      simp_rw [integral_const_mul]
      rw [integral_mul_const, pow_two]
    _ = _ := by rw [integral_rowSquare hK]

theorem signedTriangle_codegree {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    signedTriangle K = ∫ p, K p*signedCodegree K p ∂squareMeasure := by
  unfold signedTriangle
  rw [integral_prod _ (((hK.comp edgeX_qmp).mul (hK.comp edgeY_qmp)).mul (hK.comp edgeZ_qmp)).integrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    change (∫ z, K p*K (p.2,z)*K (p.1,z) ∂unitMeasure) = K p*signedCodegree K p
    rw [show (fun z => K p*K (p.2,z)*K (p.1,z)) =
      (fun z => K p*(K (p.1,z)*K (p.2,z))) by funext z; ring,
      integral_const_mul]
    rfl

/-- The signed triangle bound in squared form, using only actual integrals. -/
theorem signedTriangle_sq_le {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    (signedTriangle K)^2 ≤ (∫ p, (K p)^2 ∂squareMeasure)^3 := by
  rw [signedTriangle_codegree hK]
  have hcs := integral_mul_sq_le hK (signedCodegree_bounded hK)
  have hsq := integral_signedCodegree_sq_le hK
  have hn : 0 ≤ ∫ p, (K p)^2 ∂squareMeasure := integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ _ := hcs
    _ ≤ (∫ p, (K p)^2 ∂squareMeasure)*(∫ p, (K p)^2 ∂squareMeasure)^2 :=
      mul_le_mul_of_nonneg_left hsq hn
    _ = _ := by ring



/-- The signed triangle bound in L²-norm form. -/
theorem abs_signedTriangle_le {K : ℝ × ℝ → ℝ} (hK : BoundedObservable squareMeasure K) :
    |signedTriangle K| ≤ (Real.sqrt (∫ p, (K p)^2 ∂squareMeasure))^3 := by
  have hn : 0 ≤ ∫ p, (K p)^2 ∂squareMeasure := integral_nonneg fun _ => sq_nonneg _
  apply (sq_le_sq₀ (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)).mp
  rw [sq_abs, show ((Real.sqrt (∫ p, (K p)^2 ∂squareMeasure))^3)^2 =
    (∫ p, (K p)^2 ∂squareMeasure)^3 by
      calc
        _ = ((Real.sqrt (∫ p, (K p)^2 ∂squareMeasure))^2)^3 := by ring
        _ = _ := by rw [Real.sq_sqrt hn]]
  exact signedTriangle_sq_le hK

def centeredKernel (U : Graphon) (s : ℝ) (p : ℝ × ℝ) : ℝ := U p-s

def degreeEnergy (U : Graphon) (s : ℝ) : ℝ :=
  ∫ x, (∫ y, centeredKernel U s (x,y) ∂unitMeasure)^2 ∂unitMeasure

theorem centered_bounded (U : Graphon) (s : ℝ) : BoundedObservable squareMeasure (centeredKernel U s) := by
  simpa only [centeredKernel, sub_eq_add_neg] using
    (graphon_boundedObservable U).add (BoundedObservable.const (-s))

theorem degreeEnergy_nonneg (U : Graphon) (s : ℝ) : 0 ≤ degreeEnergy U s :=
  integral_nonneg fun _ => sq_nonneg _

theorem integral_centered_pair (U : Graphon) (s : ℝ) :
    (∫ p, (X U p-s)*(Z U p-s) ∂tripleMeasure) = degreeEnergy U s := by
  have hK := centered_bounded U s
  have h12 : QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1,p.2.1)) cubeMeasure squareMeasure :=
    QuasiMeasurePreserving.prodMap (QuasiMeasurePreserving.id unitMeasure) Measure.quasiMeasurePreserving_fst
  have h13 : QuasiMeasurePreserving (fun p : ℝ × (ℝ × ℝ) => (p.1,p.2.2)) cubeMeasure squareMeasure :=
    QuasiMeasurePreserving.prodMap (QuasiMeasurePreserving.id unitMeasure) Measure.quasiMeasurePreserving_snd
  have hF := (hK.comp h12).mul (hK.comp h13)
  have hassoc := (measurePreserving_prodAssoc unitMeasure unitMeasure unitMeasure).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun p : ℝ × (ℝ × ℝ) => centeredKernel U s (p.1,p.2.1)*centeredKernel U s (p.1,p.2.2))
  change (∫ p, centeredKernel U s (p.1.1,p.1.2)*centeredKernel U s (p.1.1,p.2) ∂tripleMeasure) = _
  change (∫ p, centeredKernel U s (p.1.1,p.1.2)*centeredKernel U s (p.1.1,p.2) ∂tripleMeasure) =
    (∫ p, centeredKernel U s (p.1,p.2.1)*centeredKernel U s (p.1,p.2.2) ∂cubeMeasure) at hassoc
  rw [hassoc, integral_prod _ hF.integrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∫ p : ℝ × ℝ, centeredKernel U s (x,p.1)*centeredKernel U s (x,p.2) ∂squareMeasure) = _
    simpa only [pow_two] using integral_prod_mul (fun y => centeredKernel U s (x,y))
      (fun y => centeredKernel U s (x,y))

/-- Exact triangle Taylor expansion around a constant graphon. -/
theorem triangle_centered_expansion (U : Graphon) (s : ℝ) :
    triangle U = s^3+3*s^2*(edgeDensity U-s)+3*s*degreeEnergy U s+
      signedTriangle (centeredKernel U s) := by
  let A := fun p => X U p-s
  let B := fun p => Y U p-s
  let C := fun p => Z U p-s
  have hA : BoundedObservable tripleMeasure A := (centered_bounded U s).comp edgeX_qmp
  have hB : BoundedObservable tripleMeasure B := (centered_bounded U s).comp edgeY_qmp
  have hC : BoundedObservable tripleMeasure C := (centered_bounded U s).comp edgeZ_qmp
  have ha : (∫ p, A p ∂tripleMeasure) = edgeDensity U-s := by
    rw [show (∫ p, A p ∂tripleMeasure) = ∫ p, U p-s ∂squareMeasure from
      integral_X (f := fun x => x-s) U (centered_bounded U s)]
    rw [integral_sub (graphon_integrable U) (integrable_const s)]
    simp [edgeDensity]
  have hb : (∫ p, B p ∂tripleMeasure) = edgeDensity U-s :=
    (integral_cycle U (fun x _ _ => x-s)).trans ha
  have hc : (∫ p, C p ∂tripleMeasure) = edgeDensity U-s :=
    (integral_cycle U (fun _ y _ => y-s)).trans hb
  have hac : (∫ p, A p*C p ∂tripleMeasure) = degreeEnergy U s := integral_centered_pair U s
  have hca : (∫ p, C p*A p ∂tripleMeasure) = degreeEnergy U s := by
    simpa only [mul_comm] using hac
  have hbc : (∫ p, B p*C p ∂tripleMeasure) = degreeEnergy U s :=
    (integral_cycle U (fun _ y z => (y-s)*(z-s))).symm.trans hca
  have hab : (∫ p, A p*B p ∂tripleMeasure) = degreeEnergy U s :=
    (integral_cycle U (fun x y _ => (x-s)*(y-s))).symm.trans hbc
  have hp : triangle U = ∫ p,
      (A p*B p*C p + s*(A p*B p)) +
      (s*(B p*C p) + s*(A p*C p)) +
      (s^2*A p + s^2*B p) + (s^2*C p + s^3) ∂tripleMeasure := by
    rw [← integral_XYZ]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by dsimp [A,B,C]; ring
  have h1 := ((hA.mul hB).mul hC).add ((hA.mul hB).const_mul s)
  have h2 := ((hB.mul hC).const_mul s).add ((hA.mul hC).const_mul s)
  have h3 := (hA.const_mul (s^2)).add (hB.const_mul (s^2))
  have h4 := (hC.const_mul (s^2)).add (BoundedObservable.const (s^3))
  rw [hp]
  rw [integral_add (f := fun p => (A p*B p*C p+s*(A p*B p))+(s*(B p*C p)+s*(A p*C p))+
      (s^2*A p+s^2*B p)) (g := fun p => s^2*C p+s^3) ((h1.add h2).add h3).integrable h4.integrable,
    integral_add (f := fun p => (A p*B p*C p+s*(A p*B p))+(s*(B p*C p)+s*(A p*C p)))
      (g := fun p => s^2*A p+s^2*B p) (h1.add h2).integrable h3.integrable,
    integral_add (f := fun p => A p*B p*C p+s*(A p*B p))
      (g := fun p => s*(B p*C p)+s*(A p*C p)) h1.integrable h2.integrable,
    integral_add ((hA.mul hB).mul hC).integrable ((hA.mul hB).const_mul s).integrable,
    integral_add ((hB.mul hC).const_mul s).integrable ((hA.mul hC).const_mul s).integrable,
    integral_add (hA.const_mul (s^2)).integrable (hB.const_mul (s^2)).integrable,
    integral_add (hC.const_mul (s^2)).integrable (integrable_const (s^3))]
  simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
    ha, hb, hc, hac, hab, hbc]
  change signedTriangle (centeredKernel U s) + s*degreeEnergy U s +
    (s*degreeEnergy U s+s*degreeEnergy U s) +
    (s^2*(edgeDensity U-s)+s^2*(edgeDensity U-s)) +
    (s^2*(edgeDensity U-s)+s^3) = _
  ring

end SparseLowerTail.Section02

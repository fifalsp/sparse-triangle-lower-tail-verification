import SparseLowerTail.Section04.VertexIdentity

/-!
# Orthogonal Hoeffding decomposition of a bounded symmetric kernel

Stable manuscript anchor: `lem:hoeffding`. All statements apply to an arbitrary
bounded measurable symmetric real kernel H, and hence to g composed with a graphon.
Orthogonality is stated as vanishing integrals of products, with integrability
proved from boundedness. The shared-edge expectation uses edges (x,y) and (x,z).
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
namespace SparseLowerTail.Section05
open Section04

def hoeffdingMean (H : ℝ × ℝ → ℝ) : ℝ := ∫ p, H p ∂squareMeasure
def hoeffdingRow (H : ℝ × ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, H (x,y) ∂unitMeasure
def hoeffdingFirst (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := hoeffdingRow H p.1-hoeffdingMean H
def hoeffdingSecond (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := hoeffdingRow H p.2-hoeffdingMean H
def hoeffdingResidual (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  H p-hoeffdingRow H p.1-hoeffdingRow H p.2+hoeffdingMean H

/-- Elementary L² polarization, with all integrability discharged by boundedness. -/
theorem integral_square_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ} (hf : BoundedObservable μ f) (hg : BoundedObservable μ g) :
    (∫ x, (f x+g x)^2 ∂μ) = (∫ x, (f x)^2 ∂μ)+2*(∫ x, f x*g x ∂μ)+(∫ x, (g x)^2 ∂μ) := by
  have hff : Integrable (fun x => (f x)^2) μ := by simpa only [pow_two] using (hf.mul hf).integrable
  have hgg : Integrable (fun x => (g x)^2) μ := by simpa only [pow_two] using (hg.mul hg).integrable
  have hfg := (hf.mul hg).integrable.const_mul 2
  have hsum : Integrable (fun x => (f x)^2+2*(f x*g x)) μ := hff.add hfg
  calc
    _ = ∫ x, ((f x)^2+2*(f x*g x))+(g x)^2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by rw [integral_add hsum hgg, integral_add hff hfg, integral_const_mul]

theorem integral_square_centered {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : BoundedObservable μ f) :
    (∫ x, (f x-(∫ y, f y ∂μ))^2 ∂μ) = (∫ x, (f x)^2 ∂μ)-(∫ y, f y ∂μ)^2 := by
  have h := integral_square_add hf (BoundedObservable.const (-(∫ y, f y ∂μ)))
  simp only [← sub_eq_add_neg, integral_mul_const, integral_const, measureReal_univ_eq_one,
    smul_eq_mul, one_mul] at h
  rw [h]
  ring

theorem integral_fst_observable {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    (∫ p : ℝ × ℝ, f p.1 ∂squareMeasure) = ∫ x, f x ∂unitMeasure := by
  rw [integral_prod _ (hf.comp Measure.quasiMeasurePreserving_fst).integrable]
  simp

theorem integral_snd_observable {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f) :
    (∫ p : ℝ × ℝ, f p.2 ∂squareMeasure) = ∫ x, f x ∂unitMeasure := by
  rw [integral_prod _ (hf.comp Measure.quasiMeasurePreserving_snd).integrable]
  simp

theorem integral_separate_observables {f g : ℝ → ℝ}
    (hf : BoundedObservable unitMeasure f) (hg : BoundedObservable unitMeasure g) :
    (∫ p : ℝ × ℝ, f p.1*g p.2 ∂squareMeasure) =
      (∫ x, f x ∂unitMeasure)*(∫ x, g x ∂unitMeasure) := by
  have hp := (hf.comp Measure.quasiMeasurePreserving_fst).mul (hg.comp Measure.quasiMeasurePreserving_snd)
  rw [integral_prod _ hp.integrable]
  simp only [integral_const_mul, integral_mul_const]

variable {H : ℝ × ℝ → ℝ}

theorem hoeffdingRow_bounded (hH : BoundedObservable squareMeasure H) :
    BoundedObservable unitMeasure (hoeffdingRow H) := hH.integral_left

theorem integral_hoeffdingRow (hH : BoundedObservable squareMeasure H) :
    (∫ x, hoeffdingRow H x ∂unitMeasure) = hoeffdingMean H :=
  (integral_prod _ hH.integrable).symm

theorem hoeffdingCenteredRow_bounded (hH : BoundedObservable squareMeasure H) :
    BoundedObservable unitMeasure (fun x => hoeffdingRow H x-hoeffdingMean H) := by
  simpa only [sub_eq_add_neg] using (hoeffdingRow_bounded hH).add (BoundedObservable.const (-hoeffdingMean H))

theorem integral_hoeffdingCenteredRow (hH : BoundedObservable squareMeasure H) :
    (∫ x, hoeffdingRow H x-hoeffdingMean H ∂unitMeasure) = 0 := by
  rw [integral_sub (hoeffdingRow_bounded hH).integrable (integrable_const _), integral_hoeffdingRow hH]
  simp

theorem hoeffdingFirst_bounded (hH : BoundedObservable squareMeasure H) :
    BoundedObservable squareMeasure (hoeffdingFirst H) :=
  (hoeffdingCenteredRow_bounded hH).comp Measure.quasiMeasurePreserving_fst

theorem hoeffdingSecond_bounded (hH : BoundedObservable squareMeasure H) :
    BoundedObservable squareMeasure (hoeffdingSecond H) :=
  (hoeffdingCenteredRow_bounded hH).comp Measure.quasiMeasurePreserving_snd

theorem hoeffdingResidual_bounded (hH : BoundedObservable squareMeasure H) :
    BoundedObservable squareMeasure (hoeffdingResidual H) := by
  have hd := hoeffdingRow_bounded hH
  have hb := ((hH.add ((hd.comp Measure.quasiMeasurePreserving_fst).const_mul (-1))).add
    ((hd.comp Measure.quasiMeasurePreserving_snd).const_mul (-1))).add (BoundedObservable.const (hoeffdingMean H))
  convert hb using 1
  funext p
  unfold hoeffdingResidual
  ring

/-- The decomposition is a pointwise algebraic identity. -/
theorem hoeffding_decomposition (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    H p-hoeffdingMean H = hoeffdingFirst H p+hoeffdingSecond H p+hoeffdingResidual H p := by
  unfold hoeffdingFirst hoeffdingSecond hoeffdingResidual
  ring

/-- The first and second row terms are orthogonal by independence. -/
theorem hoeffding_first_second_orthogonal (hH : BoundedObservable squareMeasure H) :
    (∫ p, hoeffdingFirst H p*hoeffdingSecond H p ∂squareMeasure) = 0 := by
  change (∫ p, (hoeffdingRow H p.1-hoeffdingMean H)*(hoeffdingRow H p.2-hoeffdingMean H) ∂squareMeasure) = 0
  rw [integral_separate_observables (hoeffdingCenteredRow_bounded hH) (hoeffdingCenteredRow_bounded hH),
    integral_hoeffdingCenteredRow hH]
  ring

/-- The residual has zero conditional mean in each row. -/
theorem hoeffdingResidual_row_zero (hH : BoundedObservable squareMeasure H) :
    ∀ᵐ x ∂unitMeasure, (∫ y, hoeffdingResidual H (x,y) ∂unitMeasure) = 0 := by
  filter_upwards [hH.integrable.prod_right_ae] with x hx
  have hd := (hoeffdingRow_bounded hH).integrable
  have hi₁ : Integrable (fun y => H (x,y)-hoeffdingRow H x) unitMeasure := hx.sub (integrable_const _)
  have hi₂ : Integrable (fun y => (H (x,y)-hoeffdingRow H x)-hoeffdingRow H y) unitMeasure := hi₁.sub hd
  change (∫ y, ((H (x,y)-hoeffdingRow H x)-hoeffdingRow H y)+hoeffdingMean H ∂unitMeasure) = 0
  rw [integral_add hi₂ (integrable_const _), integral_sub hi₁ hd,
    integral_sub hx (integrable_const _), integral_hoeffdingRow hH]
  simp [hoeffdingRow]

theorem hoeffding_first_residual_orthogonal (hH : BoundedObservable squareMeasure H) :
    (∫ p, hoeffdingFirst H p*hoeffdingResidual H p ∂squareMeasure) = 0 := by
  rw [integral_prod _ ((hoeffdingFirst_bounded hH).mul (hoeffdingResidual_bounded hH)).integrable]
  have he : (fun x => ∫ y, hoeffdingFirst H (x,y)*hoeffdingResidual H (x,y) ∂unitMeasure) =ᵐ[unitMeasure] 0 := by
    filter_upwards [hoeffdingResidual_row_zero hH] with x hx
    change (∫ y, (hoeffdingRow H x-hoeffdingMean H)*hoeffdingResidual H (x,y) ∂unitMeasure) = 0
    rw [integral_const_mul, hx]
    ring
  rw [integral_congr_ae he]
  simp

theorem hoeffdingResidual_symmetric (hSym : ∀ᵐ p ∂squareMeasure, H p.swap = H p) :
    ∀ᵐ p ∂squareMeasure, hoeffdingResidual H p.swap = hoeffdingResidual H p := by
  filter_upwards [hSym] with p hp
  unfold hoeffdingResidual
  simp only [Prod.fst_swap,Prod.snd_swap,hp]
  ring

theorem hoeffding_second_residual_orthogonal (hH : BoundedObservable squareMeasure H)
    (hSym : ∀ᵐ p ∂squareMeasure, H p.swap = H p) :
    (∫ p, hoeffdingSecond H p*hoeffdingResidual H p ∂squareMeasure) = 0 := by
  calc
    _ = ∫ p, hoeffdingFirst H p.swap*hoeffdingResidual H p.swap ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [hoeffdingResidual_symmetric hSym] with p hp
      rw [hp]
      rfl
    _ = ∫ p, hoeffdingFirst H p*hoeffdingResidual H p ∂squareMeasure :=
      Measure.measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
        (fun p => hoeffdingFirst H p*hoeffdingResidual H p)
    _ = 0 := hoeffding_first_residual_orthogonal hH

/-- The pairwise orthogonality assertion of `lem:hoeffding`. -/
theorem hoeffding_orthogonal (hH : BoundedObservable squareMeasure H)
    (hSym : ∀ᵐ p ∂squareMeasure, H p.swap = H p) :
    (∫ p, hoeffdingFirst H p*hoeffdingSecond H p ∂squareMeasure) = 0 ∧
    (∫ p, hoeffdingFirst H p*hoeffdingResidual H p ∂squareMeasure) = 0 ∧
    (∫ p, hoeffdingSecond H p*hoeffdingResidual H p ∂squareMeasure) = 0 :=
  ⟨hoeffding_first_second_orthogonal hH,hoeffding_first_residual_orthogonal hH,
    hoeffding_second_residual_orthogonal hH hSym⟩

/-- Pythagoras for the orthogonal decomposition. -/
theorem hoeffding_pythagoras (hH : BoundedObservable squareMeasure H)
    (hSym : ∀ᵐ p ∂squareMeasure, H p.swap = H p) :
    (∫ p, (H p-hoeffdingMean H)^2 ∂squareMeasure) =
      2*(∫ x, (hoeffdingRow H x-hoeffdingMean H)^2 ∂unitMeasure)+
        (∫ p, (hoeffdingResidual H p)^2 ∂squareMeasure) := by
  have hf := hoeffdingFirst_bounded hH
  have hg := hoeffdingSecond_bounded hH
  have hh := hoeffdingResidual_bounded hH
  have hc : (∫ p, (hoeffdingFirst H p+hoeffdingSecond H p)*hoeffdingResidual H p ∂squareMeasure) = 0 := by
    rw [show (fun p => (hoeffdingFirst H p+hoeffdingSecond H p)*hoeffdingResidual H p) =
      (fun p => hoeffdingFirst H p*hoeffdingResidual H p+hoeffdingSecond H p*hoeffdingResidual H p) by
        funext p; ring,
      integral_add (hf.mul hh).integrable (hg.mul hh).integrable,
      hoeffding_first_residual_orthogonal hH, hoeffding_second_residual_orthogonal hH hSym]
    ring
  have hb : BoundedObservable unitMeasure (fun x => (hoeffdingRow H x-hoeffdingMean H)^2) := by
    simpa only [pow_two] using (hoeffdingCenteredRow_bounded hH).mul (hoeffdingCenteredRow_bounded hH)
  have h₁ : (∫ p, (hoeffdingFirst H p)^2 ∂squareMeasure) =
      ∫ x, (hoeffdingRow H x-hoeffdingMean H)^2 ∂unitMeasure := integral_fst_observable hb
  have h₂ : (∫ p, (hoeffdingSecond H p)^2 ∂squareMeasure) =
      ∫ x, (hoeffdingRow H x-hoeffdingMean H)^2 ∂unitMeasure := integral_snd_observable hb
  simp_rw [hoeffding_decomposition]
  rw [integral_square_add (hf.add hg) hh, integral_square_add hf hg,
    hc, hoeffding_first_second_orthogonal hH, h₁,h₂]
  ring

/-- The residual energy in terms of kernel and row second moments. -/
theorem hoeffding_row_energy_identity (hH : BoundedObservable squareMeasure H)
    (hSym : ∀ᵐ p ∂squareMeasure, H p.swap = H p) :
    (∫ p, (H p)^2 ∂squareMeasure)-2*(∫ x, (hoeffdingRow H x)^2 ∂unitMeasure)+(hoeffdingMean H)^2 =
      ∫ p, (hoeffdingResidual H p)^2 ∂squareMeasure := by
  have h := hoeffding_pythagoras hH hSym
  have hHc := integral_square_centered hH
  have hdc := integral_square_centered (hoeffdingRow_bounded hH)
  rw [integral_hoeffdingRow hH] at hdc
  change (∫ p, (H p-hoeffdingMean H)^2 ∂squareMeasure) =
    (∫ p, (H p)^2 ∂squareMeasure)-(hoeffdingMean H)^2 at hHc
  rw [hHc,hdc] at h
  linarith

/-- Shared-edge expectation equals the row second moment by Fubini. -/
theorem hoeffding_shared_edge (hH : BoundedObservable squareMeasure H) :
    (∫ p : (ℝ × ℝ) × ℝ, H p.1*H (p.1.1,p.2) ∂TriangleIntegration.tripleMeasure) =
      ∫ x, (hoeffdingRow H x)^2 ∂unitMeasure := by
  have hb := (hH.comp TriangleIntegration.edgeX_qmp).mul (hH.comp TriangleIntegration.edgeZ_qmp)
  rw [integral_prod _ hb.integrable]
  have hinner : (fun p : ℝ × ℝ => ∫ z, H p*H (p.1,z) ∂unitMeasure) =
      (fun p => H p*hoeffdingRow H p.1) := by
    funext p
    rw [integral_const_mul]
    rfl
  rw [hinner, integral_vertex_test_pair hH (hoeffdingRow_bounded hH)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by change hoeffdingRow H x*hoeffdingRow H x = _; ring

/-- The exact expectation identity in `lem:hoeffding`. -/
theorem hoeffding_energy_identity (hH : BoundedObservable squareMeasure H)
    (hSym : ∀ᵐ p ∂squareMeasure, H p.swap = H p) :
    (∫ p, (H p)^2 ∂squareMeasure) -
      2*(∫ p : (ℝ × ℝ) × ℝ, H p.1*H (p.1.1,p.2) ∂TriangleIntegration.tripleMeasure)+
      (∫ p, H p ∂squareMeasure)^2 = ∫ p, (hoeffdingResidual H p)^2 ∂squareMeasure := by
  rw [hoeffding_shared_edge hH]
  exact hoeffding_row_energy_identity hH hSym

/-- The quadratic inequality (T4), before specialization to g composed with U. -/
theorem hoeffding_nonneg (hH : BoundedObservable squareMeasure H)
    (hSym : ∀ᵐ p ∂squareMeasure, H p.swap = H p) :
    0 ≤ (∫ p, (H p)^2 ∂squareMeasure) -
      2*(∫ p : (ℝ × ℝ) × ℝ, H p.1*H (p.1.1,p.2) ∂TriangleIntegration.tripleMeasure)+
      (∫ p, H p ∂squareMeasure)^2 := by
  rw [hoeffding_energy_identity hH hSym]
  exact integral_nonneg fun p => sq_nonneg _


/-- The inequality expressed entirely as expectations of triangle edge values. -/
theorem hoeffding_graphon_nonneg (U : Graphon) (g : ℝ → ℝ)
    (hg : BoundedObservable squareMeasure (fun p => g (U p))) :
    0 ≤ (∫ p, (g (TriangleIntegration.X U p))^2 ∂TriangleIntegration.tripleMeasure) -
      2*(∫ p, g (TriangleIntegration.X U p)*g (TriangleIntegration.Z U p)
        ∂TriangleIntegration.tripleMeasure) +
      (∫ p, g (TriangleIntegration.X U p) ∂TriangleIntegration.tripleMeasure)^2 := by
  have hsq : BoundedObservable squareMeasure (fun p => (g (U p))^2) := by
    simpa only [pow_two] using hg.mul hg
  rw [TriangleIntegration.integral_X U (f := fun u => (g u)^2) hsq, TriangleIntegration.integral_X U hg]
  exact hoeffding_nonneg hg (U.symmetric.mono fun p hp => congrArg g hp)

/-- Direct form of (T4) for every affine entropy observable g(u)=u+ωh(u). -/
theorem hoeffding_affine_entropy_nonneg (U : Graphon) (ω : ℝ) :
    let g := fun u : ℝ => u+ω*entropy u
    0 ≤ (∫ p, (g (TriangleIntegration.X U p))^2 ∂TriangleIntegration.tripleMeasure) -
      2*(∫ p, g (TriangleIntegration.X U p)*g (TriangleIntegration.Z U p)
        ∂TriangleIntegration.tripleMeasure) + (edgeDensity U+ω*cost U)^2 := by
  let g := fun u : ℝ => u+ω*entropy u
  have hg : BoundedObservable squareMeasure (fun p => g (U p)) :=
    (graphon_boundedObservable U).add ((graphon_entropy_boundedObservable U).const_mul ω)
  have h := hoeffding_graphon_nonneg U g hg
  have hm : (∫ p, g (TriangleIntegration.X U p) ∂TriangleIntegration.tripleMeasure) =
      edgeDensity U+ω*cost U := by
    rw [TriangleIntegration.integral_X U hg]
    change (∫ p, U p+ω*entropy (U p) ∂squareMeasure) = _
    rw [integral_add (graphon_integrable U) ((cost_integrable U).const_mul ω), integral_const_mul]
    rfl
  rwa [hm] at h


/-- Constant kernels have zero Hoeffding residual, as used at the critical balanced model. -/
theorem hoeffdingResidual_zero_of_ae_constant {c : ℝ}
    (hc : H =ᵐ[squareMeasure] fun _ => c) :
    hoeffdingResidual H =ᵐ[squareMeasure] 0 := by
  have hm : hoeffdingMean H = c := by
    unfold hoeffdingMean
    rw [integral_congr_ae hc]
    simp
  have hd : ∀ᵐ x ∂unitMeasure, hoeffdingRow H x = c := by
    filter_upwards [Measure.ae_ae_of_ae_prod hc] with x hx
    unfold hoeffdingRow
    rw [integral_congr_ae hx]
    simp
  filter_upwards [hc, Measure.quasiMeasurePreserving_fst.ae hd,
    Measure.quasiMeasurePreserving_snd.ae hd] with p hp hx hy
  change H p-hoeffdingRow H p.1-hoeffdingRow H p.2+hoeffdingMean H = 0
  rw [hp,hx,hy,hm]
  ring

end SparseLowerTail.Section05

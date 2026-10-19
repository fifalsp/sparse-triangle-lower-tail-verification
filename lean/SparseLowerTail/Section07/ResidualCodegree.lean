import SparseLowerTail.Section07.ResidualAction

/-! Exact separation of the leading eigenfunction from the codegree kernel,
including the seven-term identity `eq:s7codeg`. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

private theorem integral_rank_one_product {e u v : ℝ → ℝ} (a b : ℝ)
    (he : BoundedObservable unitMeasure e) (hu : BoundedObservable unitMeasure u)
    (hv : BoundedObservable unitMeasure v)
    (hn : (∫ x, e x*e x ∂unitMeasure)=1)
    (hue : (∫ x, u x*e x ∂unitMeasure)=0)
    (hve : (∫ x, v x*e x ∂unitMeasure)=0) :
    (∫ x, (a*e x+u x)*(b*e x+v x) ∂unitMeasure)=a*b+∫ x, u x*v x ∂unitMeasure := by
  have h₁ := (he.mul he).integrable.const_mul (a*b)
  have h₂ := (hv.mul he).integrable.const_mul a
  have h₃ := (hu.mul he).integrable.const_mul b
  have h₄ := (hu.mul hv).integrable
  have h₁₂ : Integrable (fun x => a*b*(e x*e x)+a*(v x*e x)) unitMeasure := h₁.add h₂
  have h₁₂₃ : Integrable (fun x => a*b*(e x*e x)+a*(v x*e x)+b*(u x*e x)) unitMeasure := h₁₂.add h₃
  calc
    _ = ∫ x, ((a*b*(e x*e x)+a*(v x*e x))+b*(u x*e x))+u x*v x ∂unitMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp; ring
    _ = _ := by
      rw [integral_add h₁₂₃ h₄,integral_add h₁₂ h₃,
        integral_add h₁ h₂,integral_const_mul,integral_const_mul,integral_const_mul,hn,hue,hve]
      ring

/-- Actual square-kernel splitting, with the cross terms killed by Rψ=0. -/
theorem centeredSquare_spectral_split (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U))
    (hψ : BoundedObservable unitMeasure (S.eigenfunction 0)) :
    ∀ᵐ p ∂squareMeasure, centeredSquare U p.1 p.2=
      S.eigenvalue 0^2*S.eigenfunction 0 p.1*S.eigenfunction 0 p.2+residualSquare U S p.1 p.2 := by
  have hrows := boundedObservable_sections (spectralRemainder_bounded S hψ)
  have hzero := spectralRemainder_eigenfunction_zero U S
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrows,Measure.quasiMeasurePreserving_snd.ae hrows,
    Measure.quasiMeasurePreserving_fst.ae hzero,Measure.quasiMeasurePreserving_snd.ae hzero] with p hx hy hxe hye
  have hn : (∫ z, S.eigenfunction 0 z*S.eigenfunction 0 z ∂unitMeasure)=1 := by
    simpa using S.orthonormal_integral 0 0
  have hh := integral_rank_one_product (S.eigenvalue 0*S.eigenfunction 0 p.1)
    (S.eigenvalue 0*S.eigenfunction 0 p.2) hψ hx hy hn hxe hye
  have he : (fun z => (S.eigenvalue 0*S.eigenfunction 0 p.1*S.eigenfunction 0 z+spectralRemainder U S (p.1,z))*
      (S.eigenvalue 0*S.eigenfunction 0 p.2*S.eigenfunction 0 z+spectralRemainder U S (p.2,z)))=
      (fun z => centeredKernel U (p.1,z)*centeredKernel U (p.2,z)) := by
    funext z
    dsimp [spectralRemainder]
    ring
  rw [he] at hh
  dsimp [centeredSquare,residualSquare]
  rw [hh]
  ring

def degreeEigenfunctionPair (U : Graphon) (S : KernelSpectralExpansion (centeredKernel U)) : ℝ :=
  ∫ x, degreeDeviation U x*S.eigenfunction 0 x ∂unitMeasure

/-- The exact decomposition of KD into its leading component and remainder. -/
theorem centeredAction_spectral_split (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U))
    (hψ : BoundedObservable unitMeasure (S.eigenfunction 0)) :
    ∀ᵐ x ∂unitMeasure, centeredAction U (degreeDeviation U) x=
      S.eigenvalue 0*S.eigenfunction 0 x*degreeEigenfunctionPair U S+
        kernelAction (spectralRemainder U S) (degreeDeviation U) x := by
  filter_upwards [boundedObservable_sections (spectralRemainder_bounded S hψ)] with x hx
  have h₁ := ((degreeDeviation_bounded U).mul hψ).integrable.const_mul
    (S.eigenvalue 0*S.eigenfunction 0 x)
  have h₂ := (hx.mul (degreeDeviation_bounded U)).integrable
  dsimp [centeredAction,kernelAction,degreeEigenfunctionPair]
  rw [← integral_const_mul,← integral_add h₁ h₂]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by dsimp [spectralRemainder]; ring

/-- The seven actual integral terms of `eq:s7codeg`, expressed with the sign
function so the same identity covers both blocks. -/
theorem codegree_spectral_error_identity (U : Graphon)
    (S : KernelSpectralExpansion (centeredKernel U))
    (hψ : BoundedObservable unitMeasure (S.eigenfunction 0)) :
    ∀ᵐ p ∂squareMeasure,
      codegree U p.1 p.2-(edgeDensity U*rowDegree U p.1+
        S.eigenvalue 0^2*S.eigenfunction 0 p.1*signBlockFunction (S.eigenfunction 0) p.2)=
      (∫ x, degreeDeviation U x^2 ∂unitMeasure)-
      S.eigenvalue 0*degreeEigenfunctionPair U S*(S.eigenfunction 0 p.1+S.eigenfunction 0 p.2)-
      kernelAction (spectralRemainder U S) (degreeDeviation U) p.1+
      rowDegree U p.1*degreeDeviation U p.2-
      kernelAction (spectralRemainder U S) (degreeDeviation U) p.2+
      S.eigenvalue 0^2*S.eigenfunction 0 p.1*
        (S.eigenfunction 0 p.2-signBlockFunction (S.eigenfunction 0) p.2)+
      residualSquare U S p.1 p.2 := by
  filter_upwards [codegree_centered_expansion U,centeredSquare_spectral_split U S hψ,
    Measure.quasiMeasurePreserving_fst.ae (centeredAction_spectral_split U S hψ),
    Measure.quasiMeasurePreserving_snd.ae (centeredAction_spectral_split U S hψ)] with p hc hs hx hy
  rw [hc,hs,hx,hy]
  dsimp [degreeDeviation]
  ring

end SparseLowerTail.Section07

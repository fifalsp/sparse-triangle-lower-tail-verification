import SparseLowerTail.Section05.CoverCertificate
import SparseLowerTail.Section05.FiniteCover
import SparseLowerTail.Section02.Patterns
import SparseLowerTail.Section02.Existence

/-!
# Critical classification from the cover and apex certificate

This is the actual graphon assembly in the proof of `prop:critical`.
Cover exclusion and apex positivity/zero patterns remain explicit INTERNAL
certificate obligations. No assertion in this file supplies those obligations.
-/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section05
open Section02 Section04 TriangleIntegration

/-- The four critical patterns, as a measurable set of triangle edge values. -/
def criticalPatterns : Set EdgeTriple :=
  {u | AllowedPattern criticalA criticalB u.1.1 u.1.2 u.2}

theorem measurableSet_criticalPatterns : MeasurableSet criticalPatterns := by
  have hm (a b c : ℝ) : MeasurableSet {u : EdgeTriple |
      u.1.1=a ∧ u.1.2=b ∧ u.2=c} :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const).inter
      ((measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const).inter
        (measurableSet_eq_fun measurable_snd measurable_const))
  exact (hm _ _ _).union ((hm _ _ _).union ((hm _ _ _).union (hm _ _ _)))

/-- Transfer the actual pushforward-law patterns to a measurable half partition. -/
theorem balanced_of_triangleLaw_patterns {U : Graphon}
    (hp : ∀ᵐ u ∂triangleLaw U, u ∈ criticalPatterns)
    (he : edgeDensity U = criticalMean) : IsBalanced U criticalA criticalB := by
  have ht := (ae_map_iff (edgeValues_aemeasurable U) measurableSet_criticalPatterns).mp hp
  apply balanced_of_patterns critical_pair_bounds.1 critical_pair_bounds.2
    (ne_of_lt criticalA_lt_criticalB) _ he
  filter_upwards [ht] with p hp
  change AllowedPattern criticalA criticalB (X U p) (Z U p) (Y U p) at hp
  rcases hp with ⟨hx,hz,hy⟩ | ⟨hx,hz,hy⟩ | ⟨hx,hz,hy⟩ | ⟨hx,hz,hy⟩
  · exact Or.inl ⟨hx,hy,hz⟩
  · exact Or.inr (Or.inl ⟨hx,hy,hz⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hx,hy,hz⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hx,hy,hz⟩))

/-- Own-paper numerical/analytic apex obligations; they are not classical inputs.
Only the zero-to-pattern implication is needed for this direction of rigidity. -/
structure CriticalApexCertificate (θ : Fin 12 → ℝ) (lam ell : ℝ) : Prop where
  lam_nonneg : 0 ≤ lam
  support_lower : ell ≤ supportLambda criticalTriangle criticalMean criticalCost
  nonneg : ∀ u ∈ edgeCube ell, 0 ≤ coverCertificate θ lam u (criticalMean,criticalCost)
  zero_patterns : ∀ u ∈ edgeCube ell,
    coverCertificate θ lam u (criticalMean,criticalCost) = 0 → u ∈ criticalPatterns

/-- At the critical parameter, the certificate forces actual graphon rigidity. -/
theorem balanced_of_critical_apex {θ : Fin 12 → ℝ} {lam ell : ℝ}
    (hcert : CriticalApexCertificate θ lam ell) {U : Graphon}
    (hlaw : RelaxedLaw (criticalMean,criticalCost) (triangleLaw U)) :
    IsBalanced U criticalA criticalB := by
  have hz := hlaw.certificate_zero_ae θ hcert.lam_nonneg hcert.support_lower hcert.nonneg
  have hp : ∀ᵐ u ∂triangleLaw U, u ∈ criticalPatterns := by
    filter_upwards [hlaw.supported_of_lower_le hcert.support_lower,hz] with u hu hz
    exact hcert.zero_patterns u hu hz
  apply balanced_of_triangleLaw_patterns hp
  have he := hlaw.edge
  rwa [triangleLaw_edge] at he

/-- The value and all optimizer equality cases follow from precisely the cover
exclusion and apex obligations in the paper. Both remain internal until proved. -/
theorem criticalClassification_of_certificates
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hcount : ClassicalTriangleCounting) (hSampling : UniformSampling)
    (hcover : ∀ π ∈ criticalRegion, π ≠ (criticalMean,criticalCost) →
      ¬∃ ν : Measure EdgeTriple, RelaxedLaw π ν)
    {θ : Fin 12 → ℝ} {lam ell : ℝ} (hcert : CriticalApexCertificate θ lam ell) :
    CriticalClassification := by
  have hclass : ∀ U : Graphon, IsMinimizer threshold U →
      IsConstant U threshold ∨ IsBalanced U criticalA criticalB := by
    intro U hU
    by_cases hc : IsConstant U threshold
    · exact Or.inl hc
    · have hlaw := (minimizer_relaxedLaw hSampling hU).2.2
      have he : (edgeDensity U,cost U) = (criticalMean,criticalCost) := by
        by_contra hn
        exact hcover _ (minimizer_mem_criticalRegion hU hc) hn ⟨triangleLaw U,hlaw⟩
      rw [he] at hlaw
      exact Or.inr (balanced_of_critical_apex hcert hlaw)
  obtain ⟨U,hU⟩ := exists_minimizer hdyadic hcompact hcount
    ⟨threshold_mem_Ioo.1.le,threshold_mem_Ioo.2.le⟩
  refine ⟨?_,hclass⟩
  have he := (isMinimizer_iff.mp hU).2
  rcases hclass U hU with hc | hb
  · exact he.symm.trans (constant_integrals
      ⟨threshold_mem_Ioo.1.le,threshold_mem_Ioo.2.le⟩ hc).2
  · exact he.symm.trans (critical_balanced_integrals hb).2

/-- The finite-data cover connects directly to the critical graphon theorem.
The cover and apex hypotheses are still internal verification obligations. -/
theorem criticalClassification_of_verifiedCover
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hcount : ClassicalTriangleCounting) (hSampling : UniformSampling)
    {ι : Type*} [Fintype ι] {cells : ι → CertificateCell}
    (hcover : VerifiedCertificateCover cells)
    {θ : Fin 12 → ℝ} {lam ell : ℝ} (hcert : CriticalApexCertificate θ lam ell) :
    CriticalClassification :=
  criticalClassification_of_certificates hdyadic hcompact hcount hSampling
    (fun _ hπ hne => hcover.no_relaxedLaw hπ hne) hcert

end SparseLowerTail.Section05

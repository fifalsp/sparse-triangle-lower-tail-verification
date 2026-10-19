import SparseLowerTail.Section05.CoverDefinitions

/-!
# Weak duality for the actual twelve-feature certificate

Stable anchors: `eq:features`, `def:certificate`, `lem:weakdual`.
All integrability follows from the positive support required by `RelaxedLaw`.
No feature expectation, Hoeffding inequality, or certificate expectation is assumed.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
namespace SparseLowerTail.Section05
open Section04

private theorem coverCycle_eq_word : coverCycle = edgePermutationWord [false,true] := rfl

theorem TriangleLawSymmetric.coverCycle_preserving {ν : Measure EdgeTriple}
    (hs : TriangleLawSymmetric ν) : MeasurePreserving coverCycle ν ν := by
  rw [coverCycle_eq_word]
  exact hs.word_preserving _

theorem TriangleLawSymmetric.integral_coverCycle {ν : Measure EdgeTriple}
    (hs : TriangleLawSymmetric ν) (f : EdgeTriple → ℝ) :
    (∫ u, f (coverCycle u) ∂ν) = ∫ u, f u ∂ν := by
  rw [coverCycle_eq_word]
  exact (hs.word_preserving _).integral_comp (edgePermutationWord [false,true]).measurableEmbedding f

theorem cyclicAverage_bounded {ν : Measure EdgeTriple} {f : EdgeTriple → ℝ}
    (hs : TriangleLawSymmetric ν) (hf : BoundedObservable ν f) :
    BoundedObservable ν (cyclicAverage f) := by
  have hfc := hf.comp hs.coverCycle_preserving.quasiMeasurePreserving
  have hfcc := hfc.comp hs.coverCycle_preserving.quasiMeasurePreserving
  convert ((hf.add hfc).add hfcc).mul_const (1/3) using 1
  funext u
  unfold cyclicAverage
  ring

theorem integral_cyclicAverage {ν : Measure EdgeTriple} [IsFiniteMeasure ν]
    {f : EdgeTriple → ℝ} (hs : TriangleLawSymmetric ν) (hf : BoundedObservable ν f) :
    (∫ u, cyclicAverage f u ∂ν) = ∫ u, f u ∂ν := by
  have hfc := hf.comp hs.coverCycle_preserving.quasiMeasurePreserving
  have hfcc := hfc.comp hs.coverCycle_preserving.quasiMeasurePreserving
  have hsum : Integrable (fun u => f u+f (coverCycle u)) ν := hf.integrable.add hfc.integrable
  have hcc : (∫ u, f (coverCycle (coverCycle u)) ∂ν) = ∫ u, f u ∂ν :=
    (hs.integral_coverCycle (fun u => f (coverCycle u))).trans (hs.integral_coverCycle f)
  unfold cyclicAverage
  rw [integral_div, integral_add hsum hfcc.integrable,
    integral_add hf.integrable hfc.integrable, hcc, hs.integral_coverCycle]
  ring

variable {π : ℝ × ℝ} {ν : Measure EdgeTriple}

/-- Coordinate boundedness is a consequence of the actual support condition. -/
theorem RelaxedLaw.first_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => u.1.1) := by
  refine ⟨(measurable_fst.comp measurable_fst).aemeasurable,1,by norm_num,?_⟩
  filter_upwards [hν.supported] with u hu
  have hp : 0 < supportLambda criticalTriangle π.1 π.2 := Real.exp_pos _
  rw [Real.norm_eq_abs,abs_of_nonneg (hp.le.trans hu.1.1)]
  exact hu.1.2

theorem RelaxedLaw.second_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => u.1.2) :=
  hν.first_bounded.comp hν.symmetric.coverCycle_preserving.quasiMeasurePreserving

theorem RelaxedLaw.third_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => u.2) :=
  hν.second_bounded.comp hν.symmetric.coverCycle_preserving.quasiMeasurePreserving

theorem RelaxedLaw.log_first_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => Real.log u.1.1) := by
  let ell := supportLambda criticalTriangle π.1 π.2
  have hell : 0 < ell := Real.exp_pos _
  refine ⟨Real.measurable_log.comp_aemeasurable hν.first_bounded.measurable,
    |Real.log ell|,abs_nonneg _,?_⟩
  filter_upwards [hν.supported] with u hu
  have hlo := Real.log_le_log hell hu.1.1
  have hhi := Real.log_nonpos (hell.le.trans hu.1.1) hu.1.2
  rw [Real.norm_eq_abs,abs_of_nonpos hhi]
  linarith [neg_le_abs (Real.log ell)]

theorem RelaxedLaw.entropy_first_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => entropy u.1.1) := by
  have hb := ((hν.first_bounded.mul hν.log_first_bounded).add
    (hν.first_bounded.const_mul (-1))).add (BoundedObservable.const 1)
  convert hb using 1
  funext u
  unfold entropy
  ring

theorem RelaxedLaw.vertexEntropy_first_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => vertexEntropy u.1.1) := by
  have hb := ((hν.first_bounded.mul hν.log_first_bounded).add
    (hν.first_bounded.const_mul (-2))).add (BoundedObservable.const 2)
  convert hb using 1
  funext u
  unfold vertexEntropy
  ring

theorem boundedObservable_nat_pow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : BoundedObservable μ f) (n : ℕ) :
    BoundedObservable μ (fun x => (f x)^n) := by
  induction n with
  | zero => simpa using (BoundedObservable.const (μ := μ) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem RelaxedLaw.edgeTest_bounded (hν : RelaxedLaw π ν) (j : Fin 5) :
    BoundedObservable ν (fun u => edgeTest j u.1.1) := by
  fin_cases j <;> simp only [edgeTest,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact BoundedObservable.const 1
  · exact hν.first_bounded
  · exact boundedObservable_nat_pow hν.first_bounded 2
  · exact boundedObservable_nat_pow hν.first_bounded 3
  · exact hν.first_bounded.mul hν.log_first_bounded

theorem RelaxedLaw.vertexTest_bounded (hν : RelaxedLaw π ν) (j : Fin 4) :
    BoundedObservable ν (fun u => vertexTest j u.1.1) := by
  fin_cases j <;> simp only [vertexTest,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact hν.first_bounded
  · exact boundedObservable_nat_pow hν.first_bounded 3
  · exact boundedObservable_nat_pow hν.first_bounded 4
  · exact hν.first_bounded.mul hν.log_first_bounded

theorem RelaxedLaw.edgeResidual_bounded (hν : RelaxedLaw π ν) (j : Fin 5) :
    BoundedObservable ν (coverEdgeResidual j π) :=
  (hν.edgeTest_bounded j).mul (hν.log_first_bounded.add
    ((hν.second_bounded.const_mul (relaxationMultiplier π)).mul hν.third_bounded))

theorem RelaxedLaw.vertexResidual_bounded (hν : RelaxedLaw π ν) (j : Fin 4) :
    BoundedObservable ν (coverVertexResidual j π) := by
  have hkB := hν.vertexEntropy_first_bounded.comp hν.symmetric.coverCycle_preserving.quasiMeasurePreserving
  have hkC := hkB.comp hν.symmetric.coverCycle_preserving.quasiMeasurePreserving
  have hb := (hν.vertexTest_bounded j).mul
    ((hkB.add hkC).add (BoundedObservable.const (-2*relaxationVertexMean π)))
  convert hb using 1
  funext u
  unfold coverVertexResidual
  dsimp only [coverCycle]
  ring

theorem RelaxedLaw.observable_first_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => criticalObservable u.1.1) :=
  hν.first_bounded.add (hν.entropy_first_bounded.const_mul criticalOmega)

theorem RelaxedLaw.observable_second_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => criticalObservable u.1.2) :=
  hν.observable_first_bounded.comp hν.symmetric.coverCycle_preserving.quasiMeasurePreserving

theorem RelaxedLaw.feature_bounded (hν : RelaxedLaw π ν) (i : Fin 12) :
    BoundedObservable ν (fun u => certificateFeature i u π) := by
  have h₀ := (cyclicAverage_bounded hν.symmetric hν.first_bounded).add (BoundedObservable.const (-π.1))
  have h₁ := ((hν.first_bounded.mul hν.second_bounded).mul hν.third_bounded).add
    (BoundedObservable.const (-criticalTriangle))
  have h₂ := (cyclicAverage_bounded hν.symmetric hν.entropy_first_bounded).add (BoundedObservable.const (-π.2))
  fin_cases i <;> simp only [certificateFeature,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · simpa only [sub_eq_add_neg] using h₀
  · simpa only [sub_eq_add_neg] using h₁
  · simpa only [sub_eq_add_neg] using h₂
  all_goals first
    | exact cyclicAverage_bounded hν.symmetric (hν.edgeResidual_bounded _)
    | exact cyclicAverage_bounded hν.symmetric (hν.vertexResidual_bounded _)

theorem RelaxedLaw.hoeffding_bounded (hν : RelaxedLaw π ν) :
    BoundedObservable ν (fun u => certificateHoeffding u π) := by
  have hsq := cyclicAverage_bounded hν.symmetric (boundedObservable_nat_pow hν.observable_first_bounded 2)
  have hpair := cyclicAverage_bounded hν.symmetric (hν.observable_first_bounded.mul hν.observable_second_bounded)
  have hb := (hsq.add (hpair.const_mul (-2))).add (BoundedObservable.const ((π.1+criticalOmega*π.2)^2))
  convert hb using 1
  funext u
  unfold certificateHoeffding
  ring

/-- The twelve actual feature expectations vanish; all required integrability is proved above. -/
theorem RelaxedLaw.feature_expectation (hν : RelaxedLaw π ν) (i : Fin 12) :
    (∫ u, certificateFeature i u π ∂ν) = 0 := by
  letI := hν.probability
  have he (j : Fin 5) : (∫ u, cyclicAverage (coverEdgeResidual j π) u ∂ν) = 0 := by
    rw [integral_cyclicAverage hν.symmetric (hν.edgeResidual_bounded j)]
    exact hν.edge_tests j
  have hv (j : Fin 4) : (∫ u, cyclicAverage (coverVertexResidual j π) u ∂ν) = 0 := by
    rw [integral_cyclicAverage hν.symmetric (hν.vertexResidual_bounded j)]
    exact hν.vertex_tests j
  fin_cases i <;> simp only [certificateFeature,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · rw [integral_sub (cyclicAverage_bounded hν.symmetric hν.first_bounded).integrable (integrable_const _),
      integral_cyclicAverage hν.symmetric hν.first_bounded,hν.edge]
    simp
  · rw [integral_sub ((hν.first_bounded.mul hν.second_bounded).mul hν.third_bounded).integrable
      (integrable_const _),hν.triangle]
    simp
  · rw [integral_sub (cyclicAverage_bounded hν.symmetric hν.entropy_first_bounded).integrable (integrable_const _),
      integral_cyclicAverage hν.symmetric hν.entropy_first_bounded,hν.cost]
    simp
  all_goals first | exact he _ | exact hv _

/-- The symmetrized Hoeffding expectation is the (T4) left side. -/
theorem RelaxedLaw.hoeffding_expectation (hν : RelaxedLaw π ν) :
    (∫ u, certificateHoeffding u π ∂ν) =
      (∫ u, (criticalObservable u.1.1)^2 ∂ν)-
      2*(∫ u, criticalObservable u.1.1*criticalObservable u.1.2 ∂ν)+
      (π.1+criticalOmega*π.2)^2 := by
  letI := hν.probability
  have hsq := boundedObservable_nat_pow hν.observable_first_bounded 2
  have hp := hν.observable_first_bounded.mul hν.observable_second_bounded
  have hi₁ := (cyclicAverage_bounded hν.symmetric hsq).integrable
  have hi₂ := (cyclicAverage_bounded hν.symmetric hp).integrable.const_mul 2
  have hi : Integrable (fun u => cyclicAverage (fun v => (criticalObservable v.1.1)^2) u-
      2*cyclicAverage (fun v => criticalObservable v.1.1*criticalObservable v.1.2) u) ν := hi₁.sub hi₂
  unfold certificateHoeffding
  rw [integral_add hi (integrable_const _),integral_sub hi₁ hi₂,integral_const_mul,
    integral_cyclicAverage hν.symmetric hsq,integral_cyclicAverage hν.symmetric hp]
  simp

theorem RelaxedLaw.hoeffding_expectation_nonneg (hν : RelaxedLaw π ν) :
    0 ≤ ∫ u, certificateHoeffding u π ∂ν := by
  rw [hν.hoeffding_expectation]
  exact hν.hoeffding

/-- Every certificate is integrable under a relaxed law. -/
theorem RelaxedLaw.certificate_integrable (hν : RelaxedLaw π ν) (θ : Fin 12 → ℝ) (lam : ℝ) :
    Integrable (fun u => coverCertificate θ lam u π) ν := by
  letI := hν.probability
  have hs := integrable_finset_sum Finset.univ
    (fun i _ => (hν.feature_bounded i).integrable.const_mul (θ i))
  exact hs.neg.sub (hν.hoeffding_bounded.integrable.const_mul lam)

/-- Exact expectation formula in `lem:weakdual`(a). -/
theorem RelaxedLaw.certificate_expectation (hν : RelaxedLaw π ν) (θ : Fin 12 → ℝ) (lam : ℝ) :
    (∫ u, coverCertificate θ lam u π ∂ν) = -lam*(∫ u, certificateHoeffding u π ∂ν) := by
  letI := hν.probability
  have hi := fun i (_ : i ∈ (Finset.univ : Finset (Fin 12))) =>
    (hν.feature_bounded i).integrable.const_mul (θ i)
  have hs := integrable_finset_sum Finset.univ hi
  have hneg : Integrable (fun u => -(∑ i, θ i*certificateFeature i u π)) ν := hs.neg
  unfold coverCertificate
  rw [integral_sub hneg (hν.hoeffding_bounded.integrable.const_mul lam),integral_neg,
    integral_finset_sum Finset.univ hi,integral_const_mul]
  simp only [integral_const_mul,hν.feature_expectation,mul_zero,Finset.sum_const_zero]
  ring

/-- Weak duality: every relaxed law has nonpositive certificate expectation. -/
theorem RelaxedLaw.certificate_expectation_nonpos (hν : RelaxedLaw π ν)
    (θ : Fin 12 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ u, coverCertificate θ lam u π ∂ν) ≤ 0 := by
  rw [hν.certificate_expectation]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) hν.hoeffding_expectation_nonneg

/-- Relaxed-law support lies in any certified larger cube. -/
theorem RelaxedLaw.supported_of_lower_le (hν : RelaxedLaw π ν) {ell₀ : ℝ}
    (hell : ell₀ ≤ supportLambda criticalTriangle π.1 π.2) :
    ∀ᵐ u ∂ν, u ∈ edgeCube ell₀ := by
  filter_upwards [hν.supported] with u hu
  exact ⟨⟨hell.trans hu.1.1,hu.1.2⟩,⟨hell.trans hu.2.1.1,hu.2.1.2⟩,
    ⟨hell.trans hu.2.2.1,hu.2.2.2⟩⟩

/-- `lem:weakdual`(c): a nonnegative certificate vanishes almost surely. -/
theorem RelaxedLaw.certificate_zero_ae (hν : RelaxedLaw π ν) (θ : Fin 12 → ℝ)
    {lam ell₀ : ℝ} (hlam : 0 ≤ lam)
    (hell : ell₀ ≤ supportLambda criticalTriangle π.1 π.2)
    (hpos : ∀ u ∈ edgeCube ell₀, 0 ≤ coverCertificate θ lam u π) :
    ∀ᵐ u ∂ν, coverCertificate θ lam u π = 0 := by
  have hnonneg := (hν.supported_of_lower_le hell).mono fun u hu => hpos u hu
  have hzero : (∫ u, coverCertificate θ lam u π ∂ν) = 0 :=
    le_antisymm (hν.certificate_expectation_nonpos θ hlam) (integral_nonneg_of_ae hnonneg)
  exact (integral_eq_zero_iff_of_nonneg_ae hnonneg (hν.certificate_integrable θ lam)).mp hzero

/-- `lem:weakdual`(b): strict positivity excludes every relaxed law. -/
theorem no_relaxedLaw_of_certificate_pos (θ : Fin 12 → ℝ) {π : ℝ × ℝ} {lam ell₀ : ℝ}
    (hlam : 0 ≤ lam) (hell : ell₀ ≤ supportLambda criticalTriangle π.1 π.2)
    (hpos : ∀ u ∈ edgeCube ell₀, 0 < coverCertificate θ lam u π) :
    ¬∃ ν : Measure EdgeTriple, RelaxedLaw π ν := by
  rintro ⟨ν,hν⟩
  letI := hν.probability
  have hz := hν.certificate_zero_ae θ hlam hell (fun u hu => (hpos u hu).le)
  have hcontr : ∀ᵐ u ∂ν, False := by
    filter_upwards [hz,hν.supported_of_lower_le hell] with u hu hs
    exact (ne_of_gt (hpos u hs)) hu
  exact (hcontr.exists).choose_spec


/-- Literal measure-one conclusion of `lem:weakdual`(c). -/
theorem RelaxedLaw.certificate_zero_set_measure (hν : RelaxedLaw π ν) (θ : Fin 12 → ℝ)
    {lam ell₀ : ℝ} (hlam : 0 ≤ lam)
    (hell : ell₀ ≤ supportLambda criticalTriangle π.1 π.2)
    (hpos : ∀ u ∈ edgeCube ell₀, 0 ≤ coverCertificate θ lam u π) :
    ν {u | u ∈ edgeCube ell₀ ∧ coverCertificate θ lam u π = 0} = 1 := by
  letI := hν.probability
  have hfull : ∀ᵐ u ∂ν, u ∈ {u | u ∈ edgeCube ell₀ ∧ coverCertificate θ lam u π = 0} :=
    (hν.supported_of_lower_le hell).and (hν.certificate_zero_ae θ hlam hell hpos)
  have he : {u | u ∈ edgeCube ell₀ ∧ coverCertificate θ lam u π = 0} =ᵐ[ν] univ :=
    eventuallyEq_univ.mpr hfull
  simpa using measure_congr he


end SparseLowerTail.Section05

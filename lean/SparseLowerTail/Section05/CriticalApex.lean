import SparseLowerTail.Section05.CriticalGraphon
import SparseLowerTail.Section05.CoverCertificate

/-! The critical-apex law and its universal contact identity (`lem:apex`). -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section05
open Section04 TriangleIntegration

def criticalParameter : ℝ × ℝ := (criticalMean,criticalCost)
def criticalSupport : ℝ := supportLambda criticalTriangle criticalMean criticalCost

theorem criticalParameter_mem_domain : criticalParameter∈parameterDomain := by
  have hm : 0<criticalMean := by
    unfold criticalMean
    linarith [critical_strict_bounds.1,critical_strict_bounds.2.2.1,threshold_mem_Ioo.1]
  have ht : 0<criticalTriangle := pow_pos threshold_mem_Ioo.1 3
  have hp := mul_pos criticalMu_pos ht
  constructor
  · exact hm
  · change criticalMean+criticalCost<1
    linarith [critical_multiplier_identity]

theorem critical_relaxation_multiplier : relaxationMultiplier criticalParameter=criticalMu := by
  unfold relaxationMultiplier criticalParameter
  rw [←critical_multiplier_identity]
  exact mul_div_cancel_right₀ _ (ne_of_gt (pow_pos threshold_mem_Ioo.1 3))

/-- The support endpoint is strictly below the smaller critical edge value. -/
theorem criticalSupport_lt_criticalA : criticalSupport<criticalA := by
  have hb := critical_strict_bounds
  have hba : 0<criticalB := threshold_mem_Ioo.1.trans hb.2.2.1
  have ha1 : criticalA<1 := hb.2.1.trans threshold_mem_Ioo.2
  have ht : 0<criticalTriangle := pow_pos threshold_mem_Ioo.1 3
  have hexp : supportExponent criticalTriangle criticalMean criticalCost=
      criticalMu*(1-criticalCost+criticalMean)/2 := by
    rw [supportExponent,div_eq_iff (by positivity : (2:ℝ)*criticalTriangle≠0)]
    have hh := congrArg (fun v:ℝ=>v*(1-criticalCost+criticalMean)) critical_multiplier_identity
    nlinarith [hh]
  have ha := mul_pos hb.1 (sub_pos.mpr ha1)
  have hbb := mul_pos hba (sub_pos.mpr hb.2.2.2)
  have hsum : 0<criticalMu*criticalTriangle+criticalA*(1-criticalA)+criticalB*(1-criticalB) :=
    add_pos (add_pos (mul_pos criticalMu_pos ht) ha) hbb
  have hg := mul_pos criticalMu_pos hsum
  have hlog := critical_balancedEL.1
  have hid := critical_multiplier_identity
  have hm : 2*criticalMean=criticalA+criticalB := by unfold criticalMean; ring
  have he : -supportExponent criticalTriangle criticalMean criticalCost<Real.log criticalA := by
    rw [hexp]
    nlinarith
  have hh := Real.exp_lt_exp.mpr he
  simpa only [criticalSupport,supportLambda,Real.exp_log hb.1] using hh

theorem criticalGraphon_lower (p : ℝ × ℝ) : criticalA≤criticalGraphon p := by
  change criticalA≤blockValue halfInterval criticalA criticalB p
  simp only [blockValue]
  split_ifs <;> first | exact le_rfl | exact criticalA_lt_criticalB.le

/-- Euler-law tests need only the actual Euler equation and a positive lower bound. -/
theorem triangleLaw_edge_test_of_EL {U : Graphon} {ell μ : ℝ} (hell : 0<ell)
    (hU : ∀ᵐ p ∂squareMeasure,ell≤U p)
    (hEL : ∀ᵐ p ∂squareMeasure,Real.log (U p)=-μ*codegree U p.1 p.2)
    {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hb : BoundedObservable squareMeasure (fun p=>φ (U p))) :
    (∫ u,φ u.1.1*(Real.log u.1.1+μ*u.1.2*u.2) ∂triangleLaw U)=0 := by
  have hm : Measurable (fun u:EdgeTriple=>φ u.1.1*(Real.log u.1.1+μ*u.1.2*u.2)) := by fun_prop
  rw [integral_triangleLaw U hm]
  have hh := Certificate.integral_test_residual U (μ:=μ) hell hU hEL hb
  simp only [sub_self,zero_mul] at hh
  convert hh using 1
  congr 1
  funext p
  dsimp [X]
  ring

/-- The vertex-law tests follow from a constant actual row integral. -/
theorem triangleLaw_vertex_test_of_row {U : Graphon} {k : ℝ}
    (hrow : ∀ᵐ x ∂unitMeasure,(∫ y,vertexEntropy (U (x,y)) ∂unitMeasure)=k)
    {χ : ℝ → ℝ} (hχ : Measurable χ)
    (hf : BoundedObservable squareMeasure (fun p=>χ (U p))) :
    (∫ u,χ u.1.1*(vertexEntropy u.1.2+vertexEntropy u.2-2*k) ∂triangleLaw U)=0 := by
  have hm : Measurable (fun u:EdgeTriple=>χ u.1.1*(vertexEntropy u.1.2+vertexEntropy u.2-2*k)) := by
    unfold vertexEntropy
    fun_prop
  rw [integral_triangleLaw U hm]
  have hk := graphon_vertexEntropy_bounded U
  have hy := hk.comp edgeY_qmp
  have hz := hk.comp edgeZ_qmp
  have hb := (hf.comp edgeX_qmp).mul ((hz.add hy).add (BoundedObservable.const (-2*k)))
  have hi : Integrable (fun p=>χ (X U p)*(vertexEntropy (Z U p)+vertexEntropy (Y U p)-2*k)) tripleMeasure := by
    simpa only [sub_eq_add_neg,neg_mul] using hb.integrable
  rw [integral_prod _ hi]
  apply integral_eq_zero_of_ae
  have hri := hk.integrable.prod_right_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrow,
    Measure.quasiMeasurePreserving_snd.ae hrow,
    Measure.quasiMeasurePreserving_fst.ae hri,
    Measure.quasiMeasurePreserving_snd.ae hri] with p hx hy hix hiy
  change (∫ z,χ (U p)*(vertexEntropy (U (p.1,z))+vertexEntropy (U (p.2,z))-2*k) ∂unitMeasure)=0
  have hadd : Integrable (fun z=>vertexEntropy (U (p.1,z))+vertexEntropy (U (p.2,z))) unitMeasure := hix.add hiy
  rw [integral_const_mul,integral_sub hadd (integrable_const _),integral_add hix hiy,hx,hy]
  simp only [integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul]
  ring

/-- All five constraints for the actual critical graphon's pushforward law. -/
theorem criticalGraphon_relaxedLaw : RelaxedLaw criticalParameter (triangleLaw criticalGraphon) := by
  refine ⟨inferInstance,triangleLaw_symmetric _,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (triangleLaw_edge _).trans criticalGraphon_integrals.2.2
  · exact (triangleLaw_triangle _).trans criticalGraphon_integrals.1
  · exact (triangleLaw_cost _).trans criticalGraphon_integrals.2.1
  · intro j
    rw [critical_relaxation_multiplier]
    exact triangleLaw_edge_test_of_EL critical_strict_bounds.1
      (Eventually.of_forall criticalGraphon_lower)
      (Eventually.of_forall fun p=>criticalGraphon_log_equation p.1 p.2)
      (edgeTest_measurable j) (edgeTest_bounded _ j)
  · intro j
    apply triangleLaw_vertex_test_of_row _ (vertexTest_measurable j) (vertexTest_bounded _ j)
    exact Eventually.of_forall fun x=> (criticalGraphon_row_vertexEntropy x).2
  · have hh := triangleLaw_hoeffding criticalGraphon criticalOmega
    simpa only [criticalGraphon_integrals.2.2,criticalGraphon_integrals.2.1,criticalParameter,
      criticalObservable] using hh
  · exact triangleLaw_supported (Eventually.of_forall fun p=>
      criticalSupport_lt_criticalA.le.trans (criticalGraphon_lower p))

/-- The selected Hoeffding observable is pointwise constant on the canonical critical graphon. -/
theorem criticalGraphon_observable (p : ℝ × ℝ) :
    criticalObservable (criticalGraphon p)=criticalMean+criticalOmega*criticalCost := by
  change criticalObservable (blockValue halfInterval criticalA criticalB p)=_
  simp only [blockValue]
  split_ifs
  all_goals first | exact criticalObservable_contacts.2 |
    exact criticalObservable_contacts.1.symm.trans criticalObservable_contacts.2

/-- The last clause of `lem:hoeffding`, for every bounded symmetric kernel. -/
theorem hoeffding_energy_zero_of_ae_constant {H : ℝ × ℝ → ℝ} {c : ℝ}
    (hH : BoundedObservable squareMeasure H)
    (hSym : ∀ᵐ p ∂squareMeasure,H p.swap=H p)
    (hc : H=ᵐ[squareMeasure] fun _=>c) :
    (∫ p,(H p)^2 ∂squareMeasure)-
      2*(∫ p:EdgeTriple,H p.1*H (p.1.1,p.2) ∂tripleMeasure)+
      (∫ p,H p ∂squareMeasure)^2=0 := by
  rw [hoeffding_energy_identity hH hSym]
  have hz := hoeffdingResidual_zero_of_ae_constant hc
  calc
    (∫ p,(hoeffdingResidual H p)^2 ∂squareMeasure)=∫ _,(0:ℝ) ∂squareMeasure := by
      apply integral_congr_ae
      filter_upwards [hz] with p hp
      simp only [Pi.zero_apply] at hp
      rw [hp,zero_pow (by decide : (2:ℕ)≠0)]
    _ =0 := by simp

/-- Exact saturation of the nonlinear Hoeffding constraint at the critical apex. -/
theorem criticalGraphon_hoeffding_zero :
    (∫ u,certificateHoeffding u criticalParameter ∂triangleLaw criticalGraphon)=0 := by
  rw [criticalGraphon_relaxedLaw.hoeffding_expectation]
  have hEntropy : Measurable entropy := continuous_entropy.measurable
  have hm₁ : Measurable (fun u:EdgeTriple=>(criticalObservable u.1.1)^2) := by
    unfold criticalObservable
    fun_prop
  have hm₂ : Measurable (fun u:EdgeTriple=>criticalObservable u.1.1*criticalObservable u.1.2) := by
    unfold criticalObservable
    fun_prop
  rw [integral_triangleLaw _ hm₁,integral_triangleLaw _ hm₂]
  simp only [X,Z,criticalGraphon_observable,criticalParameter]
  simp
  ring

/-- Every twelve-feature certificate has zero expectation at the actual apex law. -/
theorem criticalGraphon_certificate_expectation (θ : Fin 12 → ℝ) (lam : ℝ) :
    (∫ u,coverCertificate θ lam u criticalParameter ∂triangleLaw criticalGraphon)=0 := by
  rw [criticalGraphon_relaxedLaw.certificate_expectation,criticalGraphon_hoeffding_zero,mul_zero]

/-- The common vertex-entropy row level in scalar coordinates. -/
theorem critical_vertex_sum : vertexEntropy criticalA+vertexEntropy criticalB=
    2*relaxationVertexMean criticalParameter := by
  have he := balancedEL_multiplier_triangle critical_balancedEL
  rw [critical_pair_triangle] at he
  change criticalMu*criticalTriangle=-(criticalA*Real.log criticalA+criticalB*Real.log criticalB)/2 at he
  have hc := critical_pair_cost
  have hm := critical_multiplier_identity
  change (entropy criticalA+entropy criticalB)/2=criticalCost at hc
  dsimp [vertexEntropy,entropy,relaxationVertexMean,criticalParameter] at hc ⊢
  linarith

def criticalContact1 : EdgeTriple := ((criticalA,criticalA),criticalA)
def criticalContact2 : EdgeTriple := ((criticalA,criticalB),criticalB)

/-- Each Euler test cancels in the weighted pair of critical contact patterns. -/
theorem critical_edgeResidual_contact (j : Fin 5) :
    cyclicAverage (coverEdgeResidual j criticalParameter) criticalContact1+
      3*cyclicAverage (coverEdgeResidual j criticalParameter) criticalContact2=0 := by
  simp only [cyclicAverage,coverEdgeResidual,coverCycle,criticalContact1,criticalContact2,
    critical_relaxation_multiplier]
  rw [critical_balancedEL.1,critical_balancedEL.2]
  ring

/-- Each vertex test cancels by the constant row level. -/
theorem critical_vertexResidual_contact (j : Fin 4) :
    cyclicAverage (coverVertexResidual j criticalParameter) criticalContact1+
      3*cyclicAverage (coverVertexResidual j criticalParameter) criticalContact2=0 := by
  have hk : relaxationVertexMean criticalParameter=(vertexEntropy criticalA+vertexEntropy criticalB)/2 := by
    linarith [critical_vertex_sum]
  simp only [cyclicAverage,coverVertexResidual,coverCycle,criticalContact1,criticalContact2,hk]
  ring

set_option maxHeartbeats 800000 in
/-- All twelve feature values satisfy the exact critical contact relation. -/
theorem critical_feature_contact (i : Fin 12) :
    certificateFeature i criticalContact1 criticalParameter+
      3*certificateFeature i criticalContact2 criticalParameter=0 := by
  fin_cases i <;> simp only [certificateFeature,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · simp only [cyclicAverage,coverCycle,criticalContact1,criticalContact2,criticalParameter,criticalMean]
    ring
  · have ht := critical_pair_triangle
    dsimp only [balancedTriangle] at ht
    dsimp only [criticalContact1,criticalContact2,criticalTriangle]
    nlinarith
  · have hc := critical_pair_cost
    change (entropy criticalA+entropy criticalB)/2=criticalCost at hc
    simp only [cyclicAverage,coverCycle,criticalContact1,criticalContact2,criticalParameter]
    linarith
  · exact critical_edgeResidual_contact 0
  · exact critical_edgeResidual_contact 1
  · exact critical_edgeResidual_contact 2
  · exact critical_edgeResidual_contact 3
  · exact critical_edgeResidual_contact 4
  · exact critical_vertexResidual_contact 0
  · exact critical_vertexResidual_contact 1
  · exact critical_vertexResidual_contact 2
  · exact critical_vertexResidual_contact 3

/-- The symmetrized Hoeffding integrand vanishes at both critical contacts. -/
theorem critical_hoeffding_contacts :
    certificateHoeffding criticalContact1 criticalParameter=0 ∧
      certificateHoeffding criticalContact2 criticalParameter=0 := by
  have ha := criticalObservable_contacts.2
  have hb := criticalObservable_contacts.1.symm.trans ha
  constructor <;> simp only [certificateHoeffding,cyclicAverage,coverCycle,
    criticalContact1,criticalContact2,ha,hb,criticalParameter] <;> ring

/-- `lem:apex`(b), for all real multipliers (hence in particular every λ≥0). -/
theorem critical_certificate_contact (θ : Fin 12 → ℝ) (lam : ℝ) :
    coverCertificate θ lam criticalContact1 criticalParameter+
      3*coverCertificate θ lam criticalContact2 criticalParameter=0 := by
  have hs : (∑ i:Fin 12, θ i*(certificateFeature i criticalContact1 criticalParameter+
      3*certificateFeature i criticalContact2 criticalParameter))=0 := by
    simp only [critical_feature_contact,mul_zero,Finset.sum_const_zero]
  simp_rw [mul_add,mul_left_comm (θ _) 3,Finset.sum_add_distrib,←Finset.mul_sum] at hs
  simp only [coverCertificate,critical_hoeffding_contacts.1,critical_hoeffding_contacts.2,mul_zero,sub_zero]
  linarith

/-- The full critical-apex lemma for the canonical graphon and its actual law. -/
theorem critical_apex_properties :
    criticalParameter∈parameterDomain ∧ relaxationMultiplier criticalParameter=criticalMu ∧
    criticalSupport<criticalA ∧ RelaxedLaw criticalParameter (triangleLaw criticalGraphon) ∧
    (∫ u,certificateHoeffding u criticalParameter ∂triangleLaw criticalGraphon)=0 ∧
    ∀ θ:Fin 12→ℝ,∀ lam:ℝ,coverCertificate θ lam criticalContact1 criticalParameter+
      3*coverCertificate θ lam criticalContact2 criticalParameter=0 :=
  ⟨criticalParameter_mem_domain,critical_relaxation_multiplier,criticalSupport_lt_criticalA,
    criticalGraphon_relaxedLaw,criticalGraphon_hoeffding_zero,critical_certificate_contact⟩

end SparseLowerTail.Section05

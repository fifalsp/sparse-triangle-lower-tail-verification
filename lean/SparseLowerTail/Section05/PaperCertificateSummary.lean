import SparseLowerTail.Section05.CertificateConcavity
import SparseLowerTail.Section05.CoverCertificate
import SparseLowerTail.Section05.SupportBounds
import SparseLowerTail.Section05.BalancedTriangleLaw
import SparseLowerTail.Section08.CertificateExpectation

/-! Current manuscript interfaces for weak duality, support and balanced codegrees. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section05
open Section04
attribute [local instance] Classical.propDecidable

/-- All four parts of current `lem:weakdual`, including parameter concavity. -/
theorem weak_duality_all (θ : Fin 12 → ℝ) {lam ell₀ : ℝ} {π : ℝ × ℝ}
    (hlam : 0≤lam) (hell : ell₀≤supportLambda criticalTriangle π.1 π.2) :
    (∀ ν:Measure EdgeTriple,RelaxedLaw π ν →
      (∫ u,coverCertificate θ lam u π ∂ν)=-lam*(∫ u,certificateHoeffding u π ∂ν) ∧
      (∫ u,coverCertificate θ lam u π ∂ν)≤0) ∧
    ((∀ u∈edgeCube ell₀,0<coverCertificate θ lam u π) →
      ¬∃ ν:Measure EdgeTriple,RelaxedLaw π ν) ∧
    ((∀ u∈edgeCube ell₀,0≤coverCertificate θ lam u π) →
      ∀ ν:Measure EdgeTriple,RelaxedLaw π ν →
        ν {u | u∈edgeCube ell₀ ∧ coverCertificate θ lam u π=0}=1) ∧
    (∀ u:EdgeTriple,ConcaveOn ℝ univ (coverCertificate θ lam u)) := by
  refine ⟨?_,?_,?_,fun u=>coverCertificate_concave θ hlam u⟩
  · intro ν hν
    exact ⟨hν.certificate_expectation θ lam,hν.certificate_expectation_nonpos θ hlam⟩
  · exact no_relaxedLaw_of_certificate_pos θ hlam hell
  · intro hp ν hν
    exact hν.certificate_zero_set_measure θ hlam hell hp

/-- The literal current support lemma, including the multiplier and vertex-level identities. -/
theorem minimizer_support_data (hSampling : UniformSampling) {r:ℝ}
    (hr:r∈Ioo (0:ℝ) 1) {U:Graphon} (hU:IsMinimizer r U) :
    r≤edgeDensity U ∧
    graphonMultiplier U r*r^3=1-cost U-edgeDensity U ∧
    0<1-cost U-edgeDensity U ∧
    vertexMean U r=1+cost U-edgeDensity U ∧
    ∀ᵐ p ∂squareMeasure,supportLambda (r^3) (edgeDensity U) (cost U)≤U p := by
  have hr0 := ne_of_gt hr.1
  have hm : graphonMultiplier U r*r^3=1-cost U-edgeDensity U := by
    unfold graphonMultiplier
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hr0)
  refine ⟨(minimizer_mean_bounds hr hU).1,hm,?_,vertexMean_eq hr0 U,
    minimizer_supportLambda_lower hSampling hr hU⟩
  rw [←hm]
  exact mul_pos (minimizer_multiplier_pos hr hU) (pow_pos hr.1 3)

/-- The unnumbered codegree computation before `s4:eq:cube`, for all real block
values. This also covers the manuscript's nonnegative kernels above one. -/
theorem codegree_blockValue_real {P:Set ℝ} (hP:MeasurableSet P)
    (hm:unitMeasure P=(1/2:ENNReal)) (a b x y:ℝ) :
    (∫ z,blockValue P a b (x,z)*blockValue P a b (y,z) ∂unitMeasure)=
      if (x∈P ↔ y∈P) then (a^2+b^2)/2 else a*b := by
  classical
  by_cases hx:x∈P <;> by_cases hy:y∈P
  all_goals
    simp only [blockValue,hx,hy,if_true,if_false]
    simp (config:={contextual:=true}) only
      [mul_ite,if_true,if_false,true_iff,false_iff,not_true_eq_false]
  all_goals (rw [integral_half_partition hP hm]; ring)

/-- The last claim of current `s8:expect`, deduced from the actual four-atom law
and the proved zero expectation, without assuming individual contact values. -/
theorem branch_certificate_contact_identity {z:ℝ} (hz:0<z) (hz1:z<1) :
    Certificate.psi z (branchA z) (branchA z) (branchA z)+
      3*Certificate.psi z (branchA z) (branchB z) (branchB z)=0 := by
  let U := branchGraphon z hz hz1
  let f : EdgeTriple → ℝ := fun u=>Certificate.psi z u.1.1 u.2 u.1.2
  have hf : Measurable f := by
    dsimp [f]
    unfold Certificate.psi Certificate.potential
    fun_prop
  have hzero : (∫ u,f u ∂triangleLaw U)=0 := by
    rw [integral_triangleLaw U hf]
    exact Certificate.expectation_branch_zero hz hz1
  obtain ⟨ha,hb⟩ := (branchGraphon_isBalanced hz hz1).values_mem_Icc
  have he := integral_triangleLaw_balanced_any (branchA z) (branchB z) ha hb f
  change (∫ u,f u ∂triangleLaw U)=_ at he
  dsimp [f] at he
  rw [Certificate.psi_swap_xw z (branchB z) (branchB z) (branchA z),
    Certificate.psi_swap_xy z (branchB z) (branchA z) (branchB z)] at he
  linarith

end SparseLowerTail.Section05

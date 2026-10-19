import SparseLowerTail.Section05.TriangleLawSymmetry
import SparseLowerTail.Section05.CriticalRegion

/-! The finite triangle-law relaxation (`def:relaxed`) and its validity for
actual critical minimizers (`lem:valid`). All five conditions are represented;
permutation invariance is expressed by the two generating transpositions. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section05
open Section04 TriangleIntegration

def criticalOmega : ℝ := (criticalB-criticalA)/(entropy criticalA-entropy criticalB)

def criticalObservable (u : ℝ) : ℝ := u+criticalOmega*entropy u

def relaxationMultiplier (π : ℝ × ℝ) : ℝ := (1-π.2-π.1)/criticalTriangle

def relaxationVertexMean (π : ℝ × ℝ) : ℝ := 1+π.2-π.1

def edgeTest (j : Fin 5) (u : ℝ) : ℝ := ![1,u,u^2,u^3,u*Real.log u] j

def vertexTest (j : Fin 4) (u : ℝ) : ℝ := ![u,u^3,u^4,u*Real.log u] j

theorem criticalA_lt_criticalB : criticalA < criticalB :=
  branchA_lt_branchB (transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2)

theorem critical_entropy_gap_pos : 0 < entropy criticalA-entropy criticalB := by
  exact sub_pos.mpr (strictAntiOn_entropy critical_pair_bounds.1 critical_pair_bounds.2
    criticalA_lt_criticalB)

theorem criticalOmega_pos : 0 < criticalOmega :=
  div_pos (sub_pos.mpr criticalA_lt_criticalB) critical_entropy_gap_pos

/-- Exact equal-level identity used to choose the Hoeffding observable. -/
theorem criticalObservable_contacts :
    criticalObservable criticalA = criticalObservable criticalB ∧
      criticalObservable criticalA = criticalMean+criticalOmega*criticalCost := by
  have hden : entropy criticalA-entropy criticalB ≠ 0 := ne_of_gt critical_entropy_gap_pos
  have he : criticalObservable criticalA = criticalObservable criticalB := by
    unfold criticalObservable criticalOmega
    field_simp
    ring
  refine ⟨he,?_⟩
  have hc := critical_pair_cost
  change (entropy criticalA+entropy criticalB)/2 = criticalCost at hc
  have hm := congrArg (fun x => criticalOmega*x) hc
  dsimp [criticalObservable] at he ⊢
  unfold criticalMean
  nlinarith

theorem criticalObservable_constant_on_balanced {U : Graphon}
    (hU : IsBalanced U criticalA criticalB) :
    (fun p => criticalObservable (U p)) =ᵐ[squareMeasure]
      (fun _ => criticalMean+criticalOmega*criticalCost) := by
  classical
  obtain ⟨P,_,_,_,heq⟩ := hU
  filter_upwards [heq] with p hp
  rw [hp]
  split_ifs
  · exact criticalObservable_contacts.2
  · exact criticalObservable_contacts.1.symm.trans criticalObservable_contacts.2

theorem edgeTest_measurable (j : Fin 5) : Measurable (edgeTest j) := by
  unfold edgeTest
  fin_cases j <;> dsimp
  all_goals fun_prop

theorem vertexTest_measurable (j : Fin 4) : Measurable (vertexTest j) := by
  unfold vertexTest
  fin_cases j <;> dsimp
  all_goals fun_prop

theorem graphon_pow_bounded (U : Graphon) (n : ℕ) :
    BoundedObservable squareMeasure (fun p => (U p)^n) := by
  induction n with
  | zero => simpa using (BoundedObservable.const (μ := squareMeasure) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul (graphon_boundedObservable U)

theorem edgeTest_bounded (U : Graphon) (j : Fin 5) :
    BoundedObservable squareMeasure (fun p => edgeTest j (U p)) := by
  unfold edgeTest
  fin_cases j <;> dsimp
  · exact BoundedObservable.const 1
  · exact graphon_boundedObservable U
  · exact graphon_pow_bounded U 2
  · exact graphon_pow_bounded U 3
  · exact graphon_mulLog_boundedObservable U

theorem vertexTest_bounded (U : Graphon) (j : Fin 4) :
    BoundedObservable squareMeasure (fun p => vertexTest j (U p)) := by
  unfold vertexTest
  fin_cases j <;> dsimp
  · exact graphon_boundedObservable U
  · exact graphon_pow_bounded U 3
  · exact graphon_pow_bounded U 4
  · exact graphon_mulLog_boundedObservable U

structure RelaxedLaw (π : ℝ × ℝ) (ν : Measure EdgeTriple) : Prop where
  probability : IsProbabilityMeasure ν
  symmetric : TriangleLawSymmetric ν
  edge : (∫ u, u.1.1 ∂ν) = π.1
  triangle : (∫ u, u.1.1*u.1.2*u.2 ∂ν) = criticalTriangle
  cost : (∫ u, entropy u.1.1 ∂ν) = π.2
  edge_tests : ∀ j : Fin 5,
    (∫ u, edgeTest j u.1.1*(Real.log u.1.1+relaxationMultiplier π*u.1.2*u.2) ∂ν) = 0
  vertex_tests : ∀ j : Fin 4,
    (∫ u, vertexTest j u.1.1*(vertexEntropy u.1.2+vertexEntropy u.2-
      2*relaxationVertexMean π) ∂ν) = 0
  hoeffding : 0 ≤ (∫ u, (criticalObservable u.1.1)^2 ∂ν)-
    2*(∫ u, criticalObservable u.1.1*criticalObservable u.1.2 ∂ν)+
      (π.1+criticalOmega*π.2)^2
  supported : ∀ᵐ u ∂ν, u ∈ edgeCube (supportLambda criticalTriangle π.1 π.2)

/-- Complete `lem:valid` for the actual pushforward probability law. -/
theorem minimizer_relaxedLaw (hSampling : UniformSampling) {U : Graphon}
    (hU : IsMinimizer threshold U) :
    (edgeDensity U,cost U) ∈ parameterDomain ∧
      graphonMultiplier U threshold = relaxationMultiplier (edgeDensity U,cost U) ∧
      RelaxedLaw (edgeDensity U,cost U) (triangleLaw U) := by
  have hr := threshold_mem_Ioo
  refine ⟨minimizer_parameter_domain hr hU, rfl, ?_⟩
  refine ⟨inferInstance, triangleLaw_symmetric U, triangleLaw_edge U, ?_,
    triangleLaw_cost U, ?_, ?_, ?_, ?_⟩
  · rw [triangleLaw_triangle U,minimizer_triangle_eq hr hU]
    rfl
  · intro j
    exact triangleLaw_edge_test hr hU (edgeTest_measurable j) (edgeTest_bounded U j)
  · intro j
    have h := triangleLaw_vertex_test hSampling hr hU
      (vertexTest_measurable j) (vertexTest_bounded U j)
    simpa only [vertexMean_eq (ne_of_gt hr.1),relaxationVertexMean] using h
  · exact triangleLaw_hoeffding U criticalOmega
  · exact minimizer_triangleLaw_supported hSampling hr hU

end SparseLowerTail.Section05

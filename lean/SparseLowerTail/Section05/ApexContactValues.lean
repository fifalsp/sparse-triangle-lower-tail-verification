import SparseLowerTail.Section05.ApexLocalBridge
import SparseLowerTail.Section04.BalancedStationary

/-! The missing mixed-contact value is an exact algebraic consequence of the
all-a contact value, for every coefficient vector and multiplier. This is the
identity used to reduce the fan tangency system to four equations. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section04 Certificate

def apexAAA : EdgeTriple := ((criticalA,criticalA),criticalA)
def apexABB : EdgeTriple := ((criticalA,criticalB),criticalB)

theorem criticalMultiplier_eq_branchMu :
    relaxationMultiplier criticalPoint=branchMu transitionParameter := by
  have h := balancedEL_multiplier_cost (branch_balancedEL transitionParameter_mem_Ioo.1
    (transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2))
  change branchMu transitionParameter*balancedTriangle criticalA criticalB =
    1-balancedCost criticalA criticalB-(criticalA+criticalB)/2 at h
  rw [critical_pair_triangle,critical_pair_cost] at h
  have ht : criticalTriangle≠0 := (pow_pos threshold_mem_Ioo.1 3).ne'
  unfold relaxationMultiplier criticalPoint
  dsimp only
  apply (div_eq_iff ht).mpr
  simpa only [criticalTriangle,criticalCost,criticalMean,mul_comm] using h.symm

theorem critical_apex_EL :
    BalancedEL criticalA criticalB (relaxationMultiplier criticalPoint) := by
  rw [criticalMultiplier_eq_branchMu]
  exact branch_balancedEL transitionParameter_mem_Ioo.1
    (transitionParameter_mem_Ioo.2.trans spinodal_spec.1.2)

theorem critical_vertexEntropy_sum :
    vertexEntropy criticalA+vertexEntropy criticalB=2*relaxationVertexMean criticalPoint := by
  have hc := critical_pair_cost
  change (entropy criticalA+entropy criticalB)/2=criticalCost at hc
  simp only [vertexEntropy,entropy] at hc ⊢
  unfold relaxationVertexMean criticalPoint criticalMean
  dsimp only
  linarith

theorem apexEdgeResidual_weighted (j : Fin 5) :
    cyclicAverage (coverEdgeResidual j criticalPoint) apexAAA+
      3*cyclicAverage (coverEdgeResidual j criticalPoint) apexABB=0 := by
  have ha := critical_apex_EL.1
  have hb := critical_apex_EL.2
  simp only [cyclicAverage,coverCycle,apexAAA,apexABB,coverEdgeResidual]
  rw [ha,hb]
  ring

theorem apexVertexResidual_weighted (j : Fin 4) :
    cyclicAverage (coverVertexResidual j criticalPoint) apexAAA+
      3*cyclicAverage (coverVertexResidual j criticalPoint) apexABB=0 := by
  have hv := critical_vertexEntropy_sum
  have he : vertexEntropy criticalB=2*relaxationVertexMean criticalPoint-vertexEntropy criticalA := by linarith
  simp only [cyclicAverage,coverCycle,apexAAA,apexABB,coverVertexResidual]
  rw [he]
  ring

theorem apexFeature_weighted (i : Fin 12) :
    certificateFeature i apexAAA criticalPoint+
      3*certificateFeature i apexABB criticalPoint=0 := by
  fin_cases i
  · change (criticalA+criticalA+criticalA)/3-criticalMean+
      3*((criticalA+criticalB+criticalB)/3-criticalMean)=0
    unfold criticalMean
    ring
  · have ht := critical_pair_triangle
    change (criticalA^3+3*criticalA*criticalB^2)/4=criticalTriangle at ht
    change criticalA*criticalA*criticalA-criticalTriangle+
      3*(criticalA*criticalB*criticalB-criticalTriangle)=0
    nlinarith only [ht]
  · have hc := critical_pair_cost
    change (entropy criticalA+entropy criticalB)/2=criticalCost at hc
    change (entropy criticalA+entropy criticalA+entropy criticalA)/3-criticalCost+
      3*((entropy criticalA+entropy criticalB+entropy criticalB)/3-criticalCost)=0
    linarith
  · exact apexEdgeResidual_weighted 0
  · exact apexEdgeResidual_weighted 1
  · exact apexEdgeResidual_weighted 2
  · exact apexEdgeResidual_weighted 3
  · exact apexEdgeResidual_weighted 4
  · exact apexVertexResidual_weighted 0
  · exact apexVertexResidual_weighted 1
  · exact apexVertexResidual_weighted 2
  · exact apexVertexResidual_weighted 3

theorem apexHoeffding_AAA : certificateHoeffding apexAAA criticalPoint=0 := by
  simp only [certificateHoeffding,cyclicAverage,coverCycle,apexAAA,criticalPoint]
  rw [criticalObservable_contacts.2]
  ring

theorem apexHoeffding_ABB : certificateHoeffding apexABB criticalPoint=0 := by
  simp only [certificateHoeffding,cyclicAverage,coverCycle,apexABB,criticalPoint]
  rw [←criticalObservable_contacts.1,criticalObservable_contacts.2]
  ring

theorem apexCertificate_weighted (θ : Fin 12 → ℝ) (lam : ℝ) :
    coverCertificate θ lam apexAAA criticalPoint+
      3*coverCertificate θ lam apexABB criticalPoint=0 := by
  simp only [coverCertificate,apexHoeffding_AAA,apexHoeffding_ABB,mul_zero,sub_zero]
  have hsum : (∑i,θ i*certificateFeature i apexAAA criticalPoint)+
      3*(∑i,θ i*certificateFeature i apexABB criticalPoint)=0 := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have h := congrArg (fun t : ℝ => θ i*t) (apexFeature_weighted i)
    nlinarith only [h]
  linarith

theorem apexCertificate_ABB_zero_of_AAA {θ : Fin 12 → ℝ} {lam : ℝ}
    (h : coverCertificate θ lam apexAAA criticalPoint=0) :
    coverCertificate θ lam apexABB criticalPoint=0 := by
  linarith [apexCertificate_weighted θ lam]

end SparseLowerTail.Section05

import SparseLowerTail.Section08.FiniteCertificateAssembly
import SparseLowerTail.Section02.RelabelBalanced

/-! Literal current crossing and tie-exclusion conclusions. -/
noncomputable section
open Set
namespace SparseLowerTail.Section08
open Section02 Section04 Section05 Section06 Section07

/-- The complete crossing statement, including the closed fold endpoint. -/
theorem penalized_crossing_all :
    penalizedCrossing ∈ Ioo (0:ℝ) (1/1000) ∧
    penalizedCrossing ∈ Ioc (0:ℝ) foldPoint ∧
    (∀ z ∈ Ioc (0:ℝ) foldPoint,penalizedGap z=0 ↔ z=penalizedCrossing) ∧
    (∀ z ∈ Ioo (0:ℝ) penalizedCrossing,penalizedGap z<0) ∧
    (∀ z ∈ Ioc penalizedCrossing foldPoint,0<penalizedGap z) := by
  exact ⟨penalizedCrossing_spec.1,⟨penalizedCrossing_spec.1.1,penalizedCrossing_lt_fold.le⟩,
    fun _ hz => penalizedGap_zero_iff hz,fun _ hz => penalizedGap_neg_before hz,
    fun _ hz => penalizedGap_pos_after hz⟩

/-- The current tie-exclusion lemma on its exact target interval, with an actual relabeling. -/
theorem middle_tie_relabeling (hCDF : ClassicalCDFTransport) (hfamily : MiddleFamilyCertificate)
    {r : ℝ} (hr : r ∈ Icc smallTarget threshold) {U : Graphon} (hU : IsMinimizer r U)
    (hF : cost U=balancedCost (branchA (leftBranch r)) (branchB (leftBranch r)))
    (he : (branchA (leftBranch r)+branchB (leftBranch r))/2≤edgeDensity U) :
    ∃ (ha : branchA (leftBranch r) ∈ Icc (0:ℝ) 1)
      (hb : branchB (leftBranch r) ∈ Icc (0:ℝ) 1),
      IsBalancedRelabeling U (branchA (leftBranch r)) (branchB (leftBranch r)) ha hb := by
  have hr0 : 0<r := smallTarget_mem_unit.1.trans_le hr.1
  have hr1 : r<1 := hr.2.trans_lt threshold_mem_Ioo.2
  obtain ⟨hz,hz40⟩ := leftBranch_le_one_fortieth ⟨hr0,hr.2⟩
  have hz1 : leftBranch r<1 := by linarith
  have htspin : threshold<spinodalValue := by
    rw [threshold_eq_transitionTarget]
    exact transitionTarget_spec.1.2
  have ht : balancedTriangle (branchA (leftBranch r)) (branchB (leftBranch r))=r^3 := by
    rw [branch_triangle_eq_rho_cube hz,branchRho_leftBranch ⟨hr0.le,hr.2.trans htspin.le⟩]
  have hbal := Certificate.minimizer_balanced_of_tie_certificate ⟨hr0,hr1⟩ hz hz40
    hU ht hF he (hfamily r hr)
  have ha : branchA (leftBranch r) ∈ Icc (0:ℝ) 1 :=
    ⟨(branchA_pos hz).le,(branchA_lt_branchB hz1).le.trans (branchB_lt_one hz hz1).le⟩
  have hb : branchB (leftBranch r) ∈ Icc (0:ℝ) 1 :=
    ⟨(branchB_pos _).le,(branchB_lt_one hz hz1).le⟩
  exact ⟨ha,hb,Section02.IsBalanced.exists_relabel hCDF hbal ha hb⟩

/-- The tie conclusion needs only the explicit compact-family certificate as remaining author input. -/
theorem middle_tie_relabeling_of_compact (hCDF : ClassicalCDFTransport)
    (hfamily : CompactFamilyCertificate) {r : ℝ} (hr : r ∈ Icc smallTarget threshold)
    {U : Graphon} (hU : IsMinimizer r U)
    (hF : cost U=balancedCost (branchA (leftBranch r)) (branchB (leftBranch r)))
    (he : (branchA (leftBranch r)+branchB (leftBranch r))/2≤edgeDensity U) :
    ∃ (ha : branchA (leftBranch r) ∈ Icc (0:ℝ) 1)
      (hb : branchB (leftBranch r) ∈ Icc (0:ℝ) 1),
      IsBalancedRelabeling U (branchA (leftBranch r)) (branchB (leftBranch r)) ha hb :=
  middle_tie_relabeling hCDF (middleFamilyCertificate_of_compact hfamily) hr hU hF he

end SparseLowerTail.Section08

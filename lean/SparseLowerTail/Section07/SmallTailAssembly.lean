import SparseLowerTail.Section07.SmallTargetBipodal
import SparseLowerTail.Section07.SmallData
import SparseLowerTail.Section07.ClassicalKernelSpectrum
import SparseLowerTail.Section06.Stability

/-! Final interfaces for small-target classification. The supporting branch
already gives actual attainment, so the converse does not need compactness.
The structural bipodality theorem is proved for actual minimizers. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04 Section06

/-- Every graphon with the balanced branch values is an actual minimizer.
This uses the proved supporting range, not an assumed classification. -/
theorem smallTarget_isMinimizer_of_balanced (external : KP26PenalizedReduction)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) {U : Graphon}
    (hU : IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r))) :
    IsMinimizer r U := by
  obtain ⟨W,hW,hBW⟩ := smallTarget_branch_minimizer external hr
  obtain ⟨ha,hb⟩ := hU.values_mem_Icc
  apply isMinimizer_iff.mpr
  constructor
  · change triangle U≤r^3
    rw [hU.triangle_eq ha hb,←hBW.triangle_eq ha hb]
    exact hW.1
  · rw [hU.cost_eq ha hb,←hBW.cost_eq ha hb]
    exact (isMinimizer_iff.mp hW).2

/-- Produce the spectral data required by the structural argument from exactly
the recorded classical spectral theorem and internally proved hypotheses. -/
theorem smallTarget_spectral_expansion (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) {U : Graphon} (hU : IsMinimizer r U) :
    Nonempty (KernelSpectralExpansion (centeredKernel U)) := by
  have hz := (smallTarget_support hr).1
  have hμ := branchMu_pos hz.1 (hz.2.trans_lt penalizedCrossing_mem_unit.2)
  exact centeredKernel_spectral_expansion hSpectral hSampling
    ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
    (div_nonneg hμ.le (by norm_num : (0:ℝ)≤3)) hU
    ((smallTarget_data external hr).2 U hU).2.2

/-- Once a particular minimizer is bipodal, the already-proved bipodal
classification identifies its exact balanced branch values. -/
theorem smallTarget_balanced_of_bipodal (hSampling : UniformSampling)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) {U : Graphon} (hU : IsMinimizer r U)
    (hbip : ∃ c a d b,IsBipodal U c a d b) :
    IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) := by
  obtain ⟨c,a,d,b,hB⟩ := hbip
  exact (bipodal_minimizer_classification hSampling
    ⟨hr.1,hr.2.trans_lt smallTarget_lt_threshold⟩ hU hB).1

/-- Complete small-target classification among all graphons, relative only to
KP26 and the stated classical sampling/spectral results. -/
theorem smallTarget_classification (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) : BranchClassification r := by
  intro U
  constructor
  · intro hU
    obtain ⟨S⟩ := smallTarget_spectral_expansion external hSampling hSpectral hr hU
    exact smallTarget_balanced_of_bipodal hSampling hr hU
      (smallTarget_isBipodal external hSampling hr hU S)
  · exact smallTarget_isMinimizer_of_balanced external hr

theorem smallTarget_branch_values {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) :
    branchA (leftBranch r)∈Icc (0:ℝ) 1 ∧ branchB (leftBranch r)∈Icc (0:ℝ) 1 := by
  obtain ⟨ha,hab,hb,_,_⟩ := branch_data_at ⟨hr.1,(hr.2.trans_lt smallTarget_lt_threshold).le⟩
  exact ⟨⟨ha.le,(hab.trans hb).le⟩,⟨(ha.trans hab).le,hb.le⟩⟩

/-- The literal relabeling formulation of thm:smalltail, using the recorded
classical nonatomic CDF transport to identify measurable half partitions. -/
theorem smallTarget_relabel_classification (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem)
    (hCDF : Section02.ClassicalCDFTransport)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget) :
    ∀ U : Graphon,IsMinimizer r U ↔
      Section02.IsBalancedRelabeling U (branchA (leftBranch r)) (branchB (leftBranch r))
        (smallTarget_branch_values hr).1 (smallTarget_branch_values hr).2 :=
  (branchClassification_relabel_iff hCDF _ _).mp
    (smallTarget_classification external hSampling hSpectral hr)

end SparseLowerTail.Section07

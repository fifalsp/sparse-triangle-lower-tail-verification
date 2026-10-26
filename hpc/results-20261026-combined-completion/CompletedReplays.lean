import SparseLowerTail
import SparseLowerTail.MainReplayAssembly
import SparseLowerTail.Section05.CoverJobReplay.Job00Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job01Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job02Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job03Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job04Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job05Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job06Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job07Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job08Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job09Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job10Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job11Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job12Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job13Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job14Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job15Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job16Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job17Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job18Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job19Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job20Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job21Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job22Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job23Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job24Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job26Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job27Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job28Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job29Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job30Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job31Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job32Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job33Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job34Full.Ordered
import SparseLowerTail.Section05.CoverJobReplay.Job35Full.Ordered
import SparseLowerTail.Section05.ApexReplay.F1.FullCube
import SparseLowerTail.Section05.ApexReplay.F2.FullCube
import SparseLowerTail.Section05.ApexReplay.F3.FullCube
import SparseLowerTail.Section05.ApexReplay.F4.FullCube
import SparseLowerTail.Section05.ApexReplay.F5.FullCube
import SparseLowerTail.Section05.ApexReplay.F6.FullCube
import SparseLowerTail.Section08.FamilyABBReplay.Full.FullNeighborhood
import SparseLowerTail.Section08.FamilyABBRadiusReplay.Full.FullNeighborhood
import SparseLowerTail.Section08.FamilyExteriorReplay.Full.CompactCertificate
noncomputable section
namespace SparseLowerTail.CompletedReplays
open Section02 Section04 Section05 Section07 Section08 Certificate Section05.CoverGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem all_nonapex : NonapexJobResults := by
  intro j q hq
  fin_cases j
  · exact CoverJobReplay.Job00Full.ordered hq
  · exact CoverJobReplay.Job01Full.ordered hq
  · exact CoverJobReplay.Job02Full.ordered hq
  · exact CoverJobReplay.Job03Full.ordered hq
  · exact CoverJobReplay.Job04Full.ordered hq
  · exact CoverJobReplay.Job05Full.ordered hq
  · exact CoverJobReplay.Job06Full.ordered hq
  · exact CoverJobReplay.Job07Full.ordered hq
  · exact CoverJobReplay.Job08Full.ordered hq
  · exact CoverJobReplay.Job09Full.ordered hq
  · exact CoverJobReplay.Job10Full.ordered hq
  · exact CoverJobReplay.Job11Full.ordered hq
  · exact CoverJobReplay.Job12Full.ordered hq
  · exact CoverJobReplay.Job13Full.ordered hq
  · exact CoverJobReplay.Job14Full.ordered hq
  · exact CoverJobReplay.Job15Full.ordered hq
  · exact CoverJobReplay.Job16Full.ordered hq
  · exact CoverJobReplay.Job17Full.ordered hq
  · exact CoverJobReplay.Job18Full.ordered hq
  · exact CoverJobReplay.Job19Full.ordered hq
  · exact CoverJobReplay.Job20Full.ordered hq
  · exact CoverJobReplay.Job21Full.ordered hq
  · exact CoverJobReplay.Job22Full.ordered hq
  · exact CoverJobReplay.Job23Full.ordered hq
  · exact CoverJobReplay.Job24Full.ordered hq
  · exact CoverJobReplay.Job25Full.ordered hq
  · exact CoverJobReplay.Job26Full.ordered hq
  · exact CoverJobReplay.Job27Full.ordered hq
  · exact CoverJobReplay.Job28Full.ordered hq
  · exact CoverJobReplay.Job29Full.ordered hq
  · exact CoverJobReplay.Job30Full.ordered hq
  · exact CoverJobReplay.Job31Full.ordered hq
  · exact CoverJobReplay.Job32Full.ordered hq
  · exact CoverJobReplay.Job33Full.ordered hq
  · exact CoverJobReplay.Job34Full.ordered hq
  · exact CoverJobReplay.Job35Full.ordered hq

theorem all_apex : ApexJobResults := by
  intro i q hq
  fin_cases i
  · exact ApexReplay.F1.ordered hq
  · exact ApexReplay.F2.ordered hq
  · exact ApexReplay.F3.ordered hq
  · exact ApexReplay.F4.ordered hq
  · exact ApexReplay.F5.ordered hq
  · exact ApexReplay.F6.ordered hq

theorem full_abb : FamilyABBLocal := by
  intro z hz hL q hq
  exact FamilyABBReplay.Full.local_nonnegative_and_unique_zero hz hL hq

/-- Literal Appendix A.3 ABB Hessian at the exact binary64 radius. -/
theorem full_abb_binary64_hessian {z : ℝ} (hz : 0<z)
    (hL : Numerics.Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z)
      ManuscriptFamilyRadius.binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  FamilyABBRadiusReplay.Full.hessian_positive hz hL hq hv

theorem full_abb_binary64_local {z : ℝ} (hz : 0<z)
    (hL : Numerics.Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z)
      ManuscriptFamilyRadius.binary64Radius) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) :=
  FamilyABBRadiusReplay.Full.local_nonnegative_and_unique_zero hz hL hq

theorem full_compact : CompactFamilyCertificate :=
  FamilyExteriorReplay.Full.compact_certificate full_abb

/-- All internal finite certificate obligations discharged. The seven named
external/classical inputs remain explicit, as in the existing assumptions ledger. -/
theorem mainTheorem
    (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting) : MainTheorem :=
  mainTheorem_of_finite_certificates external hSampling hSpectral hdyadic hcompact hpull hcount
    (criticalClassification_of_ordered_jobs hdyadic hcompact hcount hSampling all_nonapex all_apex)
    full_compact
end SparseLowerTail.CompletedReplays

import SparseLowerTail.Section05.CheckedCoverJobs
import SparseLowerTail.Section08.FamilyCompactAssembly

/-! The main theorem with the unfinished numerical replays exposed directly.
The completed critical regions and the AAA neighborhood are supplied by proved
imports. None of the four numerical inputs below is an external assumption.
The names remain stable when more completed regions enter CheckedCoverJobs. -/

noncomputable section
namespace SparseLowerTail
open Section02 Section04 Section05 Section07 Section08 Certificate

/-- Direct assembly from the outstanding replay results. The first seven inputs
are the permitted external/classical statements. The last four are still
internal proof obligations: remaining nonapex regions, the six apex fans,
the ABB neighborhood, and the full compact exterior replay. -/
theorem mainTheorem_of_remaining_replays
    (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hn : RemainingNonapexJobResults) (ha : ApexJobResults)
    (hABB : FamilyABBLocal)
    (hExterior : FamilyABBLocal → CompactFamilyCertificate) : MainTheorem :=
  mainTheorem_of_finite_certificates external hSampling hSpectral
    hdyadic hcompact hpull hcount
    (criticalClassification_of_remaining_ordered_jobs hdyadic hcompact hcount hSampling hn ha)
    (hExterior hABB)

end SparseLowerTail

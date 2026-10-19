import SparseLowerTail.Section05.CoverJobsAssembly
import SparseLowerTail.Section05.CoverJobReplay.Job25Full.Ordered

/-! Complete checked regions used by the critical-cover assembly.
This module records whole domains only. Remaining jobs are internal obligations,
not external or classical assumptions. Add each completed replay here so the
remaining-obligation interface and its consumers keep stable names. -/

noncomputable section
namespace SparseLowerTail.Section05
open Section02 Section04 CoverGeometry

/-- Nonapex regions with complete imported kernel proofs. -/
def checkedNonapexJobs : Finset (Fin 36) := {25}

theorem checkedNonapexJobs_positive {j : Fin 36} (hj : j ∈ checkedNonapexJobs) :
    ∀ q ∈ orderedLogDomain (cellQ (nonapexCell j)),
      0 < logCertificate (coverCellTheta (nonapexCell j))
        (cellLambda (nonapexCell j)) (nonapexVertex j) q := by
  have he : j = 25 := by simpa [checkedNonapexJobs] using hj
  subst j
  exact fun _ hq => CoverJobReplay.Job25Full.ordered hq

/-- The corresponding original certificate is positive on the entire edge cube. -/
theorem checkedNonapexJobs_cube_positive {j : Fin 36} (hj : j ∈ checkedNonapexJobs) :
    ∀ u ∈ edgeCube (Real.exp (-cellQ (nonapexCell j))),
      0 < coverCertificate (coverCellTheta (nonapexCell j))
        (cellLambda (nonapexCell j)) u (nonapexVertex j) :=
  coverCertificate_pos_of_orderedLog _ _ _ _ (checkedNonapexJobs_positive hj)

/-- Exactly the nonapex obligations not yet discharged by imported full proofs. -/
def RemainingNonapexJobResults : Prop := ∀ j : Fin 36, j ∉ checkedNonapexJobs →
  ∀ q ∈ orderedLogDomain (cellQ (nonapexCell j)),
    0 < logCertificate (coverCellTheta (nonapexCell j))
      (cellLambda (nonapexCell j)) (nonapexVertex j) q

theorem nonapexJobResults_of_remaining (h : RemainingNonapexJobResults) :
    NonapexJobResults := by
  intro j
  by_cases hj : j ∈ checkedNonapexJobs
  · exact checkedNonapexJobs_positive hj
  · exact h j hj

/-- The critical theorem now requires only the unfinished nonapex regions,
along with the six complete apex results and the named classical inputs. -/
theorem criticalClassification_of_remaining_ordered_jobs
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hcount : ClassicalTriangleCounting) (hSampling : UniformSampling)
    (hn : RemainingNonapexJobResults) (ha : ApexJobResults) : CriticalClassification :=
  criticalClassification_of_ordered_jobs hdyadic hcompact hcount hSampling
    (nonapexJobResults_of_remaining hn) ha

end SparseLowerTail.Section05

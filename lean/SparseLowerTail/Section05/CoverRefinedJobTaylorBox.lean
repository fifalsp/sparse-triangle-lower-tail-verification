import SparseLowerTail.Section05.CoverRefinedJobIntervals
import SparseLowerTail.Section05.CoverS1TaylorBox

/-! Reuse the endpoint and box geometry data for every nonapex cover job.
Only the constants change between jobs; the symbolic derivatives are shared. -/
namespace SparseLowerTail.Section05.RefinedCover
open Numerics Certificate Set
namespace S1TaylorBoxData

def jobStartBox (D : S1TaylorBoxData) : ApexFanBox := ⟨D.centerExp,D.centerExp⟩
def jobWholeBox (D : S1TaylorBoxData) : ApexFanBox := ⟨D.lowerExp,D.upperExp⟩
def jobVelocity (D : S1TaylorBoxData) : Fin 3 → DyadicInterval :=
  fun i => DyadicInterval.ofRational (D.velocity i)
def jobMargin (D : S1TaylorBoxData) (j : Fin 36) : ℤ :=
  dyadicFactoredTaylorMargin apexCertificateExpr coverGradientExpr coverHessianExpr
    (nonapexBoxIntervals (jobStartBox D) j) (nonapexBoxIntervals (jobWholeBox D) j) (jobVelocity D)

/-- Positivity over an arbitrary closed leaf for any of the 36 actual jobs.
The historical S1 data type here contains only reusable geometry/endpoints. -/
theorem job_positive (D : S1TaylorBoxData) (j : Fin 36)
    (hl : ∀i,(D.lowerExp i).Valid) (hu : ∀i,(D.upperExp i).Valid)
    (hc : ∀i,(D.centerExp i).Valid)
    (hql : ∀i,(D.lowerExp i).q=D.box.lower i)
    (hqu : ∀i,(D.upperExp i).q=D.box.upper i)
    (hqc : ∀i,(D.centerExp i).q=D.box.centerCoordinate i)
    (hm : 0<(jobMargin D) j) {q : EdgeTriple} (hq : q∈D.box.region) :
    0<logCertificate (coverCellTheta (CoverGeometry.nonapexCell j))
      (CoverGeometry.cellLambda (CoverGeometry.nonapexCell j)) (CoverGeometry.nonapexVertex j) q := by
  let p : ApexVector := fun i => (D.box.centerCoordinate i : ℝ)
  let v : ApexVector := edgeCoordinate (D.box.displacement q)
  have hs : ∀k,(nonapexBoxIntervals (jobStartBox D) j k).contains
      (coverVariables (coverCellTheta (CoverGeometry.nonapexCell j))
        (CoverGeometry.cellLambda (CoverGeometry.nonapexCell j)) (CoverGeometry.nonapexVertex j)
        (familySegment p v 0) k) := by
    rw [familySegment_zero]
    apply nonapexBoxIntervals_contains (jobStartBox D) ⟨hc,hc⟩ j
    intro i
    change Bounds (D.box.centerCoordinate i : ℝ) ((D.centerExp i).q : ℝ) ((D.centerExp i).q : ℝ)
    rw [hqc]
    exact ⟨le_rfl,le_rfl⟩
  have hw : ∀s∈Icc (0:ℝ) 1,∀k,(nonapexBoxIntervals (jobWholeBox D) j k).contains
      (coverVariables (coverCellTheta (CoverGeometry.nonapexCell j))
        (CoverGeometry.cellLambda (CoverGeometry.nonapexCell j)) (CoverGeometry.nonapexVertex j)
        (familySegment p v s) k) := by
    intro s hs
    apply nonapexBoxIntervals_contains (jobWholeBox D) ⟨hl,hu⟩ j
    intro i
    change Bounds (p i+s*v i) ((D.lowerExp i).q : ℝ) ((D.upperExp i).q : ℝ)
    rw [hql,hqu]
    simpa only [edgeCoordinate_line,LogBox.coordinate_center] using (D.box.segment_mem hq hs i)
  have hv : ∀i,((jobVelocity D) i).contains (v i) := by
    intro i
    exact DyadicInterval.ofRational_contains (D.velocity_contains hq i)
  have H := cover_factored_taylor_positive
    (coverCellTheta (CoverGeometry.nonapexCell j))
    (CoverGeometry.cellLambda (CoverGeometry.nonapexCell j)) (CoverGeometry.nonapexVertex j)
    coverGradientExpr coverHessianExpr coverGradientExpr_correct coverHessianExpr_correct
    p v _ _ (jobVelocity D) hv hs hw hm
  have he : familySegment p v 1=edgeCoordinate q := by
    funext i
    change (D.box.centerCoordinate i : ℝ)+1*edgeCoordinate (D.box.displacement q) i=edgeCoordinate q i
    rw [LogBox.coordinate_displacement]
    ring
  rw [he] at H
  exact H

end S1TaylorBoxData
end SparseLowerTail.Section05.RefinedCover

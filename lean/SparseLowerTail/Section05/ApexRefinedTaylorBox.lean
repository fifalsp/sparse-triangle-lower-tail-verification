import SparseLowerTail.Section05.ApexRefinedBoxIntervals
import SparseLowerTail.Section05.CoverJobTaylorBox

namespace SparseLowerTail.Section05
open Numerics Certificate Set
namespace S1TaylorBoxData

def apexRefinedMargin (D : S1TaylorBoxData) (j : Fin 6) : ℤ :=
  dyadicFactoredTaylorMargin apexCertificateExpr coverGradientExpr coverHessianExpr
    (apexRefinedBoxIntervals D.jobStartBox j) (apexRefinedBoxIntervals D.jobWholeBox j) D.jobVelocity

/-- Positivity over an arbitrary closed exterior leaf for an actual apex fan,
using the refined constants and solved-coefficient bounds. -/
theorem apexRefined_positive (D : S1TaylorBoxData) (j : Fin 6)
    (hl : ∀i,(D.lowerExp i).Valid) (hu : ∀i,(D.upperExp i).Valid)
    (hc : ∀i,(D.centerExp i).Valid)
    (hql : ∀i,(D.lowerExp i).q=D.box.lower i)
    (hqu : ∀i,(D.upperExp i).q=D.box.upper i)
    (hqc : ∀i,(D.centerExp i).q=D.box.centerCoordinate i)
    (hm : 0<D.apexRefinedMargin j) {q : EdgeTriple} (hq : q∈D.box.region) :
    0<logCertificate (apexFanTheta j)
      (CoverGeometry.cellLambda (j.castAdd 6)) criticalPoint q := by
  let p : ApexVector := fun i => (D.box.centerCoordinate i : ℝ)
  let v : ApexVector := edgeCoordinate (D.box.displacement q)
  have hs : ∀k,(apexRefinedBoxIntervals D.jobStartBox j k).contains
      (coverVariables (apexFanTheta j)
        (CoverGeometry.cellLambda (j.castAdd 6)) criticalPoint
        (familySegment p v 0) k) := by
    rw [familySegment_zero]
    apply apexRefinedBoxIntervals_contains D.jobStartBox ⟨hc,hc⟩ j
    intro i
    change Bounds (D.box.centerCoordinate i : ℝ) ((D.centerExp i).q : ℝ) ((D.centerExp i).q : ℝ)
    rw [hqc]
    exact ⟨le_rfl,le_rfl⟩
  have hw : ∀s∈Icc (0:ℝ) 1,∀k,(apexRefinedBoxIntervals D.jobWholeBox j k).contains
      (coverVariables (apexFanTheta j)
        (CoverGeometry.cellLambda (j.castAdd 6)) criticalPoint
        (familySegment p v s) k) := by
    intro s hs
    apply apexRefinedBoxIntervals_contains D.jobWholeBox ⟨hl,hu⟩ j
    intro i
    change Bounds (p i+s*v i) ((D.lowerExp i).q : ℝ) ((D.upperExp i).q : ℝ)
    rw [hql,hqu]
    simpa only [edgeCoordinate_line,LogBox.coordinate_center] using (D.box.segment_mem hq hs i)
  have hv : ∀i,(D.jobVelocity i).contains (v i) := by
    intro i
    exact DyadicInterval.ofRational_contains (D.velocity_contains hq i)
  have H := cover_factored_taylor_positive
    (apexFanTheta j)
    (CoverGeometry.cellLambda (j.castAdd 6)) criticalPoint
    coverGradientExpr coverHessianExpr coverGradientExpr_correct coverHessianExpr_correct
    p v _ _ D.jobVelocity hv hs hw hm
  have he : familySegment p v 1=edgeCoordinate q := by
    funext i
    change (D.box.centerCoordinate i : ℝ)+1*edgeCoordinate (D.box.displacement q) i=edgeCoordinate q i
    rw [LogBox.coordinate_displacement]
    ring
  rw [he] at H
  exact H

end S1TaylorBoxData
end SparseLowerTail.Section05

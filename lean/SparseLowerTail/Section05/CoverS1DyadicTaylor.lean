import SparseLowerTail.Section05.CoverS1TaylorBox
import SparseLowerTail.Numerics.DyadicTaylorAxes

/-! Fixed-precision Taylor boxes for the exact S1 certificate. Rounding is
outward and proved sound; the last numerical check uses only integers. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr Set
namespace S1TaylorBoxData

def dyadicStart (D : S1TaylorBoxData) : Fin 9 → DyadicInterval :=
  fun i => .ofRational (D.start i)
def dyadicWhole (D : S1TaylorBoxData) : Fin 9 → DyadicInterval :=
  fun i => .ofRational (D.whole i)
def dyadicVelocity (D : S1TaylorBoxData) : Fin 3 → DyadicInterval :=
  fun i => .ofRational (D.velocity i)
def dyadicMargin (D : S1TaylorBoxData) : ℤ :=
  dyadicTaylorMargin s1CertificateExpr s1PartialDirections D.dyadicStart D.dyadicWhole D.dyadicVelocity

theorem dyadic_positive (D : S1TaylorBoxData)
    (hl : ∀ i, (D.lowerExp i).Valid) (hu : ∀ i, (D.upperExp i).Valid)
    (hc : ∀ i, (D.centerExp i).Valid)
    (hql : ∀ i, (D.lowerExp i).q = D.box.lower i)
    (hqu : ∀ i, (D.upperExp i).q = D.box.upper i)
    (hqc : ∀ i, (D.centerExp i).q = D.box.centerCoordinate i)
    (hm : 0 < D.dyadicMargin) {q : EdgeTriple} (hq : q ∈ D.box.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  have h := dyadic_taylor_axes_positive s1CertificateExpr s1PartialDirections
    (edgeCoordinate (D.box.displacement q))
    (fun s => s1Environment (s1LinePoint D.box.center (D.box.displacement q) s))
    D.dyadicStart D.dyadicWhole D.dyadicVelocity
    (fun i => DyadicInterval.ofRational_contains (D.velocity_contains hq i))
    (fun s _ i => s1PartialEnvironment_hasDerivAt D.box.center (D.box.displacement q) s i)
    (fun i => DyadicInterval.ofRational_contains (D.start_contains q hc hqc i))
    (fun s hs i => DyadicInterval.ofRational_contains (D.whole_contains hq hl hu hql hqu s hs i)) hm
  rw [s1CertificateExpr_realEval] at h
  change 0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0
    (edgeLine D.box.center (D.box.displacement q) 1) at h
  simpa only [D.box.segment_one] using h

end S1TaylorBoxData
end SparseLowerTail.Section05

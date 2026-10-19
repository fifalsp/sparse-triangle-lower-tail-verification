import SparseLowerTail.Section05.CoverS1TaylorAxes
import SparseLowerTail.Section05.CoverS1Environment
import SparseLowerTail.Section05.BoxSegments
import SparseLowerTail.Numerics.ExpEndpoints

/-! Compact proof-producing Taylor box data. Endpoint enclosures may be shared
between arbitrarily many boxes. A rational margin check is the only remaining
leaf-specific numerical calculation. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr Set

structure S1TaylorBoxData where
  box : LogBox
  lowerExp : Fin 3 → ExpEndpointCertificate
  upperExp : Fin 3 → ExpEndpointCertificate
  centerExp : Fin 3 → ExpEndpointCertificate

namespace S1TaylorBoxData

def start (D : S1TaylorBoxData) : Fin 9 → RationalInterval :=
  s1BoxEnvironment (fun i => .point (D.box.centerCoordinate i))
    (fun i => ⟨(D.centerExp i).lower,(D.centerExp i).upper⟩)

def whole (D : S1TaylorBoxData) : Fin 9 → RationalInterval :=
  s1BoxEnvironment (fun i => ⟨D.box.lower i,D.box.upper i⟩)
    (fun i => ⟨(D.upperExp i).lower,(D.lowerExp i).upper⟩)

def velocity (D : S1TaylorBoxData) : Fin 3 → RationalInterval :=
  fun i => ⟨-D.box.radius i,D.box.radius i⟩

def margin (D : S1TaylorBoxData) : ℚ :=
  (s1CertificateExpr.intervalEval D.start).lower+
  (gradientInterval s1CertificateExpr s1PartialDirections D.start D.velocity).lower+
  (hessianInterval s1CertificateExpr s1PartialDirections D.whole D.velocity).lower/2

theorem start_contains (D : S1TaylorBoxData) (q : EdgeTriple)
    (hc : ∀ i, (D.centerExp i).Valid)
    (hqc : ∀ i, (D.centerExp i).q = D.box.centerCoordinate i) :
    ∀ i, (D.start i).contains
      (s1Environment (s1LinePoint D.box.center (D.box.displacement q) 0) i) := by
  change ∀ i, (D.start i).contains
    (s1Environment (edgeLine D.box.center (D.box.displacement q) 0) i)
  rw [edgeLine_zero]
  apply s1BoxEnvironment_contains
  · intro i
    rw [D.box.coordinate_center]
    exact RationalInterval.point_contains _
  · intro i
    rw [D.box.coordinate_center]
    have h := (D.centerExp i).bounds (hc i)
    rw [hqc i] at h
    exact h

theorem whole_contains (D : S1TaylorBoxData) {q : EdgeTriple} (hq : q ∈ D.box.region)
    (hl : ∀ i, (D.lowerExp i).Valid) (hu : ∀ i, (D.upperExp i).Valid)
    (hql : ∀ i, (D.lowerExp i).q = D.box.lower i)
    (hqu : ∀ i, (D.upperExp i).q = D.box.upper i) :
    ∀ s ∈ Icc (0:ℝ) 1, ∀ i, (D.whole i).contains
      (s1Environment (s1LinePoint D.box.center (D.box.displacement q) s) i) := by
  intro s hs
  change ∀ i, (D.whole i).contains
    (s1Environment (edgeLine D.box.center (D.box.displacement q) s) i)
  have hsbox := D.box.segment_mem hq hs
  apply s1BoxEnvironment_contains
  · exact hsbox
  · intro i
    have hlow := (D.lowerExp i).bounds (hl i)
    have hupp := (D.upperExp i).bounds (hu i)
    rw [hql i] at hlow
    rw [hqu i] at hupp
    exact exp_neg_bounds_on_interval (hsbox i) hlow.2 hupp.1

theorem velocity_contains (D : S1TaylorBoxData) {q : EdgeTriple} (hq : q ∈ D.box.region) :
    ∀ i, (D.velocity i).contains (edgeCoordinate (D.box.displacement q) i) := by
  intro i
  simpa only [velocity,RationalInterval.contains,Rat.cast_neg] using D.box.displacement_bounds hq i

/-- Complete positivity on a closed box, including its boundary. Endpoint
validity and the final rational inequality are ordinary kernel proof arguments. -/
theorem positive (D : S1TaylorBoxData)
    (hl : ∀ i, (D.lowerExp i).Valid) (hu : ∀ i, (D.upperExp i).Valid)
    (hc : ∀ i, (D.centerExp i).Valid)
    (hql : ∀ i, (D.lowerExp i).q = D.box.lower i)
    (hqu : ∀ i, (D.upperExp i).q = D.box.upper i)
    (hqc : ∀ i, (D.centerExp i).q = D.box.centerCoordinate i)
    {L : ℚ} (hm : L < D.margin) {q : EdgeTriple} (hq : q ∈ D.box.region) :
    (L : ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  have hstart := D.start_contains q hc hqc
  have hwhole := D.whole_contains hq hl hu hql hqu
  have hv := D.velocity_contains hq
  have h := coverS1_taylor_axes_positive D.box.center (D.box.displacement q)
    D.start D.whole D.velocity hv hstart hwhole hm
  change (L : ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0
    (edgeLine D.box.center (D.box.displacement q) 1) at h
  simpa only [D.box.segment_one] using h

end S1TaylorBoxData
end SparseLowerTail.Section05

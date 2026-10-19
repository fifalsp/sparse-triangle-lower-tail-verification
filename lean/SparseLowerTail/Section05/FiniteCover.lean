import SparseLowerTail.Section05.CoverSymmetry
import SparseLowerTail.Section05.CertificateConcavity
import Mathlib.Analysis.Convex.Combination

/-!
# From finite cell certificates to exclusion of noncritical parameters

Stable manuscript anchors: `prop:cover`, `cor:cover`.
This module proves the mathematical bridge from explicitly stated finite-data
verification conditions to the corollary. It does not assert that the numerical
cell data satisfy those conditions; that remains a separate certificate obligation.
-/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section05

/-- The exceptional apex in the parameter plane. -/
def criticalPoint : ℝ × ℝ := (criticalMean,criticalCost)

/-- Exact finite cell data; coordinate lower bounds may be conservative. -/
structure CertificateCell where
  vertices : Finset (ℝ × ℝ)
  theta : Fin 12 → ℝ
  lam : ℝ
  Q : ℝ
  meanLower : ℝ
  costLower : ℝ

def CertificateCell.region (K : CertificateCell) : Set (ℝ × ℝ) :=
  convexHull ℝ (K.vertices : Set (ℝ × ℝ))

/-- The cellwise content of `prop:cover` needed for exclusion. These are proof
obligations about the actual certificate, not boolean verifier status flags. -/
structure VerifiedCertificateCell (K : CertificateCell) : Prop where
  lam_nonneg : 0 ≤ K.lam
  meanLower_pos : 0 < K.meanLower
  costLower_lt_one : K.costLower < 1
  meanLower_le : ∀ v ∈ K.vertices, K.meanLower ≤ v.1
  costLower_le : ∀ v ∈ K.vertices, K.costLower ≤ v.2
  exponent_le : supportExponent criticalTriangle K.meanLower K.costLower ≤ K.Q
  vertex_pos : ∀ v ∈ K.vertices, v ≠ criticalPoint →
    ∀ u ∈ edgeCube (Real.exp (-K.Q)), 0 < coverCertificate K.theta K.lam u v
  apex_nonneg : criticalPoint ∈ K.vertices →
    ∀ u ∈ edgeCube (Real.exp (-K.Q)), 0 ≤ coverCertificate K.theta K.lam u criticalPoint

/-- Coordinate lower bounds extend from vertices to their convex hull. -/
theorem CertificateCell.coordinate_bounds (K : CertificateCell) (hK : VerifiedCertificateCell K)
    {π : ℝ × ℝ} (hπ : π ∈ K.region) : K.meanLower ≤ π.1 ∧ K.costLower ≤ π.2 := by
  obtain ⟨ι,hi,w,v,hw,hsum,hv,hrep⟩ := mem_convexHull_iff_exists_fintype.mp hπ
  letI := hi
  have hfirst : (∑ i, w i*(v i).1) = π.1 := by simpa [Prod.fst_sum] using congrArg Prod.fst hrep
  have hsecond : (∑ i, w i*(v i).2) = π.2 := by simpa [Prod.snd_sum] using congrArg Prod.snd hrep
  constructor
  · calc
      K.meanLower = (∑ i, w i)*K.meanLower := by rw [hsum]; ring
      _ = ∑ i, w i*K.meanLower := Finset.sum_mul _ _ _
      _ ≤ ∑ i, w i*(v i).1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hK.meanLower_le (v i) (hv i)) (hw i)
      _ = π.1 := hfirst
  · calc
      K.costLower = (∑ i, w i)*K.costLower := by rw [hsum]; ring
      _ = ∑ i, w i*K.costLower := Finset.sum_mul _ _ _
      _ ≤ ∑ i, w i*(v i).2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hK.costLower_le (v i) (hv i)) (hw i)
      _ = π.2 := hsecond

/-- The cell's verified exponential cutoff is valid throughout K∩Ω. -/
theorem VerifiedCertificateCell.support_lower {K : CertificateCell} (hK : VerifiedCertificateCell K)
    {π : ℝ × ℝ} (hπK : π ∈ K.region) (hπΩ : π ∈ criticalRegion) :
    Real.exp (-K.Q) ≤ supportLambda criticalTriangle π.1 π.2 := by
  have hb := K.coordinate_bounds hK hπK
  have ht : 0 < criticalTriangle := pow_pos Section04.threshold_mem_Ioo.1 3
  have hcost : π.2 ≤ 1 := hπΩ.2.2.trans (criticalCost_lt.le.trans (by norm_num))
  have hmono := supportLambda_mono ht hK.meanLower_pos.le hb.1 hb.2 hcost
  exact (Real.exp_le_exp.mpr (neg_le_neg hK.exponent_le)).trans hmono

/-- A convex combination distinct from its exceptional point puts positive weight elsewhere. -/
theorem exists_positive_weight_off_point {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (v : ι → ℝ × ℝ) (a : ℝ × ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hne : (∑ i, w i • v i) ≠ a) : ∃ i, 0 < w i ∧ v i ≠ a := by
  classical
  by_contra hn
  push_neg at hn
  have he : ∀ i, w i • v i = w i • a := by
    intro i
    by_cases hz : w i = 0
    · simp [hz]
    · rw [hn i (lt_of_le_of_ne (hw i) (Ne.symm hz))]
  apply hne
  calc
    _ = ∑ i, w i • a := Finset.sum_congr rfl fun i _ => he i
    _ = (∑ i, w i) • a := Finset.sum_smul.symm
    _ = a := by rw [hsum]; simp

/-- Concavity upgrades vertex checks to strict positivity everywhere off the apex. -/
theorem VerifiedCertificateCell.certificate_pos {K : CertificateCell} (hK : VerifiedCertificateCell K)
    {π : ℝ × ℝ} (hπK : π ∈ K.region) (hne : π ≠ criticalPoint)
    {u : EdgeTriple} (hu : u ∈ edgeCube (Real.exp (-K.Q))) :
    0 < coverCertificate K.theta K.lam u π := by
  obtain ⟨ι,hi,w,v,hw,hsum,hv,hrep⟩ := mem_convexHull_iff_exists_fintype.mp hπK
  letI := hi
  have hoff : (∑ i, w i • v i) ≠ criticalPoint := by rwa [hrep]
  obtain ⟨j,hj,hvj⟩ := exists_positive_weight_off_point w v criticalPoint hw hsum hoff
  have hnonneg : ∀ i, 0 ≤ w i*coverCertificate K.theta K.lam u (v i) := by
    intro i
    apply mul_nonneg (hw i)
    by_cases he : v i = criticalPoint
    · rw [he]
      exact hK.apex_nonneg (he ▸ hv i) u hu
    · exact (hK.vertex_pos (v i) (hv i) he u hu).le
  have hpos : 0 < ∑ i, w i*coverCertificate K.theta K.lam u (v i) := by
    apply Finset.sum_pos' (fun i _ => hnonneg i)
    exact ⟨j,Finset.mem_univ _,mul_pos hj (hK.vertex_pos (v j) (hv j) hvj u hu)⟩
  have hjensen := coverCertificate_le_map_sum Finset.univ K.theta hK.lam_nonneg u w v
    (fun i _ => hw i) hsum
  rw [hrep] at hjensen
  exact hpos.trans_le hjensen

/-- A verified cell excludes every non-apex parameter in K∩Ω. -/
theorem VerifiedCertificateCell.no_relaxedLaw {K : CertificateCell} (hK : VerifiedCertificateCell K)
    {π : ℝ × ℝ} (hπK : π ∈ K.region) (hπΩ : π ∈ criticalRegion) (hne : π ≠ criticalPoint) :
    ¬∃ ν : Measure EdgeTriple, RelaxedLaw π ν :=
  no_relaxedLaw_of_certificate_pos K.theta hK.lam_nonneg (hK.support_lower hπK hπΩ)
    (fun _ hu => hK.certificate_pos hπK hne hu)

/-- The finite cover assumptions are retained explicitly until each numerical
and geometric certificate has been checked in Lean. -/
structure VerifiedCertificateCover {ι : Type*} [Fintype ι] (cells : ι → CertificateCell) : Prop where
  cells_verified : ∀ i, VerifiedCertificateCell (cells i)
  covers : ∀ π ∈ criticalRegion, ∃ i, π ∈ (cells i).region

/-- Full `cor:cover`, conditional precisely on the stated finite cover verification. -/
theorem VerifiedCertificateCover.no_relaxedLaw {ι : Type*} [Fintype ι]
    {cells : ι → CertificateCell} (hcover : VerifiedCertificateCover cells)
    {π : ℝ × ℝ} (hπ : π ∈ criticalRegion) (hne : π ≠ criticalPoint) :
    ¬∃ ν : Measure EdgeTriple, RelaxedLaw π ν := by
  obtain ⟨i,hi⟩ := hcover.covers π hπ
  exact (hcover.cells_verified i).no_relaxedLaw hi hπ hne

/-- Any feasible relaxed parameter in Ω must be the exact critical point. -/
theorem VerifiedCertificateCover.eq_criticalPoint {ι : Type*} [Fintype ι]
    {cells : ι → CertificateCell} (hcover : VerifiedCertificateCover cells)
    {π : ℝ × ℝ} (hπ : π ∈ criticalRegion) {ν : Measure EdgeTriple} (hν : RelaxedLaw π ν) :
    π = criticalPoint := by
  by_contra hne
  exact hcover.no_relaxedLaw hπ hne ⟨ν,hν⟩

end SparseLowerTail.Section05

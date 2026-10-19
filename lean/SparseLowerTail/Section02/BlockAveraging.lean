import SparseLowerTail.Section02.BlockEntropy
import Mathlib.MeasureTheory.Function.Floor

/-! Actual finite block averaging of graphons and the dyadic averaging operator. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- A finite measurable coloring of the vertex space defines a partition. -/
structure VertexPartition (n : ℕ) where
  color : ℝ → Fin n
  measurable : Measurable color

def VertexPartition.fiber {n : ℕ} (P : VertexPartition n) (i : Fin n) : Set ℝ := P.color ⁻¹' {i}

theorem VertexPartition.measurable_fiber {n : ℕ} (P : VertexPartition n) (i : Fin n) :
    MeasurableSet (P.fiber i) := P.measurable (measurableSet_singleton i)

def VertexPartition.rectangles {n : ℕ} (P : VertexPartition n) : RectangleFamily (Fin n × Fin n) where
  left i := P.fiber i.1
  right i := P.fiber i.2
  measurable_left i := P.measurable_fiber i.1
  measurable_right i := P.measurable_fiber i.2
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hp hq
    apply hij
    exact Prod.ext (hp.1.symm.trans hq.1) (hp.2.symm.trans hq.2)

/-- The finite cell-average operator, defined for any real kernel. -/
def blockAverage {n : ℕ} (P : VertexPartition n) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (squareMeasure.real (P.fiber (P.color p.1) ×ˢ P.fiber (P.color p.2)))⁻¹ *
    rectangleIntegral f (P.fiber (P.color p.1)) (P.fiber (P.color p.2))

theorem rectangleMean_mem_Icc (U : Graphon) (S T : Set ℝ) : rectangleMean U S T ∈ Icc (0:ℝ) 1 := by
  have hi : 0 ≤ rectangleIntegral U.toFun S T :=
    integral_nonneg_of_ae (ae_restrict_of_ae (U.bounded.mono fun _ hp => hp.1))
  have hu : rectangleIntegral U.toFun S T ≤ squareMeasure.real (S ×ˢ T) := by
    have h := integral_mono_ae (μ := squareMeasure.restrict (S ×ˢ T)) (graphon_integrable U).integrableOn (integrable_const (1:ℝ))
      (ae_restrict_of_ae (U.bounded.mono fun _ hp => hp.2))
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using h
  have hw := measureReal_nonneg (μ := squareMeasure) (s := S ×ˢ T)
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hw) hi
  · by_cases hz : squareMeasure.real (S ×ˢ T)=0
    · simp [rectangleMean,hz]
    · have hp : 0 < squareMeasure.real (S ×ˢ T) := lt_of_le_of_ne hw (Ne.symm hz)
      unfold rectangleMean
      rw [← div_eq_inv_mul]
      exact (div_le_one hp).mpr hu

theorem rectangleMean_swap (U : Graphon) (S T : Set ℝ) : rectangleMean U S T=rectangleMean U T S := by
  have hi : rectangleIntegral U.toFun S T=rectangleIntegral U.toFun T S := by
    calc
      _ = ∫ p in T ×ˢ S, U p.swap ∂squareMeasure := (setIntegral_prod_swap S T U.toFun).symm
      _ = _ := integral_congr_ae (ae_restrict_of_ae U.symmetric)
  have hw : squareMeasure.real (S ×ˢ T)=squareMeasure.real (T ×ˢ S) := by
    simp only [measureReal_def, Measure.prod_prod, mul_comm]
  unfold rectangleMean
  rw [hi,hw]

/-- The averaged graphon on a finite vertex partition. -/
def averagedGraphon {n : ℕ} (P : VertexPartition n) (U : Graphon) : Graphon where
  toFun := blockAverage P U.toFun
  measurable := by
    let f : Fin n × Fin n → ℝ := fun i => rectangleMean U (P.fiber i.1) (P.fiber i.2)
    have hf : Measurable f := measurable_of_countable f
    exact (hf.comp ((P.measurable.comp measurable_fst).prodMk (P.measurable.comp measurable_snd))).aemeasurable
  symmetric := Filter.Eventually.of_forall fun p => rectangleMean_swap U _ _
  bounded := Filter.Eventually.of_forall fun p => rectangleMean_mem_Icc U _ _

theorem averagedGraphon_on_cell {n : ℕ} (P : VertexPartition n) (U : Graphon)
    (i : Fin n × Fin n) {p : ℝ × ℝ} (hp : p ∈ P.fiber i.1 ×ˢ P.fiber i.2) :
    averagedGraphon P U p=rectangleMean U (P.fiber i.1) (P.fiber i.2) := by
  change P.color p.1=i.1 ∧ P.color p.2=i.2 at hp
  change rectangleMean U (P.fiber (P.color p.1)) (P.fiber (P.color p.2)) = _
  rw [hp.1,hp.2]

/-- The entropy integral of the genuine averaged graphon is the finite block sum. -/
theorem cost_averagedGraphon {n : ℕ} (P : VertexPartition n) (U : Graphon) :
    cost (averagedGraphon P U)=blockEntropy P.rectangles U := by
  classical
  have hcover : (⋃ i : Fin n × Fin n, P.fiber i.1 ×ˢ P.fiber i.2) = univ := by
    ext p
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨(P.color p.1,P.color p.2),rfl,rfl⟩
  have hi := integral_iUnion_fintype
    (fun i : Fin n × Fin n => (P.measurable_fiber i.1).prod (P.measurable_fiber i.2))
    P.rectangles.disjoint (fun _ => (cost_integrable (averagedGraphon P U)).integrableOn)
  rw [hcover, setIntegral_univ] at hi
  change cost (averagedGraphon P U) = _ at hi
  rw [hi]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∫ p in P.fiber i.1 ×ˢ P.fiber i.2, entropy (averagedGraphon P U p) ∂squareMeasure) =
      ∫ _ in P.fiber i.1 ×ˢ P.fiber i.2, entropy (rectangleMean U (P.fiber i.1) (P.fiber i.2)) ∂squareMeasure := by
    apply setIntegral_congr_fun ((P.measurable_fiber i.1).prod (P.measurable_fiber i.2))
    intro p hp
    exact congrArg entropy (averagedGraphon_on_cell P U i hp)
  rw [he]
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  rfl

/-- The Jensen assertion of lem:lsc(a) for every finite vertex partition. -/
theorem cost_averagedGraphon_le {n : ℕ} (P : VertexPartition n) (U : Graphon) :
    cost (averagedGraphon P U) ≤ cost U := by
  rw [cost_averagedGraphon]
  exact blockEntropy_le_cost P.rectangles U

/-- Dyadic coloring, with all exceptional/outside points assigned to the nearest end cell. -/
def dyadicPartition (k : ℕ) : VertexPartition (2^k) where
  color x := ⟨min (Nat.floor ((2:ℝ)^k*x)) (2^k-1), by
    have hpow : 0 < (2:ℕ)^k := by positivity
    exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hpow (by decide))⟩
  measurable := by
    let g : ℕ → Fin (2^k) := fun m => ⟨min m (2^k-1), by
      have hpow : 0 < (2:ℕ)^k := by positivity
      exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hpow (by decide))⟩
    exact (measurable_of_countable g).comp (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

/-- Exact classical dyadic L¹ approximation input, stated solely for integrable kernels.
It contains no entropy, minimizer, cut norm, or optimization conclusion. -/
def ClassicalDyadicL1Approximation : Prop :=
  ∀ f : ℝ × ℝ → ℝ, Integrable f squareMeasure →
    Tendsto (fun k => ∫ p, |blockAverage (dyadicPartition k) f p-f p| ∂squareMeasure) atTop (𝓝 0)

end SparseLowerTail.Section02

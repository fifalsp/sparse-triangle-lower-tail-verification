import SparseLowerTail.Section03.PartitionTests

/-! Exact averaging of bounded vertex tests on equal-mass cells. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

def vertexCellMean {n : ℕ} (P : VertexPartition n) (f : ℝ → ℝ) (i : Fin n) : ℝ :=
  (n:ℝ)*(∫ x in P.fiber i, f x ∂unitMeasure)

def projectedVertexTest {n : ℕ} (P : VertexPartition n) (f : ℝ → ℝ) : ℝ → ℝ :=
  vertexStep P (vertexCellMean P f)

theorem vertexCellMean_abs_le {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ x, |f x|≤1) (i : Fin n) :
    |vertexCellMean P f i|≤1 := by
  have hi := (unitBound_integrable hf hb).integrableOn (s:=P.fiber i)
  have hu := integral_mono_ae hi (integrable_const (1:ℝ))
    (Eventually.of_forall fun x => (abs_le.mp (hb x)).2)
  have hl := integral_mono_ae (integrable_const (-1:ℝ)) hi
    (Eventually.of_forall fun x => (abs_le.mp (hb x)).1)
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,hmass] at hu hl
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hid : (n:ℝ)*(1/(n:ℝ))=1 := by field_simp
  apply abs_le.mpr
  dsimp only [vertexCellMean]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hl hn'.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hu hn'.le
    nlinarith

theorem projectedVertexTest_measurable {n : ℕ} (P : VertexPartition n) (f : ℝ → ℝ) :
    Measurable (projectedVertexTest P f) := vertexStep_measurable P _

theorem projectedVertexTest_abs_le {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ x, |f x|≤1) (x : ℝ) :
    |projectedVertexTest P f x|≤1 := vertexCellMean_abs_le hn P hmass hf hb _

/-- Every cell integral is preserved exactly, without an approximation premise. -/
theorem projectedVertexTest_cell_integral {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (f : ℝ → ℝ) (i : Fin n) :
    (∫ x in P.fiber i, projectedVertexTest P f x ∂unitMeasure)=∫ x in P.fiber i, f x ∂unitMeasure := by
  calc
    _=∫ _ in P.fiber i, vertexCellMean P f i ∂unitMeasure := by
      apply setIntegral_congr_fun (P.measurable_fiber i)
      intro x hx
      change P.color x=i at hx
      simp only [projectedVertexTest,vertexStep,hx]
    _=_ := by
      rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,hmass]
      dsimp only [vertexCellMean]
      have hn' : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
      field_simp

/-- The global mean is preserved by cell averaging. -/
theorem projectedVertexTest_integral {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) {f : ℝ → ℝ} (hf : Integrable f unitMeasure) :
    (∫ x, projectedVertexTest P f x ∂unitMeasure)=∫ x, f x ∂unitMeasure := by
  have hp : Integrable (projectedVertexTest P f) unitMeasure := vertexStep_integrable P _
  rw [integral_vertexPartition P hp,integral_vertexPartition P hf]
  exact Finset.sum_congr rfl (fun i _ => projectedVertexTest_cell_integral hn P hmass f i)

/-- The original test and its projection have the same quadratic correlation with the projection. -/
theorem projectedVertexTest_correlation {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    {f : ℝ → ℝ} (hf : Integrable f unitMeasure) :
    (∫ x, f x*projectedVertexTest P f x ∂unitMeasure)=
      ∫ x, (projectedVertexTest P f x)^2 ∂unitMeasure := by
  have hp : Integrable (projectedVertexTest P f) unitMeasure := vertexStep_integrable P _
  simp only [pow_two]
  change (∫ x, f x*vertexStep P (vertexCellMean P f) x ∂unitMeasure)=
    ∫ x, projectedVertexTest P f x*vertexStep P (vertexCellMean P f) x ∂unitMeasure
  rw [integral_mul_vertexStep P _ hf,integral_mul_vertexStep P _ hp]
  simp_rw [projectedVertexTest_cell_integral hn P hmass]

/-- Two signed matrix tests are unchanged when both tests are replaced by their cell averages. -/
theorem matrixStepKernel_projected_test {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    (M : Fin n → Fin n → ℝ) {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ x, |f x|≤1) :
    (∫ p, f p.1*f p.2*matrixStepKernel P M p ∂squareMeasure)=
      ∫ p, projectedVertexTest P f p.1*projectedVertexTest P f p.2*matrixStepKernel P M p ∂squareMeasure := by
  rw [matrixStepKernel_weighted_integral P M hf hf hb hb,
    matrixStepKernel_weighted_integral P M (projectedVertexTest_measurable P f)
      (projectedVertexTest_measurable P f) (projectedVertexTest_abs_le hn P hmass hf hb)
      (projectedVertexTest_abs_le hn P hmass hf hb)]
  simp_rw [projectedVertexTest_cell_integral hn P hmass]

end SparseLowerTail.Section03

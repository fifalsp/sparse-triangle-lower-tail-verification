import SparseLowerTail.Section03.RankOneTests

/-! Rounding a cell average of a balanced sign function to a vertex partition. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

def partitionSign (S : Set ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x∈S then 1 else -1

theorem partitionSign_measurable {S : Set ℝ} (hS : MeasurableSet S) : Measurable (partitionSign S) := by
  classical
  exact Measurable.ite hS measurable_const measurable_const

theorem partitionSign_abs (S : Set ℝ) (x : ℝ) : |partitionSign S x|=1 := by
  classical
  by_cases hx : x∈S <;> norm_num [partitionSign,hx]

theorem partitionSign_integral {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ x, partitionSign S x ∂unitMeasure)=2*unitMeasure.real S-1 := by
  classical
  have he : partitionSign S=(fun x => 2*S.indicator (fun _ => (1:ℝ)) x-1) := by
    funext x; by_cases hx : x∈S <;> norm_num [partitionSign,hx]
  rw [he,integral_sub (((integrable_const (1:ℝ)).indicator hS).const_mul 2) (integrable_const (1:ℝ)),
    integral_const_mul,integral_indicator hS]
  simp

def roundedCellSign {n : ℕ} (P : VertexPartition n) (g : ℝ → ℝ) (i : Fin n) : ℝ :=
  if 0<vertexCellMean P g i then 1 else -1

def roundedVertexTest {n : ℕ} (P : VertexPartition n) (g : ℝ → ℝ) : ℝ → ℝ :=
  vertexStep P (roundedCellSign P g)

def roundedVertexSet {n : ℕ} (P : VertexPartition n) (g : ℝ → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0<vertexCellMean P g i)

theorem roundedVertexTest_measurable {n : ℕ} (P : VertexPartition n) (g : ℝ → ℝ) :
    Measurable (roundedVertexTest P g) := vertexStep_measurable P _

theorem roundedCellSign_abs {n : ℕ} (P : VertexPartition n) (g : ℝ → ℝ) (i : Fin n) :
    |roundedCellSign P g i|=1 := by
  unfold roundedCellSign
  split_ifs <;> norm_num

theorem roundedVertexTest_abs {n : ℕ} (P : VertexPartition n) (g : ℝ → ℝ) (x : ℝ) :
    |roundedVertexTest P g x|=1 := roundedCellSign_abs P g _

/-- Rounding the average's sign improves its correlation with the original sign test. -/
theorem roundedVertexTest_correlation {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    {g : ℝ → ℝ} (hg : Measurable g) (hb : ∀ x, |g x|≤1) :
    (∫ x, (projectedVertexTest P g x)^2 ∂unitMeasure)≤
      ∫ x, g x*roundedVertexTest P g x ∂unitMeasure := by
  rw [← projectedVertexTest_correlation hn P hmass (unitBound_integrable hg hb)]
  change (∫ x, g x*vertexStep P (vertexCellMean P g) x ∂unitMeasure)≤
    ∫ x, g x*vertexStep P (roundedCellSign P g) x ∂unitMeasure
  rw [integral_mul_vertexStep P _ (unitBound_integrable hg hb),integral_mul_vertexStep P _ (unitBound_integrable hg hb)]
  apply Finset.sum_le_sum
  intro i _
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hi : (∫ x in P.fiber i, g x ∂unitMeasure)=vertexCellMean P g i/(n:ℝ) := by
    dsimp only [vertexCellMean]; field_simp
  rw [hi]
  have hc := vertexCellMean_abs_le hn P hmass hg hb i
  simp only [← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hn').mpr
  have he : roundedCellSign P g i*vertexCellMean P g i=|vertexCellMean P g i| := by
    unfold roundedCellSign
    split_ifs with h
    · rw [one_mul,abs_of_pos h]
    · rw [neg_one_mul,abs_of_nonpos (le_of_not_gt h)]
  rw [he]
  nlinarith [sq_abs (vertexCellMean P g i),abs_nonneg (vertexCellMean P g i)]

/-- The rounded step test encodes exactly the cardinality of its vertex partition. -/
theorem roundedVertexTest_integral {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (g : ℝ → ℝ) :
    (∫ x, roundedVertexTest P g x ∂unitMeasure)=2*(roundedVertexSet P g).card/(n:ℝ)-1 := by
  classical
  have he : ∀ i, roundedCellSign P g i=2*(if 0<vertexCellMean P g i then (1:ℝ) else 0)-1 := by
    intro i; unfold roundedCellSign; split_ifs <;> norm_num
  have hi := integral_mul_vertexStep P (roundedCellSign P g) (integrable_const (1:ℝ))
  simp only [one_mul,integral_const,measureReal_restrict_apply_univ,hmass,smul_eq_mul,mul_one] at hi
  change (∫ x, roundedVertexTest P g x ∂unitMeasure)=_ at hi
  rw [hi]
  simp_rw [he]
  have hsum : (∑ i : Fin n, (if 0<vertexCellMean P g i then (1:ℝ) else 0))=(roundedVertexSet P g).card := by
    simp [roundedVertexSet,Finset.sum_boole]
  simp only [← Finset.sum_mul,Finset.sum_sub_distrib,← Finset.mul_sum,hsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hn' : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp

/-- The L¹ error of the rounded sign is controlled by the projection deficit. -/
theorem roundedVertexTest_l1_error {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    {g : ℝ → ℝ} (hg : Measurable g) (hb : ∀ x, g x=1 ∨ g x=-1) :
    (∫ x, |roundedVertexTest P g x-g x| ∂unitMeasure)≤
      1-∫ x, (projectedVertexTest P g x)^2 ∂unitMeasure := by
  have hgabs : ∀ x, |g x|≤1 := fun x => by rcases hb x with h|h <;> simp [h]
  have hs := roundedVertexTest_measurable P g
  have hsabs : ∀ x, |roundedVertexTest P g x|≤1 := fun x => (roundedVertexTest_abs P g x).le
  have he : (fun x => |roundedVertexTest P g x-g x|)=(fun x => 1-g x*roundedVertexTest P g x) := by
    funext x
    rcases hb x with h|h <;> unfold roundedVertexTest vertexStep roundedCellSign <;> split_ifs <;> norm_num [h]
  rw [he,integral_sub (integrable_const (1:ℝ)) (boundedTest_product_integrable hg hs hgabs hsabs)]
  have hc := roundedVertexTest_correlation hn P hmass hg hgabs
  simpa using (sub_le_sub_left hc 1)

end SparseLowerTail.Section03

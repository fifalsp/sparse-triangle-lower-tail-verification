import SparseLowerTail.Section03.StepMatrixCut
import SparseLowerTail.Section03.SignedCut

/-! Cell averages and exact signed tests for arbitrary real step matrices. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

def vertexStep {n : ℕ} (P : VertexPartition n) (c : Fin n → ℝ) (x : ℝ) : ℝ := c (P.color x)

theorem vertexStep_measurable {n : ℕ} (P : VertexPartition n) (c : Fin n → ℝ) :
    Measurable (vertexStep P c) := (measurable_of_countable c).comp P.measurable

theorem vertexStep_integrable {n : ℕ} (P : VertexPartition n) (c : Fin n → ℝ) :
    Integrable (vertexStep P c) unitMeasure := by
  apply Integrable.of_bound (vertexStep_measurable P c).aestronglyMeasurable (∑ i, |c i|)
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs,vertexStep] using
      Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ (P.color x))

/-- Exact integration over the finite measurable vertex partition. -/
theorem integral_vertexPartition {n : ℕ} (P : VertexPartition n) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    (∫ x, f x ∂unitMeasure)=∑ i, ∫ x in P.fiber i, f x ∂unitMeasure := by
  have hcover : (⋃ i, P.fiber i)=univ := by ext x; simp only [mem_iUnion,mem_univ,iff_true]; exact ⟨P.color x,rfl⟩
  have hdisj : Pairwise (fun i j => Disjoint (P.fiber i) (P.fiber j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.symm.trans hj)
  have hh := integral_iUnion_fintype P.measurable_fiber hdisj (fun _ => hf.integrableOn)
  simpa only [hcover,setIntegral_univ] using hh

/-- A bounded measurable function is integrable on the unit interval. -/
theorem unitBound_integrable {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ x, |f x|≤1) :
    Integrable f unitMeasure :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

/-- Multiplication by a finite step test reduces to the cell integrals. -/
theorem integral_mul_vertexStep {n : ℕ} (P : VertexPartition n) (c : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : Integrable f unitMeasure) :
    (∫ x, f x*vertexStep P c x ∂unitMeasure)=∑ i, c i*(∫ x in P.fiber i, f x ∂unitMeasure) := by
  have hi : Integrable (fun x => f x*vertexStep P c x) unitMeasure := by
    have hb : ∀ᵐ x ∂unitMeasure, ‖vertexStep P c x‖≤∑ i, |c i| :=
      Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,vertexStep] using
          Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ (P.color x))
    simpa only [mul_comm] using hf.bdd_mul' (vertexStep_measurable P c).aestronglyMeasurable hb
  rw [integral_vertexPartition P hi]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=∫ x in P.fiber i, c i*f x ∂unitMeasure := by
      apply setIntegral_congr_fun (P.measurable_fiber i)
      intro x hx
      change P.color x=i at hx
      simp only [vertexStep,hx,mul_comm]
    _=_ := integral_const_mul _ _

/-- The signed weighted integral of a real step matrix is exactly its finite block sum. -/
theorem matrixStepKernel_weighted_integral {n : ℕ} (P : VertexPartition n)
    (M : Fin n → Fin n → ℝ) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x|≤1) (hgb : ∀ x, |g x|≤1) :
    (∫ p, f p.1*g p.2*matrixStepKernel P M p ∂squareMeasure)=
      ∑ i, ∑ j, M i j*(∫ x in P.fiber i, f x ∂unitMeasure)*(∫ x in P.fiber j, g x ∂unitMeasure) := by
  have hi := weightedKernel_integrable (matrixStepKernel_integrable P M) hf hg hfb hgb
  have hcover : (⋃ ij : Fin n×Fin n, P.fiber ij.1×ˢP.fiber ij.2)=univ := by
    ext p; simp only [mem_iUnion,mem_univ,iff_true]; exact ⟨(P.color p.1,P.color p.2),rfl,rfl⟩
  have hh := integral_iUnion_fintype
    (fun ij : Fin n×Fin n => (P.measurable_fiber ij.1).prod (P.measurable_fiber ij.2))
    P.rectangles.disjoint (fun _ => hi.integrableOn)
  rw [hcover,setIntegral_univ] at hh
  rw [hh,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  calc
    _=∫ p in P.fiber i×ˢP.fiber j, M i j*(f p.1*g p.2) ∂squareMeasure := by
      apply setIntegral_congr_fun ((P.measurable_fiber i).prod (P.measurable_fiber j))
      rintro p ⟨hi,hj⟩
      change P.color p.1=i at hi
      change P.color p.2=j at hj
      simp only [matrixStepKernel,hi,hj]; ring
    _=M i j*((∫ x in P.fiber i, f x ∂unitMeasure)*(∫ x in P.fiber j, g x ∂unitMeasure)) := by
      rw [integral_const_mul]; congr 1; exact setIntegral_prod_mul f g _ _
    _=_ := by ring

end SparseLowerTail.Section03

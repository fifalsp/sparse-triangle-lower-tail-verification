import SparseLowerTail.Section03.StepMatrixCut
import SparseLowerTail.Section02.CutDistanceIdentities

/-! Algebraic cut-norm bounds for real matrices and their relabeled step kernels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

theorem matrixRectangleSum_add {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (xy : (Fin n → Bool)×(Fin n → Bool)) :
    matrixRectangleSum (fun u v => A u v+B u v) xy=matrixRectangleSum A xy+matrixRectangleSum B xy := by
  simp only [matrixRectangleSum,mul_add,Finset.sum_add_distrib]

theorem finiteMatrixCutNorm_add_le {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    finiteMatrixCutNorm (fun u v => A u v+B u v)≤finiteMatrixCutNorm A+finiteMatrixCutNorm B := by
  unfold finiteMatrixCutNorm
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sup'_le
  intro xy _
  rw [matrixRectangleSum_add]
  exact (abs_add_le _ _).trans (add_le_add
    (Finset.le_sup' (fun xy => |matrixRectangleSum A xy|) (Finset.mem_univ xy))
    (Finset.le_sup' (fun xy => |matrixRectangleSum B xy|) (Finset.mem_univ xy)))

/-- Division by a positive scalar divides the matrix cut norm. -/
theorem finiteMatrixCutNorm_div_le {n : ℕ} (A : Fin n → Fin n → ℝ) {p : ℝ} (hp : 0<p) :
    finiteMatrixCutNorm (fun u v => A u v/p)≤finiteMatrixCutNorm A/p := by
  have hrect : ∀ xy, matrixRectangleSum (fun u v => A u v/p) xy=matrixRectangleSum A xy/p := by
    intro xy
    simp only [matrixRectangleSum,← mul_div_assoc,← Finset.sum_div]
  unfold finiteMatrixCutNorm
  calc
    _≤(Finset.univ.sup' Finset.univ_nonempty (fun xy : (Fin n → Bool)×(Fin n → Bool) =>
      |matrixRectangleSum A xy|)/p)/(n:ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply Finset.sup'_le
        intro xy _
        rw [hrect,abs_div,abs_of_pos hp]
        exact div_le_div_of_nonneg_right (Finset.le_sup' (fun xy => |matrixRectangleSum A xy|) (Finset.mem_univ xy)) hp.le
    _=_ := by ring

/-- Matrix closeness and graphon closeness combine after the same genuine relabeling. -/
theorem stepKernel_close_of_matrix_and_graphon (n : ℕ) (hn : 0<n)
    (A B : Fin n → Fin n → ℝ) (U W : Graphon)
    (hU : ∀ x, U x=matrixStepKernel (uniformVertexPartition n hn) B x)
    (φ : BijectiveRelabeling) {a b : ℝ}
    (hmat : finiteMatrixCutNorm (fun u v => A u v-B u v)≤a)
    (hnear : cutNorm (fun x => relabel U φ.toRelabeling x-W x)≤b) :
    cutNorm (fun x => matrixStepKernel (uniformVertexPartition n hn) A (φ.equiv x.1,φ.equiv x.2)-W x)≤a+b := by
  let K := matrixStepKernel (uniformVertexPartition n hn) (fun u v => A u v-B u v)
  have hK : Integrable (pullbackKernel K φ) squareMeasure :=
    integrable_pullbackKernel (matrixStepKernel_integrable _ _) φ
  have hUW := (graphon_integrable (relabel U φ.toRelabeling)).sub (graphon_integrable W)
  have he : (fun x => matrixStepKernel (uniformVertexPartition n hn) A (φ.equiv x.1,φ.equiv x.2)-W x) =
      (fun x => pullbackKernel K φ x+(relabel U φ.toRelabeling x-W x)) := by
    funext x
    change _=K (φ.equiv x.1,φ.equiv x.2)+(U (φ.equiv x.1,φ.equiv x.2)-W x)
    rw [hU]
    dsimp only [K,matrixStepKernel]
    ring
  rw [he]
  have hnorm : cutNorm (pullbackKernel K φ)≤a := by
    exact (cutNorm_uniform_step_comp n hn _ φ.equiv φ.preserving).trans_le hmat
  exact (cutNorm_add_le hK hUW).trans (add_le_add hnorm hnear)

end SparseLowerTail.Section03

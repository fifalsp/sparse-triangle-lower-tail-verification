import SparseLowerTail.Section03.Rounding
import SparseLowerTail.Section03.ConditionedStructure

/-! Matrix forms of the two possible minimizer structures. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section03
open Section02

/-- Positive scaling of a real matrix scales its finite cut norm. -/
theorem finiteMatrixCutNorm_mul_le {n : ℕ} (A : Fin n → Fin n → ℝ) {p : ℝ} (hp : 0≤p) :
    finiteMatrixCutNorm (fun i j => p*A i j)≤p*finiteMatrixCutNorm A := by
  have hrect : ∀ xy, matrixRectangleSum (fun i j => p*A i j) xy=p*matrixRectangleSum A xy := by
    intro xy
    simp only [matrixRectangleSum,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  unfold finiteMatrixCutNorm
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sup'_le
  intro xy _
  rw [hrect,abs_mul,abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun xy => |matrixRectangleSum A xy|) (Finset.mem_univ xy)) hp

/-- A normalized approximation gives the stated unnormalized error εp. -/
theorem matrix_rescale_error {n : ℕ} (A B : Fin n → Fin n → ℝ) {p ε : ℝ} (hp : 0<p)
    (hnear : finiteMatrixCutNorm (fun i j => A i j/p-B i j)≤ε) :
    finiteMatrixCutNorm (fun i j => A i j-p*B i j)≤ε*p := by
  have he : (fun i j => A i j-p*B i j)=(fun i j => p*(A i j/p-B i j)) := by
    funext i j; field_simp
  rw [he]
  exact (finiteMatrixCutNorm_mul_le _ hp.le).trans (by nlinarith)

def configurationAdjacency (n : ℕ) (z : GraphEdgeCoordinate n → Bool) : Fin n → Fin n → ℝ :=
  graphEdgeMatrix (extendGraphEdges (fun i => ((z i).toNat:ℝ)))

def ConstantMatrixClose (n : ℕ) (p r ε : ℝ) (z : GraphEdgeCoordinate n → Bool) : Prop :=
  finiteMatrixCutNorm (fun i j => configurationAdjacency n z i j-r*p)≤ε*p

def BipodMatrixClose (n : ℕ) (p a b ε : ℝ) (z : GraphEdgeCoordinate n → Bool) : Prop :=
  ∃ S : Finset (Fin n), |(S.card:ℝ)-(n:ℝ)/2|≤ε*(n:ℝ) ∧
    finiteMatrixCutNorm (fun i j => configurationAdjacency n z i j-p*bipodMatrix a b S i j)≤ε*p

/-- Proximity to a constant minimizer gives the constant matrix conclusion. -/
theorem triangle_close_constant (n : ℕ) (hn : 0<n) {p r δ ε : ℝ} (hp : 0<p) (hδε : δ≤ε)
    (z : GraphEdgeCoordinate n → Bool) (U : Graphon) (hU : IsConstant U r)
    (φ : BijectiveRelabeling)
    (hnear : cutNorm (fun x => triangleScaledKernel n hn p z (φ.equiv x.1,φ.equiv x.2)-U x)<δ) :
    ConstantMatrixClose n p r ε z := by
  have he : (fun x => triangleScaledKernel n hn p z (φ.equiv x.1,φ.equiv x.2)-U x)=ᵐ[squareMeasure]
      (fun x => matrixStepKernel (uniformVertexPartition n hn)
        (fun i j => configurationAdjacency n z i j/p-r) (φ.equiv x.1,φ.equiv x.2)) := by
    filter_upwards [hU] with x hx
    dsimp only [triangleScaledKernel,matrixStepKernel,configurationAdjacency]
    rw [hx]
  rw [cutNorm_congr_ae he,cutNorm_uniform_step_comp n hn _ φ.equiv φ.preserving] at hnear
  have hm := matrix_rescale_error (configurationAdjacency n z) (fun _ _ => r) hp (hnear.le.trans hδε)
  simpa only [ConstantMatrixClose,mul_comm] using hm

/-- Proximity to a balanced minimizer gives an explicit near-balanced vertex partition. -/
theorem triangle_close_bipod (n : ℕ) (hn : 0<n) {p a b δ ε : ℝ} (hp : 0<p) (hab : a<b)
    (hδ : 0<δ) (hδε : 33*δ≤ε) (hbalance : 16*δ/(b-a)≤ε)
    (z : GraphEdgeCoordinate n → Bool) (U : Graphon) (hU : IsBalanced U a b)
    (φ : BijectiveRelabeling)
    (hnear : cutNorm (fun x => triangleScaledKernel n hn p z (φ.equiv x.1,φ.equiv x.2)-U x)<δ) :
    BipodMatrixClose n p a b ε z := by
  obtain ⟨S₀,hS,_hsubset,hhalf,hrep⟩ := hU
  have hmass : unitMeasure.real S₀=1/2 := by
    rw [measureReal_def,hhalf]
    norm_num
  have he : (fun x => triangleScaledKernel n hn p z (φ.equiv x.1,φ.equiv x.2)-U x)=ᵐ[squareMeasure]
      (fun x => matrixStepKernel (uniformVertexPartition n hn)
        (fun i j => configurationAdjacency n z i j/p) (φ.equiv x.1,φ.equiv x.2)-balancedBipodKernel a b S₀ x) := by
    filter_upwards [hrep] with x hx
    exact congrArg (fun u => triangleScaledKernel n hn p z (φ.equiv x.1,φ.equiv x.2)-u) hx
  rw [cutNorm_congr_ae he] at hnear
  obtain ⟨S,hcard,hmat⟩ := matrix_bipod_rounding n hn (fun i j => configurationAdjacency n z i j/p)
    hab hδ φ.equiv φ.preserving hS hmass hnear.le
  refine ⟨S,?_,matrix_rescale_error (configurationAdjacency n z) (bipodMatrix a b S) hp (hmat.trans hδε)⟩
  have hh := mul_le_mul_of_nonneg_right hbalance (Nat.cast_nonneg n : (0:ℝ)≤n)
  have heq : 16*δ*(n:ℝ)/(b-a)=(16*δ/(b-a))*(n:ℝ) := by ring
  exact hcard.trans (heq.trans_le hh)

end SparseLowerTail.Section03

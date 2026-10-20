import SparseLowerTail.Section03.RankOneRounding

/-! The manuscript's finite vertex-partition rounding lemma for arbitrary real matrices. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

def bipodMatrix {n : ℕ} (a b : ℝ) (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if (i∈S ↔ j∈S) then a else b

def balancedBipodKernel (a b : ℝ) (S : Set ℝ) (p : ℝ×ℝ) : ℝ := by
  classical
  exact if (p.1∈S ↔ p.2∈S) then a else b

theorem balancedBipodKernel_rankOne (a b : ℝ) (S : Set ℝ) :
    balancedBipodKernel a b S=signedRankOneKernel ((a+b)/2) ((a-b)/2) (partitionSign S) := by
  classical
  funext p
  by_cases hx : p.1∈S <;> by_cases hy : p.2∈S <;>
    simp [balancedBipodKernel,signedRankOneKernel,partitionSign,hx,hy] <;> ring

theorem roundedMatrix_rankOne {n : ℕ} (P : VertexPartition n) (g : ℝ → ℝ) (a b : ℝ) :
    matrixStepKernel P (bipodMatrix a b (roundedVertexSet P g))=
      signedRankOneKernel ((a+b)/2) ((a-b)/2) (roundedVertexTest P g) := by
  classical
  funext p
  by_cases hx : 0<vertexCellMean P g (P.color p.1) <;>
    by_cases hy : 0<vertexCellMean P g (P.color p.2) <;>
    simp [matrixStepKernel,bipodMatrix,roundedVertexSet,signedRankOneKernel,
      roundedVertexTest,vertexStep,roundedCellSign,hx,hy] <;> ring

/-- `lem:rounding` on any equal-mass measurable vertex partition.
The signed-test argument actually gives cut error ≤17δ, hence the stated 33δ. -/
theorem rounding_on_partition {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    (M : Fin n → Fin n → ℝ) {a b δ : ℝ} (hab : a<b) (hδ : 0<δ)
    {S₀ : Set ℝ} (hS : MeasurableSet S₀) (hhalf : unitMeasure.real S₀=1/2)
    (hnear : cutNorm (fun p => matrixStepKernel P M p-balancedBipodKernel a b S₀ p)≤δ) :
    ∃ S : Finset (Fin n), |(S.card:ℝ)-(n:ℝ)/2|≤16*δ*(n:ℝ)/(b-a) ∧
      finiteMatrixCutNorm (fun i j => M i j-bipodMatrix a b S i j)≤33*δ := by
  let g := partitionSign S₀
  let ℓ := (a+b)/2
  let μ := (a-b)/2
  let e := 1-∫ x, (projectedVertexTest P g x)^2 ∂unitMeasure
  have hgap : 0<b-a := sub_pos.mpr hab
  have hg : Measurable g := partitionSign_measurable hS
  have hga : ∀ x, |g x|=1 := partitionSign_abs S₀
  have hgb : ∀ x, |g x|≤1 := fun x => (hga x).le
  have hgs : ∀ x, g x=1 ∨ g x=-1 := by
    intro x; dsimp only [g,partitionSign]; split_ifs <;> simp
  have hmean : (∫ x, g x ∂unitMeasure)=0 := by rw [partitionSign_integral hS,hhalf]; norm_num
  have hsquare : (∫ x, g x*g x ∂unitMeasure)=1 := by
    have he : (fun x => g x*g x)=(fun _ => (1:ℝ)) := by
      funext x; rcases hgs x with h|h <;> simp [h]
    rw [he]; simp
  rw [balancedBipodKernel_rankOne] at hnear
  have hdef := signed_projection_defect hn P hmass M hg hgb hmean hsquare ℓ μ δ hnear
  change |μ| * e≤8*δ at hdef
  have hmu : |μ|=(b-a)/2 := by
    dsimp only [μ]
    rw [abs_of_neg (div_neg_of_neg_of_pos (sub_neg.mpr hab) (by norm_num))]
    ring
  have he0 : 0≤e := by
    have hh := projectedVertexTest_square_bounds hn P hmass hg hgb
    dsimp only [e]; linarith [hh.2]
  have hebound : e≤16*δ/(b-a) := by
    rw [hmu] at hdef
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    nlinarith
  refine ⟨roundedVertexSet P g,?_,?_⟩
  · have hh := roundedVertexSet_balance hn P hmass hg hgs hmean
    change |((roundedVertexSet P g).card:ℝ)-(n:ℝ)/2|≤(n:ℝ)/2*e at hh
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hh' := mul_le_mul_of_nonneg_left hebound (show (0:ℝ)≤(n:ℝ)/2 by positivity)
    have hnonneg : 0≤16*δ*(n:ℝ)/(b-a) := by positivity
    exact hh.trans (hh'.trans (by
      have he : (n:ℝ)/2*(16*δ/(b-a))=(16*δ*(n:ℝ)/(b-a))/2 := by ring
      rw [he]
      linarith))
  · let s := roundedVertexTest P g
    have hs := roundedVertexTest_measurable P g
    have hsa : ∀ x, |s x|=1 := roundedVertexTest_abs P g
    have herror := roundedVertexTest_l1_error hn P hmass hg hgs
    change (∫ x, |s x-g x| ∂unitMeasure)≤e at herror
    have hl1 := signedRankOneKernel_l1_le ℓ μ hg hs hga hsa
    have hl1bound : (∫ p, |signedRankOneKernel ℓ μ g p-signedRankOneKernel ℓ μ s p| ∂squareMeasure)≤16*δ := by
      exact hl1.trans ((mul_le_mul_of_nonneg_left herror (by positivity : 0≤2*|μ|)).trans (by nlinarith [hdef]))
    have hM := matrixStepKernel_integrable P M
    have hG := signedRankOneKernel_integrable ℓ μ hg hgb
    have hS' := signedRankOneKernel_integrable ℓ μ hs (fun x => (hsa x).le)
    have hnorm := (cutNorm_le_l1 (hG.sub hS')).trans hl1bound
    have hadd := cutNorm_add_le (hM.sub hG) (hG.sub hS')
    have he : (fun p => (matrixStepKernel P M p-signedRankOneKernel ℓ μ g p)+
      (signedRankOneKernel ℓ μ g p-signedRankOneKernel ℓ μ s p))=
      (fun p => matrixStepKernel P M p-signedRankOneKernel ℓ μ s p) := by funext p; ring
    simp only [Pi.sub_apply] at hadd
    rw [he] at hadd
    change cutNorm (matrixStepKernel P M-signedRankOneKernel ℓ μ g)≤δ at hnear
    change cutNorm (signedRankOneKernel ℓ μ g-signedRankOneKernel ℓ μ s)≤16*δ at hnorm
    have htotal : cutNorm (fun p => matrixStepKernel P M p-signedRankOneKernel ℓ μ s p)≤33*δ :=
      hadd.trans (by linarith)
    have heq : (fun p => matrixStepKernel P M p-signedRankOneKernel ℓ μ s p)=
        matrixStepKernel P (fun i j => M i j-bipodMatrix a b (roundedVertexSet P g) i j) := by
      rw [← roundedMatrix_rankOne P g a b]
      rfl
    rw [heq,cutNorm_matrixStepKernel hn P hmass] at htotal
    exact htotal

/-- The manuscript's relabeled interval-step formulation, valid even for a noninvertible
measure-preserving map and without requiring the real matrix to be bounded. -/
theorem matrix_bipod_rounding (n : ℕ) (hn : 0<n) (M : Fin n → Fin n → ℝ)
    {a b δ : ℝ} (hab : a<b) (hδ : 0<δ) (φ : ℝ → ℝ)
    (hφ : MeasurePreserving φ unitMeasure unitMeasure)
    {S₀ : Set ℝ} (hS : MeasurableSet S₀) (hhalf : unitMeasure.real S₀=1/2)
    (hnear : cutNorm (fun p => matrixStepKernel (uniformVertexPartition n hn) M (φ p.1,φ p.2)-
      balancedBipodKernel a b S₀ p)≤δ) :
    ∃ S : Finset (Fin n), |(S.card:ℝ)-(n:ℝ)/2|≤16*δ*(n:ℝ)/(b-a) ∧
      finiteMatrixCutNorm (fun i j => M i j-bipodMatrix a b S i j)≤33*δ := by
  exact rounding_on_partition hn (pullbackVertexPartition (uniformVertexPartition n hn) φ hφ)
    (fun i => (pullbackVertexPartition_mass _ φ hφ i).trans (uniformVertexPartition_mass n hn i))
    M hab hδ hS hhalf hnear

end SparseLowerTail.Section03

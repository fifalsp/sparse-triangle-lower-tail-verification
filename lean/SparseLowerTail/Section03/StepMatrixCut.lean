import SparseLowerTail.Section03.BernoulliConcentration
import SparseLowerTail.Section02.BlockAveraging

/-! The passage from finite matrix tests to measurable equal-mass step kernels. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

/-- Maximizing a linear functional on a cube only needs its vertices. -/
theorem finite_cube_linear_round {ι : Type*} [Fintype ι] (a f : ι → ℝ)
    (hf : ∀ i, f i∈Icc (0:ℝ) 1) :
    ∃ b : ι → Bool, (∑ i, f i*a i)≤∑ i, (b i).toNat*a i := by
  classical
  refine ⟨fun i => decide (0≤a i),Finset.sum_le_sum ?_⟩
  intro i _
  by_cases ha : 0≤a i
  · simp only [ha,decide_true,Bool.toNat_true,Nat.cast_one,one_mul]
    exact mul_le_of_le_one_left ha (hf i).2
  · simp only [ha,decide_false,Bool.toNat_false,Nat.cast_zero,zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hf i).1 (le_of_not_ge ha)

/-- Successively round the left and right matrix tests to cube vertices. -/
theorem matrix_cube_round {n : ℕ} (Z : Fin n → Fin n → ℝ) (f g : Fin n → ℝ)
    (hf : ∀ i, f i∈Icc (0:ℝ) 1) (hg : ∀ i, g i∈Icc (0:ℝ) 1) :
    ∃ xy : (Fin n → Bool)×(Fin n → Bool),
      (∑ i, ∑ j, f i*g j*Z i j)≤matrixRectangleSum Z xy := by
  obtain ⟨x,hx⟩ := finite_cube_linear_round (fun i => ∑ j, g j*Z i j) f hf
  obtain ⟨y,hy⟩ := finite_cube_linear_round (fun j => ∑ i, (x i).toNat*Z i j) g hg
  refine ⟨(x,y),?_⟩
  simp only [Finset.mul_sum] at hx hy
  have he : (∑ j, ∑ i, g j*((x i).toNat*Z i j))=
      ∑ i, ∑ j, (x i).toNat*(g j*Z i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [he] at hy
  have he' : (∑ j, ∑ i, (y j).toNat*((x i).toNat*Z i j))=matrixRectangleSum Z (x,y) := by
    rw [Finset.sum_comm]
    unfold matrixRectangleSum
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [he'] at hy
  simpa only [mul_assoc] using hx.trans hy

/-- The absolute weighted bilinear form is bounded by the maximum binary rectangle test. -/
theorem matrix_cube_abs_le {n : ℕ} (Z : Fin n → Fin n → ℝ) (f g : Fin n → ℝ)
    (hf : ∀ i, f i∈Icc (0:ℝ) 1) (hg : ∀ i, g i∈Icc (0:ℝ) 1) :
    |∑ i, ∑ j, f i*g j*Z i j|≤Finset.univ.sup' Finset.univ_nonempty
      (fun xy : (Fin n → Bool)×(Fin n → Bool) => |matrixRectangleSum Z xy|) := by
  obtain ⟨xy,hxy⟩ := matrix_cube_round Z f g hf hg
  obtain ⟨xy',hxy'⟩ := matrix_cube_round (fun i j => -Z i j) f g hf hg
  have hneg : (∑ i, ∑ j, f i*g j*(-Z i j)) = -(∑ i, ∑ j, f i*g j*Z i j) := by
    simp only [mul_neg,Finset.sum_neg_distrib]
  have hn : matrixRectangleSum (fun i j => -Z i j) xy' = -matrixRectangleSum Z xy' := by
    simp only [matrixRectangleSum,mul_neg,Finset.sum_neg_distrib]
  rw [hneg,hn] at hxy'
  apply abs_le.mpr
  constructor
  · have hh := (neg_le_abs (matrixRectangleSum Z xy')).trans
      (Finset.le_sup' (fun xy => |matrixRectangleSum Z xy|) (Finset.mem_univ xy'))
    linarith
  · exact hxy.trans ((le_abs_self _).trans
      (Finset.le_sup' (fun xy => |matrixRectangleSum Z xy|) (Finset.mem_univ xy)))

/-- The actual step kernel on a measurable vertex partition. -/
def matrixStepKernel {n : ℕ} (P : VertexPartition n) (Z : Fin n → Fin n → ℝ)
    (p : ℝ×ℝ) : ℝ := Z (P.color p.1) (P.color p.2)

theorem matrixStepKernel_integrable {n : ℕ} (P : VertexPartition n)
    (Z : Fin n → Fin n → ℝ) : Integrable (matrixStepKernel P Z) squareMeasure := by
  have hm : Measurable (matrixStepKernel P Z) :=
    (measurable_of_countable (fun ij : Fin n×Fin n => Z ij.1 ij.2)).comp
      ((P.measurable.comp measurable_fst).prodMk (P.measurable.comp measurable_snd))
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ i, ∑ j, |Z i j|)
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs]
  exact (Finset.single_le_sum (fun j _ => abs_nonneg (Z (P.color p.1) j))
    (Finset.mem_univ (P.color p.2))).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg (Z i j)))
        (Finset.mem_univ (P.color p.1)))

/-- Every measurable rectangle integral is the corresponding finite block sum. -/
theorem matrixStepKernel_rectangle {n : ℕ} (P : VertexPartition n)
    (Z : Fin n → Fin n → ℝ) (S T : Set ℝ) :
    rectangleIntegral (matrixStepKernel P Z) S T =
      ∑ i, ∑ j, Z i j*unitMeasure.real (P.fiber i∩S)*unitMeasure.real (P.fiber j∩T) := by
  classical
  have hcover : (⋃ ij : Fin n×Fin n, P.fiber ij.1 ×ˢ P.fiber ij.2)=univ := by
    ext p
    simp only [mem_iUnion,mem_univ,iff_true]
    exact ⟨(P.color p.1,P.color p.2),rfl,rfl⟩
  have hh := integral_iUnion_fintype (μ:=squareMeasure.restrict (S×ˢT))
    (fun ij : Fin n×Fin n => (P.measurable_fiber ij.1).prod (P.measurable_fiber ij.2))
    P.rectangles.disjoint (fun _ => (matrixStepKernel_integrable P Z).integrableOn.integrableOn)
  rw [hcover,setIntegral_univ] at hh
  change rectangleIntegral (matrixStepKernel P Z) S T = _ at hh
  rw [hh, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (∫ p in P.fiber i×ˢP.fiber j, matrixStepKernel P Z p
      ∂squareMeasure.restrict (S×ˢT)) =
      ∫ _ in P.fiber i×ˢP.fiber j, Z i j ∂squareMeasure.restrict (S×ˢT) := by
    apply setIntegral_congr_fun ((P.measurable_fiber i).prod (P.measurable_fiber j))
    rintro p ⟨hi,hj⟩
    change P.color p.1=i at hi
    change P.color p.2=j at hj
    simp only [matrixStepKernel,hi,hj]
  rw [he]
  simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,
    measureReal_def,Measure.restrict_apply ((P.measurable_fiber i).prod (P.measurable_fiber j)),
    prod_inter_prod,Measure.prod_prod,ENNReal.toReal_mul]
  ring

/-- A rectangle cuts each equal-mass cell by a fraction in [0,1]. -/
theorem partition_test_mem_Icc {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (S : Set ℝ) (i : Fin n) :
    (n:ℝ)*unitMeasure.real (P.fiber i∩S)∈Icc (0:ℝ) 1 := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hm := measureReal_mono (μ:=unitMeasure) (inter_subset_left : P.fiber i∩S⊆P.fiber i)
  rw [hmass i] at hm
  constructor
  · exact mul_nonneg hn'.le measureReal_nonneg
  · calc
      _ ≤ (n:ℝ)*(1/(n:ℝ)) := mul_le_mul_of_nonneg_left hm hn'.le
      _ = 1 := by field_simp

/-- A measurable step-kernel rectangle is controlled by the finite matrix cut norm. -/
theorem matrixStepKernel_rectangle_le {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    (Z : Fin n → Fin n → ℝ) (S T : Set ℝ) :
    |rectangleIntegral (matrixStepKernel P Z) S T|≤finiteMatrixCutNorm Z := by
  let f := fun i => (n:ℝ)*unitMeasure.real (P.fiber i∩S)
  let g := fun i => (n:ℝ)*unitMeasure.real (P.fiber i∩T)
  have hh := matrix_cube_abs_le Z f g (partition_test_mem_Icc hn P hmass S)
    (partition_test_mem_Icc hn P hmass T)
  have he : (∑ i, ∑ j, f i*g j*Z i j) =
      (n:ℝ)^2*rectangleIntegral (matrixStepKernel P Z) S T := by
    rw [matrixStepKernel_rectangle]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    dsimp only [f,g]; ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)] at hh
  exact (le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast hn : (0:ℝ)<n))).mpr (by
    simpa only [mul_comm] using hh)

/-- All measurable cuts of an equal-mass step kernel are bounded by binary matrix cuts. -/
theorem cutNorm_matrixStepKernel_le {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (Z : Fin n → Fin n → ℝ) :
    cutNorm (matrixStepKernel P Z)≤finiteMatrixCutNorm Z := by
  apply csSup_le (show {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧
    |rectangleIntegral (matrixStepKernel P Z) S T|=v}.Nonempty from
    ⟨0,∅,∅,MeasurableSet.empty,MeasurableSet.empty,by simp [rectangleIntegral]⟩)
  rintro v ⟨S,T,_hS,_hT,rfl⟩
  exact matrixStepKernel_rectangle_le hn P hmass Z S T

/-- The union of cells selected by a binary vector. -/
def partitionBinarySet {n : ℕ} (P : VertexPartition n) (b : Fin n → Bool) : Set ℝ :=
  {x | b (P.color x)=true}

theorem partitionBinarySet_measurable {n : ℕ} (P : VertexPartition n) (b : Fin n → Bool) :
    MeasurableSet (partitionBinarySet P b) := P.measurable (Set.to_countable {i | b i=true}).measurableSet

theorem partitionBinarySet_cell_mass {n : ℕ} (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (b : Fin n → Bool) (i : Fin n) :
    unitMeasure.real (P.fiber i∩partitionBinarySet P b)=(b i).toNat/(n:ℝ) := by
  have he : P.fiber i∩partitionBinarySet P b=if b i then P.fiber i else ∅ := by
    ext x
    simp only [mem_inter_iff,VertexPartition.fiber,mem_preimage,mem_singleton_iff,
      partitionBinarySet,mem_setOf_eq]
    cases hb : b i <;> simp
    · intro hx; simp [hx,hb]
    · exact fun hx => by simp [hx,hb]
  rw [he]
  cases hb : b i <;> simp [hmass]

/-- Every binary matrix test is realized by a measurable union of partition cells. -/
theorem matrixStepKernel_binary_rectangle {n : ℕ} (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    (Z : Fin n → Fin n → ℝ) (xy : (Fin n → Bool)×(Fin n → Bool)) :
    rectangleIntegral (matrixStepKernel P Z) (partitionBinarySet P xy.1) (partitionBinarySet P xy.2)=
      matrixRectangleSum Z xy/(n:ℝ)^2 := by
  rw [matrixStepKernel_rectangle]
  simp_rw [partitionBinarySet_cell_mass P hmass]
  simp only [matrixRectangleSum,Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- The finite and graphon cut norms coincide on every measurable equal-mass partition. -/
theorem cutNorm_matrixStepKernel {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (Z : Fin n → Fin n → ℝ) :
    cutNorm (matrixStepKernel P Z)=finiteMatrixCutNorm Z := by
  apply le_antisymm (cutNorm_matrixStepKernel_le hn P hmass Z)
  have hn2 : (0:ℝ)<(n:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hn)
  apply (div_le_iff₀ hn2).mpr
  apply Finset.sup'_le
  intro xy _
  have hh := abs_rectangleIntegral_le_cutNorm (matrixStepKernel_integrable P Z)
    (partitionBinarySet_measurable P xy.1) (partitionBinarySet_measurable P xy.2)
  rw [matrixStepKernel_binary_rectangle P hmass,abs_div,abs_of_nonneg hn2.le] at hh
  exact (div_le_iff₀ hn2).mp hh

/-- The graphon form of the Bernoulli cut-concentration estimate. -/
theorem bernoulli_step_cut_concentration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (ends : ι → Fin n×Fin n)
    (hinj : Function.Injective ends) (horder : ∀ i, (ends i).1<(ends i).2)
    (q : ι → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) 1) {ε p : ℝ}
    (hε : ε∈Icc (0:ℝ) 1) (hp : 0≤p) (hqp : ∀ i, q i≤p) :
    finiteEventMass (productBernoulliMass q)
      (Finset.univ.filter (fun z => ε*p<cutNorm (matrixStepKernel P
        (symmetricEdgeMatrix ends (fun i => (z i).toNat-q i))))) ≤
      2*4^n*Real.exp (-ε^2*p*(n:ℝ)^2/8) := by
  simp only [cutNorm_matrixStepKernel hn P hmass]
  exact bernoulli_matrix_cut_concentration hn ends hinj horder q hq hε hp hqp

/-- Binary rectangle tests attain the finite cut norm. -/
theorem finiteMatrixCutNorm_attained {n : ℕ} (Z : Fin n → Fin n → ℝ) :
    ∃ xy : (Fin n → Bool)×(Fin n → Bool),
      finiteMatrixCutNorm Z=|matrixRectangleSum Z xy|/(n:ℝ)^2 := by
  obtain ⟨xy,_hxy,heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun xy : (Fin n → Bool)×(Fin n → Bool) => |matrixRectangleSum Z xy|)
  exact ⟨xy,congrArg (fun a : ℝ => a/(n:ℝ)^2) heq⟩

/-- Pull a finite vertex partition back by any measure-preserving map. -/
def pullbackVertexPartition {n : ℕ} (P : VertexPartition n) (φ : ℝ → ℝ)
    (hφ : MeasurePreserving φ unitMeasure unitMeasure) : VertexPartition n where
  color := P.color ∘ φ
  measurable := P.measurable.comp hφ.measurable

theorem pullbackVertexPartition_mass {n : ℕ} (P : VertexPartition n) (φ : ℝ → ℝ)
    (hφ : MeasurePreserving φ unitMeasure unitMeasure) (i : Fin n) :
    unitMeasure.real ((pullbackVertexPartition P φ hφ).fiber i)=unitMeasure.real (P.fiber i) := by
  change unitMeasure.real (φ ⁻¹' P.fiber i)=unitMeasure.real (P.fiber i)
  exact hφ.measureReal_preimage (s:=P.fiber i) (P.measurable_fiber i).nullMeasurableSet

/-- Step-kernel cut norms are invariant even under noninvertible measure-preserving maps. -/
theorem cutNorm_matrixStepKernel_comp {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ)) (Z : Fin n → Fin n → ℝ)
    (φ : ℝ → ℝ) (hφ : MeasurePreserving φ unitMeasure unitMeasure) :
    cutNorm (fun p => matrixStepKernel P Z (φ p.1,φ p.2)) =
      cutNorm (matrixStepKernel P Z) := by
  change cutNorm (matrixStepKernel (pullbackVertexPartition P φ hφ) Z)=_
  rw [cutNorm_matrixStepKernel hn P hmass,
    cutNorm_matrixStepKernel hn (pullbackVertexPartition P φ hφ)
      (fun i => (pullbackVertexPartition_mass P φ hφ i).trans (hmass i))]

/-- The standard n-cell interval coloring, with null endpoints assigned by clipping. -/
def uniformVertexPartition (n : ℕ) (hn : 0<n) : VertexPartition n where
  color x := ⟨min (Nat.floor ((n:ℝ)*x)) (n-1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn (by decide))⟩
  measurable := by
    let g : ℕ → Fin n := fun m => ⟨min m (n-1),
      lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn (by decide))⟩
    exact (measurable_of_countable g).comp (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

theorem uniformVertexPartition_fiber_ae (n : ℕ) (hn : 0<n) (i : Fin n) :
    (uniformVertexPartition n hn).fiber i =ᵐ[unitMeasure]
      Ico ((i:ℝ)/(n:ℝ)) (((i:ℝ)+1)/(n:ℝ)) := by
  letI : NoAtoms unitMeasure := by unfold unitMeasure; infer_instance
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hsupport : ∀ᵐ x ∂unitMeasure, x∈Ioo (0:ℝ) 1 := by
    have hmem : ∀ᵐ x ∂unitMeasure, x∈Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem,measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0:ℝ)),
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton (1:ℝ))] with x hx hx0 hx1
    simp only [mem_singleton_iff] at hx0 hx1
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),lt_of_le_of_ne hx.2 hx1⟩
  filter_upwards [hsupport] with x hx
  have hnonneg : 0≤(n:ℝ)*x := mul_nonneg hn'.le hx.1.le
  have hfloor : Nat.floor ((n:ℝ)*x)<n := (Nat.floor_lt hnonneg).mpr (by nlinarith [hx.2])
  apply propext
  change (⟨min (Nat.floor ((n:ℝ)*x)) (n-1),_⟩ : Fin n)=i ↔ _
  rw [Fin.ext_iff]
  change min (Nat.floor ((n:ℝ)*x)) (n-1)=i.val ↔ _
  rw [min_eq_left (Nat.le_sub_one_of_lt hfloor),Nat.floor_eq_iff hnonneg]
  change ((i.val:ℝ)≤(n:ℝ)*x ∧ (n:ℝ)*x<(i.val:ℝ)+1) ↔
    ((i:ℝ)/(n:ℝ)≤x ∧ x<((i:ℝ)+1)/(n:ℝ))
  rw [div_le_iff₀ hn',lt_div_iff₀ hn']
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith

theorem uniformVertexPartition_mass (n : ℕ) (hn : 0<n) (i : Fin n) :
    unitMeasure.real ((uniformVertexPartition n hn).fiber i)=1/(n:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hi0 : (0:ℝ) ≤ (i:ℝ) := by exact_mod_cast (Nat.zero_le i.val)
  have hin : (i:ℝ)+1≤n := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  rw [measureReal_congr (uniformVertexPartition_fiber_ae n hn i)]
  have hsub : Ico ((i:ℝ)/(n:ℝ)) (((i:ℝ)+1)/(n:ℝ))⊆Icc (0:ℝ) 1 := by
    intro x hx
    exact ⟨(div_nonneg hi0 hn'.le).trans hx.1,
      hx.2.le.trans ((div_le_one hn').mpr hin)⟩
  simp only [measureReal_def,unitMeasure,Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr hsub,Real.volume_Ico]
  rw [ENNReal.toReal_ofReal (by apply sub_nonneg.mpr; apply div_le_div_of_nonneg_right _ hn'.le; linarith)]
  ring

/-- Manuscript lem:stepcut for the canonical interval step kernel and every measure-preserving map. -/
theorem cutNorm_uniform_step_comp (n : ℕ) (hn : 0<n) (Z : Fin n → Fin n → ℝ)
    (φ : ℝ → ℝ) (hφ : MeasurePreserving φ unitMeasure unitMeasure) :
    cutNorm (fun p => matrixStepKernel (uniformVertexPartition n hn) Z (φ p.1,φ p.2))=
      finiteMatrixCutNorm Z := by
  rw [cutNorm_matrixStepKernel_comp hn _ (uniformVertexPartition_mass n hn) Z φ hφ,
    cutNorm_matrixStepKernel hn _ (uniformVertexPartition_mass n hn)]

end SparseLowerTail.Section03

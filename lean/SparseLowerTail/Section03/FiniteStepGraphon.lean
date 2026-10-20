import SparseLowerTail.Section03.Decorrelation

/-! Exact finite-partition integral formulas used to pass between matrices and graphons. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

/-- Integrating a function constant on a finite measurable coloring. -/
theorem integral_finite_coloring {Ω κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace κ] [Fintype κ] [MeasurableSingletonClass κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → κ) (hf : Measurable f) (g : κ → ℝ) :
    (∫ x, g (f x) ∂μ)=∑ i, μ.real (f ⁻¹' {i})*g i := by
  classical
  have hi : Integrable (fun x => g (f x)) μ := by
    apply Integrable.of_bound ((measurable_of_countable g).comp hf).aestronglyMeasurable
      (∑ i, |g i|)
    apply Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs] using
      Finset.single_le_sum (fun i _ => abs_nonneg (g i)) (Finset.mem_univ (f x))
  have hcover : (⋃ i : κ, f ⁻¹' {i})=univ := by ext x; simp
  have hdisjoint : Pairwise (fun i j : κ => Disjoint (f ⁻¹' {i}) (f ⁻¹' {j})) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.symm.trans hj)
  have hh := integral_iUnion_fintype (fun i => hf (measurableSet_singleton i))
    hdisjoint (fun _ => hi.integrableOn)
  rw [hcover,setIntegral_univ] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∫ x in f ⁻¹' {i}, g (f x) ∂μ)=∫ _ in f ⁻¹' {i}, g i ∂μ := by
    apply setIntegral_congr_fun (hf (measurableSet_singleton i))
    intro x hx
    change g (f x)=g i
    rw [show f x=i from hx]
  rw [he]
  simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,measureReal_def]

/-- Exact two-coordinate integration over a measurable vertex partition. -/
theorem integral_partition_pair {n : ℕ} (P : VertexPartition n) (g : Fin n → Fin n → ℝ) :
    (∫ p : ℝ×ℝ, g (P.color p.1) (P.color p.2) ∂squareMeasure)=
      ∑ i, ∑ j, unitMeasure.real (P.fiber i)*unitMeasure.real (P.fiber j)*g i j := by
  have hf : Measurable (fun p : ℝ×ℝ => (P.color p.1,P.color p.2)) :=
    (P.measurable.comp measurable_fst).prodMk (P.measurable.comp measurable_snd)
  have hh := integral_finite_coloring squareMeasure _ hf (fun ij : Fin n×Fin n => g ij.1 ij.2)
  have hcell : ∀ ij : Fin n×Fin n,
      (fun p : ℝ×ℝ => (P.color p.1,P.color p.2)) ⁻¹' {ij}=P.fiber ij.1×ˢP.fiber ij.2 := by
    intro ij; ext p; simp [VertexPartition.fiber,Prod.ext_iff]
  simp_rw [hcell] at hh
  simpa only [Fintype.sum_prod_type,measureReal_def,Measure.prod_prod,ENNReal.toReal_mul] using hh

/-- Exact three-coordinate integration, without a graphon approximation hypothesis. -/
theorem integral_partition_triple {n : ℕ} (P : VertexPartition n)
    (g : Fin n → Fin n → Fin n → ℝ) :
    (∫ p : ℝ×(ℝ×ℝ), g (P.color p.1) (P.color p.2.1) (P.color p.2.2) ∂cubeMeasure)=
      ∑ i, ∑ j, ∑ k, unitMeasure.real (P.fiber i)*
        (unitMeasure.real (P.fiber j)*unitMeasure.real (P.fiber k))*g i j k := by
  have hf : Measurable (fun p : ℝ×(ℝ×ℝ) => (P.color p.1,(P.color p.2.1,P.color p.2.2))) :=
    (P.measurable.comp measurable_fst).prodMk
      ((P.measurable.comp (measurable_fst.comp measurable_snd)).prodMk
        (P.measurable.comp (measurable_snd.comp measurable_snd)))
  have hh := integral_finite_coloring cubeMeasure _ hf
    (fun ijk : Fin n×(Fin n×Fin n) => g ijk.1 ijk.2.1 ijk.2.2)
  have hcell : ∀ ijk : Fin n×(Fin n×Fin n),
      (fun p : ℝ×(ℝ×ℝ) => (P.color p.1,(P.color p.2.1,P.color p.2.2))) ⁻¹' {ijk}=
        P.fiber ijk.1×ˢ(P.fiber ijk.2.1×ˢP.fiber ijk.2.2) := by
    intro ijk; ext p; simp [VertexPartition.fiber,Prod.ext_iff]
  simp_rw [hcell] at hh
  simpa only [Fintype.sum_prod_type,measureReal_def,Measure.prod_prod,ENNReal.toReal_mul] using hh

/-- The actual step graphon of a symmetric unit-valued matrix. -/
def matrixStepGraphon {n : ℕ} (P : VertexPartition n) (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) : Graphon where
  toFun := matrixStepKernel P Z
  measurable := ((measurable_of_countable (fun ij : Fin n×Fin n => Z ij.1 ij.2)).comp
    ((P.measurable.comp measurable_fst).prodMk (P.measurable.comp measurable_snd))).aemeasurable
  symmetric := Eventually.of_forall (fun p => hsym (P.color p.2) (P.color p.1))
  bounded := Eventually.of_forall (fun p => hb (P.color p.1) (P.color p.2))

theorem matrixStepGraphon_cost {n : ℕ} (P : VertexPartition n) (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) :
    cost (matrixStepGraphon P Z hsym hb)=∑ i, ∑ j,
      unitMeasure.real (P.fiber i)*unitMeasure.real (P.fiber j)*entropy (Z i j) :=
  integral_partition_pair P (fun i j => entropy (Z i j))

theorem matrixStepGraphon_triangle {n : ℕ} (P : VertexPartition n) (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) :
    triangle (matrixStepGraphon P Z hsym hb)=∑ i, ∑ j, ∑ k,
      unitMeasure.real (P.fiber i)*(unitMeasure.real (P.fiber j)*unitMeasure.real (P.fiber k))*
        (Z i j*Z j k*Z i k) :=
  integral_partition_triple P (fun i j k => Z i j*Z j k*Z i k)

/-- Exact normalized entropy formula for the canonical n-interval step graphon. -/
theorem uniformStepGraphon_cost (n : ℕ) (hn : 0<n) (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) :
    cost (matrixStepGraphon (uniformVertexPartition n hn) Z hsym hb)=
      (∑ i, ∑ j, entropy (Z i j))/(n:ℝ)^2 := by
  rw [matrixStepGraphon_cost]
  simp_rw [uniformVertexPartition_mass]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- Exact normalized triangle formula for the canonical n-interval step graphon. -/
theorem uniformStepGraphon_triangle (n : ℕ) (hn : 0<n) (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1) :
    triangle (matrixStepGraphon (uniformVertexPartition n hn) Z hsym hb)=
      (∑ i, ∑ j, ∑ k, Z i j*Z j k*Z i k)/(n:ℝ)^3 := by
  rw [matrixStepGraphon_triangle]
  simp_rw [uniformVertexPartition_mass]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _; ring

/-- The zero diagonal contributes exactly 1/n to sparse entropy. -/
theorem uniformStepGraphon_cost_zero_diagonal (n : ℕ) (hn : 0<n) (Z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, Z i j=Z j i) (hb : ∀ i j, Z i j∈Icc (0:ℝ) 1)
    (hdiag : ∀ i, Z i i=0) :
    cost (matrixStepGraphon (uniformVertexPartition n hn) Z hsym hb)=
      (∑ i, ∑ j, if i=j then 0 else entropy (Z i j))/(n:ℝ)^2+1/(n:ℝ) := by
  rw [uniformStepGraphon_cost]
  have he : (∑ i, ∑ j, entropy (Z i j))=
      (∑ i, ∑ j, if i=j then 0 else entropy (Z i j))+(n:ℝ) := by
    have hh : ∀ i j, entropy (Z i j)=(if i=j then 0 else entropy (Z i j))+(if i=j then 1 else 0) := by
      intro i j; by_cases hij : i=j <;> simp [hij,hdiag]
    calc
      _ = ∑ i, ∑ j, ((if i=j then 0 else entropy (Z i j))+(if i=j then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _; exact hh i j
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [he,add_div]
  have hn' : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

end SparseLowerTail.Section03

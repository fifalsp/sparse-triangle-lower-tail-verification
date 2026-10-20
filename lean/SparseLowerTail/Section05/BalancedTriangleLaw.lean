import SparseLowerTail.Section05.TriangleLawSymmetry
import SparseLowerTail.Section02.Patterns
import SparseLowerTail.Section02.RelabelBalanced
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! The four-atom law of a balanced two-block graphon (`lem:patterns` part a). -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section05
open Section04 TriangleIntegration

/-- The exact expectation of every measurable test under the actual triangle law. -/
theorem integral_triangleLaw_balanced (a b : ℝ) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    {f : EdgeTriple → ℝ} (hf : Measurable f) :
    (∫ u,f u ∂triangleLaw (balancedGraphon a b ha hb))=
      (f ((a,a),a)+f ((a,b),b)+f ((b,a),b)+f ((b,b),a))/4 := by
  classical
  let U := balancedGraphon a b ha hb
  let K := |f ((a,a),a)|+|f ((a,b),b)|+|f ((b,a),b)|+|f ((b,b),a)|
  have hbound : BoundedObservable tripleMeasure (fun p=>f (edgeValues U p)) := by
    refine ⟨hf.comp_aemeasurable (edgeValues_aemeasurable U),K,by dsimp [K]; positivity,?_⟩
    apply Eventually.of_forall
    intro p
    change |f ((blockValue halfInterval a b (p.1.1,p.1.2),
      blockValue halfInterval a b (p.1.1,p.2)),blockValue halfInterval a b (p.1.2,p.2))|≤K
    by_cases hx:p.1.1∈halfInterval <;> by_cases hy:p.1.2∈halfInterval <;> by_cases hz:p.2∈halfInterval
    all_goals
      simp only [blockValue,hx,hy,hz,if_true,if_false]
      dsimp [K]
      linarith only [abs_nonneg (f ((a,a),a)),abs_nonneg (f ((a,b),b)),
        abs_nonneg (f ((b,a),b)),abs_nonneg (f ((b,b),a))]
  let R (p : ℝ × ℝ) := if (p.1∈halfInterval ↔ p.2∈halfInterval) then
    (f ((a,a),a)+f ((a,b),b))/2 else (f ((b,a),b)+f ((b,b),a))/2
  have inner (p : ℝ × ℝ) : (∫ z,f (edgeValues U (p,z)) ∂unitMeasure)=R p := by
    have he : (∫ z,f (edgeValues U (p,z)) ∂unitMeasure)=
        ((f ((U p,if p.1∈halfInterval then a else b),if p.2∈halfInterval then a else b))+
         (f ((U p,if p.1∈halfInterval then b else a),if p.2∈halfInterval then b else a)))/2 := by
      calc
        _ =∫ z,if z∈halfInterval then
            f ((U p,if p.1∈halfInterval then a else b),if p.2∈halfInterval then a else b)
          else f ((U p,if p.1∈halfInterval then b else a),if p.2∈halfInterval then b else a) ∂unitMeasure := by
          apply integral_congr_ae
          apply Eventually.of_forall
          intro z
          by_cases hx:p.1∈halfInterval <;> by_cases hy:p.2∈halfInterval <;> by_cases hz:z∈halfInterval
          all_goals simp [edgeValues,X,Y,Z,U,balancedGraphon,twoBlock,blockValue,hx,hy,hz]
        _ =_ := integral_half_partition halfInterval_measurable halfInterval_mass _ _
    rw [he]
    by_cases hx:p.1∈halfInterval <;> by_cases hy:p.2∈halfInterval
    all_goals simp [R,U,balancedGraphon,twoBlock,blockValue,hx,hy] <;> ring
  have hR : Integrable R squareMeasure := by
    convert hbound.integrable.integral_prod_left using 1
    funext p
    exact (inner p).symm
  rw [integral_triangleLaw _ hf]
  change (∫ p,f (edgeValues U p) ∂tripleMeasure)=_
  rw [integral_prod _ hbound.integrable]
  simp_rw [inner]
  rw [integral_prod _ hR]
  have middle (x:ℝ) : (∫ y,R (x,y) ∂unitMeasure)=
      (f ((a,a),a)+f ((a,b),b)+f ((b,a),b)+f ((b,b),a))/4 := by
    by_cases hx:x∈halfInterval
    · simp only [R,hx,true_iff]
      rw [integral_half_partition halfInterval_measurable halfInterval_mass]
      ring
    · simp only [R,hx,false_iff,ite_not]
      rw [integral_half_partition halfInterval_measurable halfInterval_mass]
      ring
  simp_rw [middle]
  simp

/-- The four-atom measure, including the case a=b where the atoms coincide. -/
def balancedTriangleAtoms (a b : ℝ) : Measure EdgeTriple :=
  (1/4:NNReal) • (Measure.dirac ((a,a),a)+Measure.dirac ((a,b),b)+
    Measure.dirac ((b,a),b)+Measure.dirac ((b,b),a))

instance (a b : ℝ) : IsFiniteMeasure (balancedTriangleAtoms a b) := by
  unfold balancedTriangleAtoms
  infer_instance

/-- The atomic integral formula needs no global measurability condition. -/
theorem integral_balancedTriangleAtoms (a b : ℝ) (f : EdgeTriple → ℝ) :
    (∫ u,f u ∂balancedTriangleAtoms a b)=
      (f ((a,a),a)+f ((a,b),b)+f ((b,a),b)+f ((b,b),a))/4 := by
  have hi (p:EdgeTriple) : Integrable f (Measure.dirac p) := integrable_dirac (by simp)
  unfold balancedTriangleAtoms
  rw [integral_smul_nnreal_measure,
    integral_add_measure (((hi _).add_measure (hi _)).add_measure (hi _)) (hi _),
    integral_add_measure ((hi _).add_measure (hi _)) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp only [integral_dirac]
  change ((1/4:NNReal):ℝ)*(f ((a,a),a)+f ((a,b),b)+f ((b,a),b)+f ((b,b),a))=_
  norm_num
  ring

/-- Equality of the actual pushforward probability measure with the four-atom law. -/
theorem triangleLaw_balanced_eq_atoms (a b : ℝ) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    triangleLaw (balancedGraphon a b ha hb)=balancedTriangleAtoms a b := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_triangleLaw_balanced a b ha hb f.continuous.measurable,integral_balancedTriangleAtoms]

/-- The finite law identifies every test defined only on its four support points. -/
theorem integral_triangleLaw_balanced_any (a b : ℝ) (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (f : EdgeTriple → ℝ) :
    (∫ u,f u ∂triangleLaw (balancedGraphon a b ha hb))=
      (f ((a,a),a)+f ((a,b),b)+f ((b,a),b)+f ((b,b),a))/4 := by
  rw [triangleLaw_balanced_eq_atoms,integral_balancedTriangleAtoms]

/-- A permutation-invariant test reduces to the two contact patterns, with weights 1/4 and 3/4. -/
theorem integral_triangleLaw_balanced_symmetric (a b : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (f : EdgeTriple → ℝ)
    (hs12 : f ((b,a),b)=f ((a,b),b)) (hs23 : f ((b,b),a)=f ((a,b),b)) :
    (∫ u,f u ∂triangleLaw (balancedGraphon a b ha hb))=
      f ((a,a),a)/4+3*f ((a,b),b)/4 := by
  rw [integral_triangleLaw_balanced_any,hs12,hs23]
  ring

/-- The permutation orbits of the two contact patterns are exactly these four points. -/
def twoBlockPatterns (a b : ℝ) : Set EdgeTriple :=
  {u | Section02.AllowedPattern a b u.1.1 u.1.2 u.2}

theorem measurableSet_twoBlockPatterns (a b : ℝ) : MeasurableSet (twoBlockPatterns a b) := by
  have hm (x y z:ℝ) : MeasurableSet {u:EdgeTriple | u.1.1=x ∧ u.1.2=y ∧ u.2=z} :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const).inter
      ((measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const).inter
        (measurableSet_eq_fun measurable_snd measurable_const))
  exact (hm _ _ _).union ((hm _ _ _).union ((hm _ _ _).union (hm _ _ _)))

/-- The actual triangle-law support and balanced mean force a measurable half partition. -/
theorem balanced_of_triangleLaw_twoBlockPatterns {a b : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hab:a≠b) {U:Graphon}
    (hp : ∀ᵐ u ∂triangleLaw U,u∈twoBlockPatterns a b) (he:edgeDensity U=(a+b)/2) :
    IsBalanced U a b := by
  have ht := (ae_map_iff (edgeValues_aemeasurable U) (measurableSet_twoBlockPatterns a b)).mp hp
  apply Section02.balanced_of_patterns ha hb hab _ he
  filter_upwards [ht] with p hp
  change Section02.AllowedPattern a b (X U p) (Z U p) (Y U p) at hp
  rcases hp with ⟨hx,hz,hy⟩ | ⟨hx,hz,hy⟩ | ⟨hx,hz,hy⟩ | ⟨hx,hz,hy⟩
  · exact Or.inl ⟨hx,hy,hz⟩
  · exact Or.inr (Or.inl ⟨hx,hy,hz⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hx,hy,hz⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hx,hy,hz⟩))

/-- `lem:patterns`(c), with the manuscript's mass-one hypothesis and actual relabeling conclusion. -/
theorem relabeling_of_triangleLaw_twoBlockPatterns (hCDF : Section02.ClassicalCDFTransport)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hab:a≠b) {U:Graphon}
    (hp : triangleLaw U (twoBlockPatterns a b)=1) (he:edgeDensity U=(a+b)/2) :
    Section02.IsBalancedRelabeling U a b ha hb := by
  apply (Section02.isBalanced_iff_relabel hCDF ha hb).mp
  apply balanced_of_triangleLaw_twoBlockPatterns ha hb hab _ he
  rw [ae_iff]
  change triangleLaw U (twoBlockPatterns a b)ᶜ=0
  rw [measure_compl (measurableSet_twoBlockPatterns a b) (measure_ne_top _ _),hp,measure_univ]
  norm_num

end SparseLowerTail.Section05

import SparseLowerTail.Section04.BipodalIntegral
import SparseLowerTail.Section04.BalancedMinimizers
import SparseLowerTail.Section04.EulerLagrange

/-!
# From actual two-block graphons to balanced minimizers

Stable anchors: `s4:eq:bipodal`, `s4:eq:bipsys`, `cor:bipodalmin`.
The general stationary interfaces keep the Euler and vertex identities explicit.
For minimizers the final interface discharges the Euler equation, positivity and
multiplier bounds; only the vertex identity remains to be supplied.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace SparseLowerTail.Section04
attribute [local instance] Classical.propDecidable

/-- Independent values on the two diagonal blocks and a common cross value. -/
def bipodalBlockValue (P : Set ℝ) (a d b : ℝ) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if p.1 ∈ P then (if p.2 ∈ P then a else b)
    else (if p.2 ∈ P then b else d)

def bipodalGraphon (P : Set ℝ) (hP : MeasurableSet P) (a d b : ℝ)
    (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) (hb : b ∈ Icc 0 1) : Graphon where
  toFun := bipodalBlockValue P a d b
  measurable := by
    classical
    exact ((measurable_const.ite (hP.preimage measurable_snd) measurable_const).ite
      (hP.preimage measurable_fst)
      (measurable_const.ite (hP.preimage measurable_snd) measurable_const)).aemeasurable
  symmetric := Filter.Eventually.of_forall fun p => by
    classical
    simp only [bipodalBlockValue, Prod.fst_swap, Prod.snd_swap]
    split_ifs <;> rfl
  bounded := Filter.Eventually.of_forall fun p => by
    classical
    simp only [bipodalBlockValue]
    split_ifs <;> assumption

/-- Actual measurable two-block form, including degenerate block masses. -/
def IsBipodal (U : Graphon) (c a d b : ℝ) : Prop :=
  c ∈ Icc 0 1 ∧ a ∈ Icc 0 1 ∧ d ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧
    ∃ P : Set ℝ, MeasurableSet P ∧ P ⊆ Icc 0 1 ∧
      unitMeasure P = ENNReal.ofReal c ∧ U.toFun =ᵐ[squareMeasure] bipodalBlockValue P a d b

theorem bipodalGraphon_isBipodal {P : Set ℝ} (hP : MeasurableSet P)
    (hsub : P ⊆ Icc (0 : ℝ) 1) {c : ℝ} (hc : c ∈ Icc 0 1)
    (hm : unitMeasure P = ENNReal.ofReal c) (a d b : ℝ)
    (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    IsBipodal (bipodalGraphon P hP a d b ha hd hb) c a d b :=
  ⟨hc,ha,hd,hb,P,hP,hsub,hm,Filter.EventuallyEq.rfl⟩

/-- The row-wise vertex identity, in its actual integral form. -/
def VertexIdentity (U : Graphon) : Prop :=
  ∃ k : ℝ, ∀ᵐ x ∂unitMeasure, (∫ y, vertexEntropy (U (x,y)) ∂unitMeasure) = k

theorem integral_partition {P : Set ℝ} (hP : MeasurableSet P)
    {c : ℝ} (hc : c ∈ Icc 0 1) (hm : unitMeasure P = ENNReal.ofReal c) (a b : ℝ) :
    (∫ x, (if x ∈ P then a else b) ∂unitMeasure) = c*a+(1-c)*b := by
  have hr : unitMeasure.real P = c := by simp [Measure.real, hm, ENNReal.toReal_ofReal hc.1]
  have hrc : unitMeasure.real Pᶜ = 1-c := by rw [measureReal_compl hP, measureReal_univ_eq_one, hr]
  have h := integral_piecewise (μ := unitMeasure) (f := fun _ => a) (g := fun _ => b)
    hP (integrable_const a).integrableOn (integrable_const b).integrableOn
  simpa [Set.piecewise, hr, hrc, smul_eq_mul] using h

private theorem partition_nonzero {P : Set ℝ} (hP : MeasurableSet P) {c : ℝ}
    (hc : c ∈ Ioo 0 1) (hm : unitMeasure P = ENNReal.ofReal c) :
    unitMeasure P ≠ 0 ∧ unitMeasure Pᶜ ≠ 0 := by
  constructor
  · rw [hm]
    exact (ENNReal.ofReal_pos.mpr hc.1).ne'
  · intro hn
    have hr := measureReal_compl (μ := unitMeasure) hP
    simp [Measure.real, hn, hm, ENNReal.toReal_ofReal hc.1.le] at hr
    linarith [hc.2]

/-- Positive block masses let a.e. scalar properties be read off on all blocks. -/
theorem bipodalBlockValue_ae_iff {P : Set ℝ} (hP : MeasurableSet P) {c : ℝ}
    (hc : c ∈ Ioo 0 1) (hm : unitMeasure P = ENNReal.ofReal c)
    (a d b : ℝ) (R : ℝ → Prop) :
    (∀ᵐ p ∂squareMeasure, R (bipodalBlockValue P a d b p)) ↔ R a ∧ R d ∧ R b := by
  classical
  constructor
  · intro h
    obtain ⟨hn, hcn⟩ := partition_nonzero hP hc hm
    have hh := Measure.ae_ae_of_ae_prod h
    obtain ⟨x, hx, hex⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn (ae_restrict_of_ae hh)
    obtain ⟨y, hy, hey⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn (ae_restrict_of_ae hex)
    obtain ⟨z, hz, hez⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcn (ae_restrict_of_ae hex)
    obtain ⟨u, hu, heu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcn (ae_restrict_of_ae hh)
    obtain ⟨v, hv, hev⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcn (ae_restrict_of_ae heu)
    have hzn : z ∉ P := hz
    have hun : u ∉ P := hu
    have hvn : v ∉ P := hv
    exact ⟨by simpa [bipodalBlockValue, hx, hy] using hey,
      by simpa [bipodalBlockValue, hun, hvn] using hev,
      by simpa [bipodalBlockValue, hx, hzn] using hez⟩
  · rintro ⟨ha, hd, hb⟩
    exact Filter.Eventually.of_forall fun p => by
      simp only [bipodalBlockValue]
      split_ifs <;> assumption

/-- General two-block codegrees, including unbalanced block masses. -/
theorem codegree_bipodalGraphon {P : Set ℝ} (hP : MeasurableSet P) {c : ℝ}
    (hc : c ∈ Icc 0 1) (hm : unitMeasure P = ENNReal.ofReal c)
    (a d b : ℝ) (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (x y : ℝ) :
    codegree (bipodalGraphon P hP a d b ha hd hb) x y =
      bipodalBlockValue P (c*a^2+(1-c)*b^2) (c*b^2+(1-c)*d^2)
        (b*(c*a+(1-c)*d)) (x,y) := by
  classical
  change (∫ z, bipodalBlockValue P a d b (x,z)*bipodalBlockValue P a d b (y,z) ∂unitMeasure) = _
  by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
  all_goals
    simp only [bipodalBlockValue, hx, hy, if_true, if_false]
    simp (config := {contextual := true}) only [mul_ite, if_true, if_false]
    rw [integral_partition hP hc hm]
    ring

theorem vertex_integral_bipodalGraphon {P : Set ℝ} (hP : MeasurableSet P)
    {c : ℝ} (hc : c ∈ Icc 0 1) (hm : unitMeasure P = ENNReal.ofReal c)
    (a d b : ℝ) (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (x : ℝ) :
    (∫ y, vertexEntropy (bipodalGraphon P hP a d b ha hd hb (x,y)) ∂unitMeasure) =
      if x ∈ P then c*vertexEntropy a+(1-c)*vertexEntropy b
      else c*vertexEntropy b+(1-c)*vertexEntropy d := by
  classical
  change (∫ y, vertexEntropy (bipodalBlockValue P a d b (x,y)) ∂unitMeasure) = _
  by_cases hx : x ∈ P
  all_goals
    simp only [bipodalBlockValue, hx, if_true, if_false, apply_ite vertexEntropy]
    exact integral_partition hP hc hm _ _

/-- Reading the graphon EL equation on each of the three positive-mass blocks. -/
theorem bipodalGraphon_scalar_EL {P : Set ℝ} (hP : MeasurableSet P) {c : ℝ}
    (hc : c ∈ Ioo 0 1) (hm : unitMeasure P = ENNReal.ofReal c)
    (a d b μ : ℝ) (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hel : ∀ᵐ p ∂squareMeasure, Real.log (bipodalGraphon P hP a d b ha hd hb p) =
      -μ*codegree (bipodalGraphon P hP a d b ha hd hb) p.1 p.2) :
    Real.log a = -μ*(c*a^2+(1-c)*b^2) ∧
    Real.log d = -μ*(c*b^2+(1-c)*d^2) ∧ Real.log b = -μ*b*(c*a+(1-c)*d) := by
  classical
  have hh : ∀ᵐ p ∂squareMeasure,
      bipodalBlockValue P (Real.log a+μ*(c*a^2+(1-c)*b^2))
        (Real.log d+μ*(c*b^2+(1-c)*d^2)) (Real.log b+μ*b*(c*a+(1-c)*d)) p = 0 := by
    filter_upwards [hel] with p hp
    rw [codegree_bipodalGraphon hP ⟨hc.1.le,hc.2.le⟩ hm] at hp
    change Real.log (bipodalBlockValue P a d b p) = _ at hp
    by_cases hx : p.1 ∈ P <;> by_cases hy : p.2 ∈ P
    all_goals simp [bipodalBlockValue, hx, hy] at hp ⊢
    all_goals nlinarith
  have h := (bipodalBlockValue_ae_iff hP hc hm _ _ _ (fun v => v=0)).mp hh
  exact ⟨by linarith [h.1], by linarith [h.2.1], by nlinarith [h.2.2]⟩

/-- The actual integral vertex identity gives the fourth scalar equation. -/
theorem bipodalGraphon_scalar_vertex {P : Set ℝ} (hP : MeasurableSet P) {c : ℝ}
    (hc : c ∈ Ioo 0 1) (hm : unitMeasure P = ENNReal.ofReal c)
    (a d b : ℝ) (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hv : VertexIdentity (bipodalGraphon P hP a d b ha hd hb)) :
    c*vertexEntropy a+(1-c)*vertexEntropy b = c*vertexEntropy b+(1-c)*vertexEntropy d := by
  classical
  obtain ⟨k, hk⟩ := hv
  obtain ⟨hn, hcn⟩ := partition_nonzero hP hc hm
  obtain ⟨x,hx,hex⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn (ae_restrict_of_ae hk)
  obtain ⟨y,hy,hey⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcn (ae_restrict_of_ae hk)
  have hyn : y ∉ P := hy
  rw [vertex_integral_bipodalGraphon hP ⟨hc.1.le,hc.2.le⟩ hm, if_pos hx] at hex
  rw [vertex_integral_bipodalGraphon hP ⟨hc.1.le,hc.2.le⟩ hm, if_neg hyn] at hey
  exact hex.trans hey.symm

theorem VertexIdentity.congr_ae {U W : Graphon} (heq : U.toFun =ᵐ[squareMeasure] W.toFun)
    (hv : VertexIdentity U) : VertexIdentity W := by
  obtain ⟨k,hk⟩ := hv
  refine ⟨k, ?_⟩
  filter_upwards [hk, Measure.ae_ae_of_ae_prod heq] with x hx hrow
  have hh : (fun y => vertexEntropy (W (x,y))) =ᵐ[unitMeasure]
      (fun y => vertexEntropy (U (x,y))) := hrow.mono fun y hy => congrArg vertexEntropy hy.symm
  exact (integral_congr_ae hh).trans hx

/-- The graphon identities imply the entire stationary scalar system. -/
theorem IsBipodal.stationary {U : Graphon} {c a d b μ : ℝ} (hB : IsBipodal U c a d b)
    (hc : c ∈ Ioo 0 1)
    (hel : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ*codegree U p.1 p.2)
    (hv : VertexIdentity U) : BipodalStationary c μ a d b := by
  obtain ⟨_,ha,hd,hb,P,hP,_,hm,heq⟩ := hB
  let W := bipodalGraphon P hP a d b ha hd hb
  have heqW : U.toFun =ᵐ[squareMeasure] W.toFun := heq
  have hELW := (ae_log_codegree_congr heqW μ).mp hel
  have hVW := hv.congr_ae heqW
  obtain ⟨h1,h2,h3⟩ := bipodalGraphon_scalar_EL hP hc hm a d b μ ha hd hb hELW
  exact ⟨h1,h2,h3,bipodalGraphon_scalar_vertex hP hc hm a d b ha hd hb hVW⟩

theorem IsBipodal.positive_values {U : Graphon} {c a d b : ℝ} (hB : IsBipodal U c a d b)
    (hc : c ∈ Ioo 0 1) (hpos : ∀ᵐ p ∂squareMeasure, 0 < U p) : 0<a ∧ 0<d ∧ 0<b := by
  obtain ⟨_,_,_,_,P,hP,_,hm,heq⟩ := hB
  apply (bipodalBlockValue_ae_iff hP hc hm a d b (fun v => 0<v)).mp
  filter_upwards [heq, hpos] with p hp hpp
  rwa [← hp]

/-- Nonconstant stationary two-block graphons have equal diagonal values and
balanced block masses. This uses the proved J lemma, not an assumption of it. -/
theorem IsBipodal.balanced_parameters {U : Graphon} {c a d b μ : ℝ}
    (hB : IsBipodal U c a d b) (hc : c ∈ Ioo 0 1) (hμ : 0<μ)
    (hpos : ∀ᵐ p ∂squareMeasure, 0<U p) (hne : ¬(a=b ∧ d=b))
    (hel : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ*codegree U p.1 p.2)
    (hv : VertexIdentity U) : a=d ∧ a<b ∧ c=1/2 := by
  obtain ⟨ha,hd,hb⟩ := hB.positive_values hc hpos
  exact bipodal_rigidity hc hμ ha hd hb hne (hB.stationary hc hel hv)

theorem isBalanced_of_isConstant {U : Graphon} {t : ℝ} (hU : IsConstant U t) :
    IsBalanced U t t := by
  refine ⟨halfInterval,halfInterval_measurable,halfInterval_subset,halfInterval_mass,?_⟩
  filter_upwards [hU] with p hp
  simpa using hp

theorem IsBipodal.constant_of_mass_zero {U : Graphon} {c a d b : ℝ}
    (hB : IsBipodal U c a d b) (hc : c=0) : IsConstant U d := by
  obtain ⟨_,_,_,_,P,hP,_,hm,heq⟩ := hB
  have hn : unitMeasure P = 0 := by simpa [hc] using hm
  have hae := measure_eq_zero_iff_ae_notMem.mp hn
  filter_upwards [heq, Measure.quasiMeasurePreserving_fst.ae hae,
    Measure.quasiMeasurePreserving_snd.ae hae] with p hp hx hy
  change p.1 ∉ P at hx
  change p.2 ∉ P at hy
  simpa [bipodalBlockValue,hx,hy] using hp

theorem IsBipodal.constant_of_mass_one {U : Graphon} {c a d b : ℝ}
    (hB : IsBipodal U c a d b) (hc : c=1) : IsConstant U a := by
  obtain ⟨_,_,_,_,P,hP,_,hm,heq⟩ := hB
  have hn : unitMeasure Pᶜ = 0 := by
    rw [measure_compl hP (measure_ne_top _ _),hm,hc,measure_univ]
    norm_num
  have hae : ∀ᵐ x ∂unitMeasure, x ∈ P := by
    simpa using measure_eq_zero_iff_ae_notMem.mp hn
  filter_upwards [heq, Measure.quasiMeasurePreserving_fst.ae hae,
    Measure.quasiMeasurePreserving_snd.ae hae] with p hp hx hy
  change p.1 ∈ P at hx
  change p.2 ∈ P at hy
  simpa [bipodalBlockValue,hx,hy] using hp

theorem IsBipodal.constant_of_all_equal {U : Graphon} {c a d b : ℝ}
    (hB : IsBipodal U c a d b) (ha : a=b) (hd : d=b) : IsConstant U b := by
  obtain ⟨_,_,_,_,P,_,_,_,heq⟩ := hB
  filter_upwards [heq] with p hp
  simpa [bipodalBlockValue,ha,hd] using hp

theorem IsBipodal.isBalanced_of_parameters {U : Graphon} {c a d b : ℝ}
    (hB : IsBipodal U c a d b) (had : a=d) (hc : c=1/2) : IsBalanced U a b := by
  obtain ⟨_,_,_,_,P,hP,hsub,hm,heq⟩ := hB
  refine ⟨P,hP,hsub,?_,?_⟩
  · rw [hc] at hm
    simpa using hm
  · filter_upwards [heq] with p hp
    rw [hp,← had]
    by_cases hx : p.1 ∈ P <;> by_cases hy : p.2 ∈ P
    all_goals simp [bipodalBlockValue,hx,hy]

/-- All stationary positive two-block graphons are balanced or constant;
constants are included as diagonal balanced forms. Degenerate masses are
handled explicitly, so the statement covers every two-block representation. -/
theorem IsBipodal.exists_balanced {U : Graphon} {c a d b μ : ℝ}
    (hB : IsBipodal U c a d b) (hμ : 0<μ)
    (hpos : ∀ᵐ p ∂squareMeasure, 0<U p)
    (hel : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ*codegree U p.1 p.2)
    (hv : VertexIdentity U) : ∃ a' b' : ℝ, IsBalanced U a' b' := by
  by_cases hc0 : c=0
  · exact ⟨d,d,isBalanced_of_isConstant (hB.constant_of_mass_zero hc0)⟩
  by_cases hc1 : c=1
  · exact ⟨a,a,isBalanced_of_isConstant (hB.constant_of_mass_one hc1)⟩
  by_cases heq : a=b ∧ d=b
  · exact ⟨b,b,isBalanced_of_isConstant (hB.constant_of_all_equal heq.1 heq.2)⟩
  have hc : c ∈ Ioo 0 1 := by
    constructor
    · exact lt_of_le_of_ne hB.1.1 (Ne.symm hc0)
    · exact lt_of_le_of_ne hB.1.2 hc1
  obtain ⟨had,_,hhalf⟩ := hB.balanced_parameters hc hμ hpos heq hel hv
  exact ⟨a,b,hB.isBalanced_of_parameters had hhalf⟩

/-- `cor:bipodalmin`, after the actual graphon Euler and vertex identities.
The latter are explicit analytic premises until their variation proofs have
been connected; bipodal rigidity and the scalar phase classification are proved. -/
theorem bipodal_minimizer_below_threshold {r c a d b μ : ℝ} {U : Graphon}
    (hr : r ∈ Ioo (0 : ℝ) threshold) (hmin : IsMinimizer r U)
    (hB : IsBipodal U c a d b) (hμ : 0<μ)
    (hpos : ∀ᵐ p ∂squareMeasure, 0<U p)
    (hel : ∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ*codegree U p.1 p.2)
    (hv : VertexIdentity U) :
    IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) ∧ value r=balancedValue r := by
  obtain ⟨a',b',hb⟩ := hB.exists_balanced hμ hpos hel hv
  obtain ⟨ha',hb',hval⟩ := balanced_minimizer_below_threshold hr hmin hb
  exact ⟨by simpa only [ha',hb'] using hb,hval⟩

/-- The graphon first-order equation and its bounds are proved, leaving only
the vertex-variation identity to connect in `cor:bipodalmin`. -/
theorem bipodal_minimizer_of_vertex_identity {r c a d b : ℝ} {U : Graphon}
    (hr : r ∈ Ioo (0 : ℝ) threshold) (hmin : IsMinimizer r U)
    (hB : IsBipodal U c a d b) (hv : VertexIdentity U) :
    IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) ∧
      value r = balancedValue r := by
  have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans threshold_mem_Ioo.2⟩
  exact bipodal_minimizer_below_threshold hr hmin hB
    (minimizer_multiplier_pos hr01 hmin) (minimizer_pos_ae hr01 hmin)
    (minimizer_log_equation hr01 hmin) hv

end SparseLowerTail.Section04

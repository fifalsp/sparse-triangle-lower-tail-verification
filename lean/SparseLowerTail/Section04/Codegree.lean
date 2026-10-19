import SparseLowerTail.Balanced

/-!
# Codegrees of the balanced two-block graphon

Paper anchors: `lem:Bcodegree` and the paragraph leading to
`s4:eq:EL`. The proofs apply to every measurable partition of mass one half.
The Euler–Lagrange bridge assumes positive block values: Lean's total real
logarithm at zero is not the paper's extended-real logarithm.
-/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail
attribute [local instance] Classical.propDecidable

/-- The codegree kernel, integrated against Lebesgue probability on `[0,1]`. -/
def codegree (U : Graphon) (x y : ℝ) : ℝ :=
  ∫ z, U (x,z) * U (y,z) ∂unitMeasure

/-- `lem:Bcodegree`: codegrees of a balanced two-block graphon. -/
theorem codegree_twoBlock {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P = (1 / 2 : ENNReal)) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (x y : ℝ) :
    codegree (twoBlock P hP a b ha hb) x y =
      if (x ∈ P ↔ y ∈ P) then (a^2+b^2)/2 else a*b := by
  classical
  change (∫ z, blockValue P a b (x,z) * blockValue P a b (y,z)
    ∂unitMeasure) = _
  by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
  all_goals
    simp only [blockValue, hx, hy, if_true, if_false]
    simp (config := { contextual := true }) only
      [mul_ite, if_true, if_false, true_iff, false_iff, not_true_eq_false]
  all_goals
    rw [integral_half_partition hP hm]; ring

/-- The pointwise logarithmic equation follows from its two scalar equations. -/
theorem twoBlock_log_equation_of_scalar {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P = (1 / 2 : ENNReal)) (a b μ : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hel : Real.log a = -μ*((a^2+b^2)/2) ∧ Real.log b = -μ*a*b)
    (x y : ℝ) :
    Real.log (twoBlock P hP a b ha hb (x,y)) =
      -μ * codegree (twoBlock P hP a b ha hb) x y := by
  classical
  rw [codegree_twoBlock hP hm]
  change Real.log (blockValue P a b (x,y)) = _
  by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
  all_goals simp [blockValue, hx, hy]
  all_goals first | simpa [mul_assoc] using hel.1 | simpa [mul_assoc] using hel.2

/-- An almost-everywhere logarithmic equation on two positive blocks is
exactly the pair of scalar equations `s4:eq:EL`. Positivity is kept explicit
because this theorem represents the paper's logarithmic Euler equation. -/
theorem twoBlock_ae_log_equation_iff {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P = (1 / 2 : ENNReal)) (a b μ : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (_ha_pos : 0 < a) (_hb_pos : 0 < b) :
    (∀ᵐ p ∂squareMeasure, Real.log (twoBlock P hP a b ha hb p) =
      -μ * codegree (twoBlock P hP a b ha hb) p.1 p.2) ↔
      Real.log a = -μ*((a^2+b^2)/2) ∧ Real.log b = -μ*a*b := by
  classical
  constructor
  · intro hel
    have hn : unitMeasure P ≠ 0 := by rw [hm]; norm_num
    have hc : unitMeasure Pᶜ = (1/2 : ENNReal) := by
      rw [measure_compl hP (measure_ne_top _ _), measure_univ, hm]
      norm_num
    have hcn : unitMeasure Pᶜ ≠ 0 := by rw [hc]; norm_num
    obtain ⟨x, hx, hex⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn
      (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hel))
    obtain ⟨y, hy, hey⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn
      (ae_restrict_of_ae hex)
    obtain ⟨z, hz, hez⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcn
      (ae_restrict_of_ae hex)
    have hznot : z ∉ P := hz
    constructor
    · rw [codegree_twoBlock hP hm] at hey
      change Real.log (blockValue P a b (x,y)) = _ at hey
      simpa [blockValue, hx, hy] using hey
    · rw [codegree_twoBlock hP hm] at hez
      change Real.log (blockValue P a b (x,z)) = _ at hez
      simpa [blockValue, hx, hznot, mul_assoc] using hez
  · intro hel
    exact Filter.Eventually.of_forall fun p =>
      twoBlock_log_equation_of_scalar hP hm a b μ ha hb hel p.1 p.2

/-- Codegrees are unchanged almost everywhere when representatives are changed
on a null set. This permits using the block formula for `IsBalanced` graphons. -/
theorem codegree_congr_ae {U W : Graphon}
    (heq : U.toFun =ᵐ[squareMeasure] W.toFun) :
    (fun p : ℝ × ℝ => codegree U p.1 p.2) =ᵐ[squareMeasure]
      (fun p : ℝ × ℝ => codegree W p.1 p.2) := by
  have hf := Measure.ae_ae_of_ae_prod heq
  have hx : ∀ᵐ p : ℝ × ℝ ∂squareMeasure, ∀ᵐ z ∂unitMeasure,
      U (p.1,z) = W (p.1,z) := Measure.quasiMeasurePreserving_fst.ae hf
  have hy : ∀ᵐ p : ℝ × ℝ ∂squareMeasure, ∀ᵐ z ∂unitMeasure,
      U (p.2,z) = W (p.2,z) := Measure.quasiMeasurePreserving_snd.ae hf
  filter_upwards [hx, hy] with p hpx hpy
  apply integral_congr_ae
  filter_upwards [hpx, hpy] with z hzx hzy
  rw [hzx, hzy]

/-- The logarithmic codegree equation is invariant under null-set changes. -/
theorem ae_log_codegree_congr {U W : Graphon}
    (heq : U.toFun =ᵐ[squareMeasure] W.toFun) (μ : ℝ) :
    (∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ * codegree U p.1 p.2) ↔
      ∀ᵐ p ∂squareMeasure, Real.log (W p) = -μ * codegree W p.1 p.2 := by
  have hc := codegree_congr_ae heq
  constructor
  · intro h
    filter_upwards [h, heq, hc] with p hp hUp hcp
    simpa only [← hUp, ← hcp] using hp
  · intro h
    filter_upwards [h, heq, hc] with p hp hUp hcp
    simpa only [hUp, hcp] using hp

/-- The scalar Euler equations characterize the a.e. equation for every balanced
representative, not just the constructed step-function representative. -/
theorem IsBalanced.ae_log_equation_iff {U : Graphon} {a b : ℝ}
    (hU : IsBalanced U a b) (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (μ : ℝ) :
    (∀ᵐ p ∂squareMeasure, Real.log (U p) = -μ * codegree U p.1 p.2) ↔
      Real.log a = -μ*((a^2+b^2)/2) ∧ Real.log b = -μ*a*b := by
  obtain ⟨P, hP, hm, heq⟩ := hU.exists_twoBlock ha hb
  rw [ae_log_codegree_congr heq μ]
  exact twoBlock_ae_log_equation_iff hP hm a b μ ha hb ha_pos hb_pos

end SparseLowerTail

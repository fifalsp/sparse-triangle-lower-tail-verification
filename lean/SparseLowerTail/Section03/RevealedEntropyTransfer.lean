import SparseLowerTail.Section03.RevealedCostConcentration

/-! Averaged entropy transfer from the actual conditional product marginals to the actual law. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a normalized Boolean law, its product marginals are the Bernoulli product with its actual means. -/
theorem productMarginals_eq_productBernoulliMass {ν : Type*} [Fintype ν] [DecidableEq ν]
    (m : (ν → Bool) → ℝ) (hm : ∑ z, m z=1) :
    productMarginals m=productBernoulliMass (fun i => finiteMarginal m (fun z => z i) true) := by
  funext z
  unfold productMarginals productBernoulliMass finiteProductMass
  apply Finset.prod_congr rfl
  intro i _
  have hh := finiteMarginal_sum m (fun z => z i)
  rw [hm] at hh
  simp only [Fintype.sum_bool] at hh
  have hf : finiteMarginal m (fun z => z i) false=1-finiteMarginal m (fun z => z i) true := by linarith
  cases hz : z i <;> simp [bernoulliMass,hf]

/-- An event whose unrevealed-coordinate section is allowed to depend on the revealed pattern. -/
def revealedFamilyEvent (W : Finset ι) (E : (W → Bool) → Finset (↑Wᶜ → Bool)) : Finset (ι → Bool) :=
  Finset.univ.filter (fun z => (splitCoordinates W z).2∈E (splitCoordinates W z).1)

/-- Exact disintegration of the original finite law across its actual revealed patterns. -/
theorem revealedFamilyEvent_mass (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z)
    (W : Finset ι) (E : (W → Bool) → Finset (↑Wᶜ → Bool)) :
    finiteEventMass q (revealedFamilyEvent W E) =
      ∑ y : W → Bool, revealedPatternMass q W y*finiteEventMass (unrevealedConditionalLaw q W y) (E y) := by
  classical
  have hfactor : ∀ (y : W → Bool) (z : ↑Wᶜ → Bool),
      revealedPatternMass q W y*unrevealedConditionalLaw q W y z=q ((splitCoordinates W).symm (y,z)) := by
    intro y z
    unfold unrevealedConditionalLaw
    rw [← splitCoordinates_rowMass W q y]
    exact finiteConditional_factor _ (fun _ _ => hq _) y z
  unfold finiteEventMass revealedFamilyEvent
  rw [Finset.sum_filter]
  have he := (splitCoordinates W).symm.sum_comp
    (fun z => if (splitCoordinates W z).2∈E (splitCoordinates W z).1 then q z else 0)
  simp only [Equiv.apply_symm_apply] at he
  rw [← he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  calc
    _ = ∑ z∈E y, q ((splitCoordinates W).symm (y,z)) := by
      simp only [Finset.sum_ite_mem,Finset.univ_inter]
    _ = _ := Finset.sum_congr rfl (fun z _ => (hfactor y z).symm)

/-- An exponential bound under the product marginals transfers to the actual conditional law. -/
theorem unrevealedConditionalLaw_event_exp_bound (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z)
    (W : Finset ι) (y : W → Bool) (hy : 0<revealedPatternMass q W y)
    (E : Finset (↑Wᶜ → Bool)) {c : ℝ} (hc : 0<c)
    (hproduct : finiteEventMass (productMarginals (unrevealedConditionalLaw q W y)) E≤Real.exp (-c)) :
    finiteEventMass (unrevealedConditionalLaw q W y) E≤
      (finiteRelativeEntropy (unrevealedConditionalLaw q W y)
        (productMarginals (unrevealedConditionalLaw q W y))+Real.log 2)/c := by
  let ν := unrevealedConditionalLaw q W y
  have hν : ∀ z, 0≤ν z := unrevealedConditionalLaw_nonneg q hq W y
  have hνsum : ∑ z, ν z=1 := unrevealedConditionalLaw_sum q W y hy
  have hprod : ∀ z, 0≤productMarginals ν z := productMarginals_nonneg ν hν
  have hu : 0≤finiteEventMass (productMarginals ν) E := Finset.sum_nonneg (fun z _ => hprod z)
  have hD : 0≤finiteRelativeEntropy ν (productMarginals ν) := unrevealedConditionalLaw_dependence_nonneg q hq W y
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hzero : finiteEventMass (productMarginals ν) E=0
  · have hh := finite_event_probability_zero ν (productMarginals ν) hprod (productMarginals_support ν hν) E hzero
    change finiteEventMass ν E≤_
    rw [show finiteEventMass ν E=0 from hh]
    exact div_nonneg (add_nonneg hD hlog2) hc.le
  · have hu0 : 0<finiteEventMass (productMarginals ν) E := lt_of_le_of_ne hu (Ne.symm hzero)
    have hu1 : finiteEventMass (productMarginals ν) E<1 :=
      hproduct.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))
    have hlog : c≤Real.log (1/finiteEventMass (productMarginals ν) E) := by
      have hh := Real.log_le_log hu0 hproduct
      rw [Real.log_exp] at hh
      rw [one_div,Real.log_inv]
      linarith
    have hh := finite_event_probability_le ν (productMarginals ν) hν hprod hνsum
      (productMarginals_sum ν hνsum) (productMarginals_support ν hν) E ⟨hu0,hu1⟩
    exact hh.trans (div_le_div_of_nonneg_left (add_nonneg hD hlog2) hc hlog)

/-- Averaging the transferred bound over the actual revealed-pattern probabilities. -/
theorem revealed_event_exp_bound (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z) (hqsum : ∑ z, q z=1)
    (W : Finset ι) (E : (W → Bool) → Finset (↑Wᶜ → Bool)) {c : ℝ} (hc : 0<c)
    (hproduct : ∀ y, 0<revealedPatternMass q W y →
      finiteEventMass (productMarginals (unrevealedConditionalLaw q W y)) (E y)≤Real.exp (-c)) :
    (∑ y : W → Bool, revealedPatternMass q W y*finiteEventMass (unrevealedConditionalLaw q W y) (E y))≤
      ((∑ y : W → Bool, revealedPatternMass q W y*finiteRelativeEntropy (unrevealedConditionalLaw q W y)
        (productMarginals (unrevealedConditionalLaw q W y)))+Real.log 2)/c := by
  have hμ : ∀ y : W → Bool, 0≤revealedPatternMass q W y := fun y => Finset.sum_nonneg (fun z _ => hq z)
  have hμsum : ∑ y : W → Bool, revealedPatternMass q W y=1 := by rw [revealedPatternMass_sum,hqsum]
  have hpoint : ∀ y : W → Bool,
      revealedPatternMass q W y*finiteEventMass (unrevealedConditionalLaw q W y) (E y)≤
      revealedPatternMass q W y*((finiteRelativeEntropy (unrevealedConditionalLaw q W y)
        (productMarginals (unrevealedConditionalLaw q W y))+Real.log 2)/c) := by
    intro y
    by_cases hy : revealedPatternMass q W y=0
    · simp [hy]
    · have hypos := lt_of_le_of_ne (hμ y) (Ne.symm hy)
      exact mul_le_mul_of_nonneg_left (unrevealedConditionalLaw_event_exp_bound q hq W y hypos (E y) hc (hproduct y hypos)) (hμ y)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hpoint y)
  convert hh using 1
  simp_rw [← mul_div_assoc,mul_add]
  rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.sum_mul,hμsum,one_mul]

/-- The original event probability inherits the averaged conditional entropy-transfer bound. -/
theorem revealedFamilyEvent_exp_bound (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z) (hqsum : ∑ z, q z=1)
    (W : Finset ι) (E : (W → Bool) → Finset (↑Wᶜ → Bool)) {c : ℝ} (hc : 0<c)
    (hproduct : ∀ y, 0<revealedPatternMass q W y →
      finiteEventMass (productMarginals (unrevealedConditionalLaw q W y)) (E y)≤Real.exp (-c)) :
    finiteEventMass q (revealedFamilyEvent W E)≤
      ((∑ y : W → Bool, revealedPatternMass q W y*finiteRelativeEntropy (unrevealedConditionalLaw q W y)
        (productMarginals (unrevealedConditionalLaw q W y)))+Real.log 2)/c := by
  rw [revealedFamilyEvent_mass q hq W E]
  exact revealed_event_exp_bound q hq hqsum W E hc hproduct

/-- The constant 384 in the cut-error probability estimate, with the actual conditional-law entropy. -/
theorem revealedFamilyEvent_cut_transfer (q : (ι → Bool) → ℝ) (hq : ∀ z, 0≤q z) (hqsum : ∑ z, q z=1)
    (W : Finset ι) (E : (W → Bool) → Finset (↑Wᶜ → Bool)) {ε v ω : ℝ} (hε : 0<ε) (hv : 0<v)
    (hproduct : ∀ y, 0<revealedPatternMass q W y →
      finiteEventMass (productMarginals (unrevealedConditionalLaw q W y)) (E y)≤Real.exp (-(ε^2*v/256)))
    (hD : (∑ y : W → Bool, revealedPatternMass q W y*finiteRelativeEntropy (unrevealedConditionalLaw q W y)
      (productMarginals (unrevealedConditionalLaw q W y)))≤ω*v/2)
    (hlog : Real.log 2≤ω*v) : finiteEventMass q (revealedFamilyEvent W E)≤384*ω/ε^2 := by
  have hc : 0<ε^2*v/256 := div_pos (mul_pos (sq_pos_of_pos hε) hv) (by norm_num)
  have hh := revealedFamilyEvent_exp_bound q hq hqsum W E hc hproduct
  calc
    _≤_ := hh
    _≤(ω*v/2+ω*v)/(ε^2*v/256) := div_le_div_of_nonneg_right (add_le_add hD hlog) hc.le
    _=384*ω/ε^2 := by field_simp [hε.ne',hv.ne']; ring


end SparseLowerTail.Section03

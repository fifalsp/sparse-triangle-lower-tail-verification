import SparseLowerTail.Section02.Push
import SparseLowerTail.Section04.BalancedPhase
import SparseLowerTail.Section02.RelabelBalanced

/-!
# Reduction of the full threshold theorem to the critical classification

Manuscript `thm:threshold`, conditional only on the explicit internal proposition
`CriticalClassification` corresponding to `prop:critical`. That proposition is
not declared as an axiom and is not proved in this file. Below-threshold strict
improvement is unconditional. The balanced classification uses measurable
half-partitions, as in the repository's definition of `IsBalanced`.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section05
open Section02 Section04

/-- Within-block value of the critical balanced graphon. -/
def criticalA : ℝ := branchA transitionParameter
/-- Between-block value of the critical balanced graphon. -/
def criticalB : ℝ := branchB transitionParameter

/-- Exact internal obligation `prop:critical`; this is a proposition, not an axiom. -/
def CriticalClassification : Prop :=
  value threshold = entropy threshold ∧
  ∀ U : Graphon, IsMinimizer threshold U →
    IsConstant U threshold ∨ IsBalanced U criticalA criticalB

theorem critical_pair_minimizer : IsBalancedMinimizer threshold criticalA criticalB := by
  rw [threshold_eq_transitionTarget]
  exact (balancedMinimizer_at_transition _ _).mpr (Or.inr ⟨rfl, rfl⟩)

theorem critical_pair_bounds : criticalA ∈ Icc (0:ℝ) 1 ∧ criticalB ∈ Icc (0:ℝ) 1 :=
  ⟨critical_pair_minimizer.1.1, critical_pair_minimizer.1.2.1⟩

theorem critical_pair_cost : balancedCost criticalA criticalB = entropy threshold := by
  have h := (isBalancedMinimizer_iff.mp critical_pair_minimizer).2
  rw [threshold_eq_transitionTarget, balancedValue_at_transition] at h
  simpa only [threshold_eq_transitionTarget] using h

theorem critical_pair_triangle : balancedTriangle criticalA criticalB = threshold^3 := by
  change balancedTriangle (branchA transitionParameter) (branchB transitionParameter) = threshold^3
  rw [branch_eq_scaled_ray transitionParameter_mem_Ioo.1 |>.1,
    branch_eq_scaled_ray transitionParameter_mem_Ioo.1 |>.2,
    scaled_ray_triangle transitionParameter_mem_Ioo.1,
    branchRho_transitionParameter, ← threshold_eq_transitionTarget]

/-- Every balanced critical graphon has the actual integral cost and density claimed. -/
theorem critical_balanced_integrals {U : Graphon} (hU : IsBalanced U criticalA criticalB) :
    triangle U = threshold^3 ∧ cost U = entropy threshold := by
  exact ⟨(hU.triangle_eq critical_pair_bounds.1 critical_pair_bounds.2).trans critical_pair_triangle,
    (hU.cost_eq critical_pair_bounds.1 critical_pair_bounds.2).trans critical_pair_cost⟩

/-- Any a.e. constant representative has the expected cost and triangle density. -/
theorem constant_integrals {U : Graphon} {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1)
    (hU : IsConstant U r) : triangle U = r^3 ∧ cost U = entropy r := by
  exact ⟨(triangle_congr_ae (W := constant r hr) hU).trans (triangle_constant r hr),
    (cost_congr_ae (W := constant r hr) hU).trans (cost_constant r hr)⟩

/-- Above the threshold, even a feasible competitor costing at most h(r) must be constant. -/
theorem feasible_low_cost_constant_above (hcrit : CriticalClassification)
    {r : ℝ} (hr : r ∈ Ioo threshold 1) {U : Graphon}
    (hf : Feasible r U) (hc : cost U ≤ entropy r) : IsConstant U r := by
  have hr0 : 0 < r := threshold_mem_Ioo.1.trans hr.1
  have hn : ∃ c, IsConstant U c := by
    by_contra hn
    have h := push_value threshold_mem_Ioo.1 hr.1 hr.2 hf hc hn
    exact (ne_of_lt h) hcrit.1
  obtain ⟨c, hconst⟩ := hn
  have he := constant_of_cost_le_target ⟨hr0, hr.2⟩ hconst hf hc
  simpa only [he] using hconst

/-- Every feasible graphon costs at least h(r) above threshold. -/
theorem cost_lower_above (hcrit : CriticalClassification)
    {r : ℝ} (hr : r ∈ Ioo threshold 1) {U : Graphon} (hf : Feasible r U) :
    entropy r ≤ cost U := by
  by_cases hc : cost U ≤ entropy r
  · exact (constant_integrals ⟨(threshold_mem_Ioo.1.trans hr.1).le, hr.2.le⟩
      (feasible_low_cost_constant_above hcrit hr hf hc)).2.ge
  · exact le_of_lt (lt_of_not_ge hc)

/-- `thm:threshold`(i), value assertion, without assuming attainment. -/
theorem value_eq_entropy_above (hcrit : CriticalClassification)
    {r : ℝ} (hr : r ∈ Ioo threshold 1) : value r = entropy r := by
  have hr01 : r ∈ Icc (0:ℝ) 1 := ⟨(threshold_mem_Ioo.1.trans hr.1).le, hr.2.le⟩
  apply le_antisymm (value_le_entropy hr01)
  apply le_csInf
    (show {v | ∃ U : Graphon, Feasible r U ∧ cost U = v}.Nonempty from
      ⟨_, constant r hr01, constant_feasible r hr01, rfl⟩)
  rintro v ⟨U, hf, rfl⟩
  exact cost_lower_above hcrit hr hf

/-- `thm:threshold`(i), uniqueness up to a.e. equality, and its converse. -/
theorem minimizer_above_iff (hcrit : CriticalClassification)
    {r : ℝ} (hr : r ∈ Ioo threshold 1) (U : Graphon) :
    IsMinimizer r U ↔ IsConstant U r := by
  constructor
  · intro hm
    exact feasible_low_cost_constant_above hcrit hr hm.1
      ((isMinimizer_iff.mp hm).2.trans (value_eq_entropy_above hcrit hr)).le
  · intro hc
    obtain ⟨ht, he⟩ := constant_integrals
      ⟨(threshold_mem_Ioo.1.trans hr.1).le, hr.2.le⟩ hc
    exact isMinimizer_iff.mpr ⟨ht.le, he.trans (value_eq_entropy_above hcrit hr).symm⟩

/-- `thm:threshold`(ii); both converse cases use the actual graphon integrals. -/
theorem minimizer_at_iff (hcrit : CriticalClassification) (U : Graphon) :
    IsMinimizer threshold U ↔ IsConstant U threshold ∨ IsBalanced U criticalA criticalB := by
  constructor
  · exact hcrit.2 U
  · intro hc
    have hi : triangle U = threshold^3 ∧ cost U = entropy threshold := by
      rcases hc with hc | hb
      · exact constant_integrals ⟨threshold_mem_Ioo.1.le, threshold_mem_Ioo.2.le⟩ hc
      · exact critical_balanced_integrals hb
    exact isMinimizer_iff.mpr ⟨hi.1.le, hi.2.trans hcrit.1.symm⟩

/-- The literal critical optimizer clause, with an actual measure-preserving
relabeling. The author-owned critical classification remains the same input. -/
theorem minimizer_at_relabeling_iff (hcrit : CriticalClassification)
    (hCDF : ClassicalCDFTransport) (U : Graphon) :
    IsMinimizer threshold U ↔ IsConstant U threshold ∨
      IsBalancedRelabeling U criticalA criticalB critical_pair_bounds.1
        critical_pair_bounds.2 := by
  rw [minimizer_at_iff hcrit U,
    isBalanced_iff_relabel hCDF critical_pair_bounds.1 critical_pair_bounds.2]

/-- `thm:threshold`(iii): unrestricted strict improvement below the threshold. -/
theorem value_lt_entropy_below {r : ℝ} (hr : r ∈ Ioo (0:ℝ) threshold) :
    value r ≤ balancedValue r ∧ balancedValue r < entropy r := by
  have hr1 : r < 1 := hr.2.trans threshold_mem_Ioo.2
  exact ⟨value_le_balancedValue ⟨hr.1.le, hr1.le⟩,
    (balanced_strict_improvement_iff_threshold ⟨hr.1, hr1⟩).mpr hr.2⟩

/-- The strict comparison is witnessed by the actual balanced branch graphon. -/
theorem branch_graphon_improves_below {r : ℝ} (hr : r ∈ Ioo (0:ℝ) threshold) :
    ∃ U : Graphon, IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) ∧
      triangle U = r^3 ∧ cost U = balancedValue r ∧
      value r ≤ cost U ∧ cost U < entropy r := by
  have hrt : r ∈ Ioo (0:ℝ) transitionTarget := by
    simpa only [threshold_eq_transitionTarget] using hr
  have hm := (balancedMinimizer_below_transition hrt _ _).mpr ⟨rfl, rfl⟩
  let U := balancedGraphon (branchA (leftBranch r)) (branchB (leftBranch r)) hm.1.1 hm.1.2.1
  have he : cost U = balancedValue r := by
    rw [show cost U = balancedCost _ _ from cost_balancedGraphon _ _ _ _]
    exact (isBalancedMinimizer_iff.mp hm).2
  have hz := leftBranch_mem_unit ⟨hrt.1, hrt.2.trans transitionTarget_spec.1.2⟩
  have hinv := branchRho_leftBranch
    ⟨hrt.1.le, (hrt.2.trans transitionTarget_spec.1.2).le⟩
  have ht : triangle U = r^3 := by
    rw [show triangle U = balancedTriangle _ _ from triangle_balancedGraphon _ _ _ _]
    rw [branch_eq_scaled_ray hz.1 |>.1, branch_eq_scaled_ray hz.1 |>.2,
      scaled_ray_triangle hz.1, hinv]
  exact ⟨U, balancedGraphon_isBalanced _ _ _ _, ht, he,
    value_le_cost ht.le, he ▸ (value_lt_entropy_below hr).2⟩

/-- Below the threshold no minimizer is a.e. constant, even at another value. -/
theorem minimizer_nonconstant_below {r : ℝ} (hr : r ∈ Ioo (0:ℝ) threshold)
    {U : Graphon} (hm : IsMinimizer r U) : ¬∃ c, IsConstant U c := by
  rintro ⟨c, hc⟩
  have hstrict := (value_lt_entropy_below hr).1.trans_lt (value_lt_entropy_below hr).2
  have hcost := (isMinimizer_iff.mp hm).2
  have hr01 : r ∈ Ioo (0:ℝ) 1 := ⟨hr.1, hr.2.trans threshold_mem_Ioo.2⟩
  have he := constant_of_cost_le_target hr01 hc hm.1 (hcost.trans_lt hstrict).le
  subst c
  have hcst := (constant_integrals ⟨hr01.1.le, hr01.2.le⟩ hc).2
  exact (ne_of_lt hstrict) (hcost.symm.trans hcst)

/-- The complete strict-improvement region, conditional only on `prop:critical`. -/
theorem strict_improvement_iff (hcrit : CriticalClassification)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) : value r < entropy r ↔ r < threshold := by
  rcases lt_trichotomy r threshold with hl | rfl | hg
  · exact iff_of_true ((value_lt_entropy_below ⟨hr.1, hl⟩).1.trans_lt
      (value_lt_entropy_below ⟨hr.1, hl⟩).2) hl
  · simp [hcrit.1]
  · simp [value_eq_entropy_above hcrit ⟨hg, hr.2⟩, not_lt_of_gt hg]

/-- The constant graphon is optimal precisely at and above the threshold. -/
theorem constant_optimal_iff (hcrit : CriticalClassification)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) :
    IsMinimizer r (constant r ⟨hr.1.le, hr.2.le⟩) ↔ threshold ≤ r := by
  constructor
  · intro hm
    by_contra hn
    have hs := (strict_improvement_iff hcrit hr).mpr (lt_of_not_ge hn)
    have he := (isMinimizer_iff.mp hm).2
    simp only [cost_constant] at he
    exact (ne_of_lt hs) he.symm
  · intro hle
    have he : value r = entropy r := by
      rcases eq_or_lt_of_le hle with he | hg
      · subst r; exact hcrit.1
      · exact value_eq_entropy_above hcrit ⟨hg, hr.2⟩
    exact isMinimizer_iff.mpr ⟨constant_feasible _ _, by simpa using he.symm⟩

end SparseLowerTail.Section05

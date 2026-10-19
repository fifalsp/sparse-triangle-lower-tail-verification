import SparseLowerTail.Section02.EntropyLSC
import SparseLowerTail.Section02.Relabeling
import SparseLowerTail.Section04.ActiveConstraint
import Mathlib.Topology.Order.IsLUB

/-!
# Existence of unrestricted graphon minimizers

Manuscript lem:existence(a). Only the three named classical analytic inputs are
parameters: dyadic L¹ approximation, graphon compactness modulo genuine
measure-preserving relabelings, and the triangle counting lemma. Minimizing
sequences, relabeling invariance, entropy LSC, feasibility of the limit,
attainment, and strict positivity are proved in this development.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- A genuine feasible graphon minimizing sequence, obtained from the actual infimum. -/
theorem exists_minimizing_sequence {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    ∃ U : ℕ → Graphon, (∀ n, Feasible r (U n)) ∧
      Tendsto (fun n => cost (U n)) atTop (𝓝 (value r)) := by
  have hne : {v | ∃ U : Graphon, Feasible r U ∧ cost U=v}.Nonempty :=
    ⟨_,constant r hr,constant_feasible r hr,rfl⟩
  obtain ⟨v,_,hlim,hv⟩ := exists_seq_tendsto_sInf hne (feasible_costs_bddBelow r)
  have hm : ∀ n, ∃ U : Graphon, Feasible r U ∧ cost U=v n := hv
  choose U hf he using hm
  refine ⟨U,hf,?_⟩
  simpa only [he] using hlim

/-- A fixed feasible set is closed under cut convergence by the counting lemma. -/
theorem feasible_of_cut_limit (hcount : ClassicalTriangleCounting)
    {r : ℝ} {U : ℕ → Graphon} {W : Graphon}
    (hcut : CutConverges U W) (hf : ∀ n, Feasible r (U n)) : Feasible r W :=
  le_of_tendsto (hcut.triangle hcount) (Eventually.of_forall hf)

/-- Attainment of the unrestricted graphon variational infimum. -/
theorem exists_minimizer (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) : ∃ U : Graphon, IsMinimizer r U := by
  obtain ⟨U,hf,hlim⟩ := exists_minimizing_sequence hr
  obtain ⟨W,σ,φ,hσ,hcut⟩ := hcompact U
  have hfeas : ∀ n, Feasible r (relabel (U (σ n)) (φ n)) := by
    intro n
    simpa only [Feasible,triangle_relabel] using hf (σ n)
  have hW := feasible_of_cut_limit hcount hcut hfeas
  have hcost : Tendsto (fun n => cost (relabel (U (σ n)) (φ n))) atTop (𝓝 (value r)) := by
    simpa only [cost_relabel,Function.comp_apply] using hlim.comp hσ.tendsto_atTop
  have hc := cost_le_limit_of_cut hdyadic hcut hcost
  exact ⟨W,isMinimizer_iff.mpr ⟨hW,le_antisymm hc (value_le_cost hW)⟩⟩

/-- Full positivity and bounds from lem:existence(a). -/
theorem value_pos_bounds (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) :
    0 < value r ∧ value r ≤ entropy r ∧ entropy r < 1 := by
  obtain ⟨U,hU⟩ := exists_minimizer hdyadic hcompact hcount ⟨hr.1.le,hr.2.le⟩
  have hp := Section04.cost_pos_of_feasible hr hU.1
  have he := (isMinimizer_iff.mp hU).2
  have hh := Section04.strictAntiOn_entropy (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    ⟨hr.1.le,hr.2.le⟩ hr.1
  exact ⟨he ▸ hp,value_le_entropy ⟨hr.1.le,hr.2.le⟩,by simpa only [entropy_zero] using hh⟩

end SparseLowerTail.Section02

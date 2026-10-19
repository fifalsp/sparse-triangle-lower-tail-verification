import SparseLowerTail.Basic

/-!
# Target statement: Theorem 1.3 (`thm:main`)

This file defines a proposition. It DOES NOT prove that proposition. There is
no axiom asserting it. Its graphon semantics use Lebesgue integrals, and its
optimizer clauses quantify over every graphon, not just finite SBMs.

The partition formulation of relabeling follows the paper's `lem:relabelB`;
that equivalence is proved in Section02.RelabelBalanced, relative to the
explicit classical nonatomic CDF transform. The displayed rational enclosures
are the more precise intervals in `lem:digits` for the transition target;
a* and b* are characterized here by the crossing minimizer, without decimals.
-/
noncomputable section
open Set
namespace SparseLowerTail

/-- Parts (a)--(d) of the main variational theorem, plus the certified interval
for the transition target. This structure is a proof-obligation inventory;
an inhabitant is constructed conditionally in MainTheoremAssembly and
Section08.ContinuationAssembly. The internal hypotheses remain unproved. -/
structure MainTheorem : Prop where
  threshold_bounds : (2096696762 : ℝ) / 10000000000 ≤ threshold ∧
    threshold ≤ (2096696763 : ℝ) / 10000000000
  value_reduction : ∀ r ∈ Ioo (0 : ℝ) 1, value r = balancedValue r
  strict_improvement : ∀ r ∈ Ioo (0 : ℝ) 1, value r < entropy r ↔ r < threshold
  above_transition : ∀ r ∈ Ioo threshold 1, ∀ U : Graphon,
    IsMinimizer r U ↔ IsConstant U r
  at_transition : ∃ a b : ℝ, 0 < a ∧ a < threshold ∧ threshold < b ∧ b < 1 ∧
    IsBalancedMinimizer threshold a b ∧
    ∀ U : Graphon, IsMinimizer threshold U ↔
      IsConstant U threshold ∨ IsBalanced U a b
  below_transition : ∀ r ∈ Ioo (0 : ℝ) threshold,
    ∃ a b : ℝ, 0 < a ∧ a < r ∧ r < b ∧ b < 1 ∧
      IsBalancedMinimizer r a b ∧
      (∀ c d : ℝ, IsBalancedMinimizer r c d → c = a ∧ d = b) ∧
      ∀ U : Graphon, IsMinimizer r U ↔ IsBalanced U a b

end SparseLowerTail

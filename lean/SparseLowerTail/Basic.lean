import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! Definitions use Lebesgue measure on [0,1], not a finite SBM surrogate. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail

/-- The sparse entropy, with the continuous convention `h 0 = 1`. -/
def entropy (x : ℝ) : ℝ := x * Real.log x - x + 1

@[simp] theorem entropy_zero : entropy 0 = 1 := by simp [entropy]
@[simp] theorem entropy_one : entropy 1 = 0 := by simp [entropy]

/-- Lebesgue probability measure on the unit interval, represented on ℝ. -/
def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure, Real.volume_Icc]

abbrev squareMeasure : Measure (ℝ × ℝ) := unitMeasure.prod unitMeasure
abbrev cubeMeasure : Measure (ℝ × (ℝ × ℝ)) := unitMeasure.prod squareMeasure

/-- A graphon representative; properties are required almost everywhere on
[0,1]². Values outside the unit square have no role in any definition. -/
structure Graphon where
  toFun : ℝ × ℝ → ℝ
  measurable : AEMeasurable toFun squareMeasure
  symmetric : ∀ᵐ p ∂squareMeasure, toFun p.swap = toFun p
  bounded : ∀ᵐ p ∂squareMeasure, toFun p ∈ Icc 0 1

instance : CoeFun Graphon (fun _ => (ℝ × ℝ) → ℝ) := ⟨Graphon.toFun⟩

/-- Normalized sparse entropy cost F. -/
def cost (U : Graphon) : ℝ := ∫ p, entropy (U p) ∂squareMeasure

/-- Triangle density t, with all three vertices sampled independently. -/
def triangle (U : Graphon) : ℝ :=
  ∫ p : ℝ × (ℝ × ℝ), U (p.1, p.2.1) * U (p.2.1, p.2.2) *
    U (p.1, p.2.2) ∂cubeMeasure

def Feasible (r : ℝ) (U : Graphon) : Prop := triangle U ≤ r ^ 3

/-- Order-based definition avoids assuming in advance that an infimum is attained. -/
def IsMinimizer (r : ℝ) (U : Graphon) : Prop :=
  Feasible r U ∧ ∀ W : Graphon, Feasible r W → cost U ≤ cost W

def value (r : ℝ) : ℝ := sInf {v | ∃ U : Graphon, Feasible r U ∧ cost U = v}

def constant (r : ℝ) (hr : r ∈ Icc 0 1) : Graphon where
  toFun := fun _ => r
  measurable := aemeasurable_const
  symmetric := Filter.Eventually.of_forall (fun _ => rfl)
  bounded := Filter.Eventually.of_forall (fun _ => hr)

@[simp] theorem cost_constant (r : ℝ) (hr : r ∈ Icc 0 1) :
    cost (constant r hr) = entropy r := by
  simp [cost, constant]

@[simp] theorem triangle_constant (r : ℝ) (hr : r ∈ Icc 0 1) :
    triangle (constant r hr) = r ^ 3 := by
  simp [triangle, constant, pow_succ]

theorem constant_feasible (r : ℝ) (hr : r ∈ Icc 0 1) :
    Feasible r (constant r hr) := by simp [Feasible]

/-- Equality is a.e. equality, not pointwise equality of representatives. -/
def IsConstant (U : Graphon) (r : ℝ) : Prop := U.toFun =ᵐ[squareMeasure] fun _ => r

/-- Balanced two-block form on an arbitrary measurable partition. This is the
partition formulation of `lem:relabelB`; its equivalence to measure-preserving
relabelings is a separate proof obligation. -/
def IsBalanced (U : Graphon) (a b : ℝ) : Prop := by
  classical
  exact ∃ P : Set ℝ, MeasurableSet P ∧ P ⊆ Icc 0 1 ∧ unitMeasure P = (1 / 2 : ENNReal) ∧
    U.toFun =ᵐ[squareMeasure] fun p => if (p.1 ∈ P ↔ p.2 ∈ P) then a else b

def balancedTriangle (a b : ℝ) : ℝ := (a ^ 3 + 3 * a * b ^ 2) / 4

def balancedCost (a b : ℝ) : ℝ := (entropy a + entropy b) / 2

def BalancedFeasible (r a b : ℝ) : Prop :=
  a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ balancedTriangle a b ≤ r ^ 3

def IsBalancedMinimizer (r a b : ℝ) : Prop := BalancedFeasible r a b ∧
  ∀ c d : ℝ, BalancedFeasible r c d → balancedCost a b ≤ balancedCost c d

def balancedValue (r : ℝ) : ℝ :=
  sInf {v | ∃ a b : ℝ, BalancedFeasible r a b ∧ balancedCost a b = v}

def threshold : ℝ :=
  sSup {r | r ∈ Ioo (0 : ℝ) 1 ∧ balancedValue r < entropy r}

@[simp] theorem balancedTriangle_diagonal (r : ℝ) :
    balancedTriangle r r = r ^ 3 := by unfold balancedTriangle; ring

@[simp] theorem balancedCost_diagonal (r : ℝ) :
    balancedCost r r = entropy r := by unfold balancedCost; ring

@[simp] theorem balancedTriangle_bipartite : balancedTriangle 0 1 = 0 := by
  norm_num [balancedTriangle]

@[simp] theorem balancedCost_bipartite : balancedCost 0 1 = 1 / 2 := by
  norm_num [balancedCost]

/-- The eight equally likely label triples give the balanced triangle polynomial.
Connecting this finite calculation to the graphon integral remains separate. -/
theorem balancedTriangle_eight_patterns (a b : ℝ) :
    (2 * (a * a * a) + 6 * (a * b * b)) / 8 = balancedTriangle a b := by
  unfold balancedTriangle
  ring

end SparseLowerTail

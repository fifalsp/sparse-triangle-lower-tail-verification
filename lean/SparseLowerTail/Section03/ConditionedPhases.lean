import SparseLowerTail.Section03.StructureEvents
import SparseLowerTail.Section03.ProbabilityRate

/-! The three probability-one matrix-structure conclusions from the variational classification. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02 Section04

section
variable (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    (hHarris : ∀ (ν : Type) [Fintype ν] [DecidableEq ν], ClassicalHarrisPositiveAssociation ν)
include hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris

/-- A constant minimizer classification gives the actual constant-matrix event with probability →1. -/
theorem triangle_constant_structure_tendsto
    {η ε : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hε : 0<ε)
    (hclass : ∀ U : Graphon, IsMinimizer (η^(1/3:ℝ)) U → IsConstant U (η^(1/3:ℝ)))
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
      (constantStructureEvent (n j) (p j) (η^(1/3:ℝ)) ε)) atTop (𝓝 1) := by
  classical
  apply triangle_conditional_event_tendsto hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
    hη hε n p hn hp hpzero hsparse
  intro j hnj z hz
  obtain ⟨U,hU,φ,hnear⟩ := hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,triangle_close_constant (n j) hnj (hp j).1 le_rfl
    z U (hclass U hU) φ hnear⟩

/-- A balanced minimizer classification gives the actual rounded bipod event with probability →1. -/
theorem triangle_bipod_structure_tendsto
    {η a b ε : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hab : a<b) (hε : 0<ε)
    (hclass : ∀ U : Graphon, IsMinimizer (η^(1/3:ℝ)) U → IsBalanced U a b)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
      (bipodStructureEvent (n j) (p j) a b ε)) atTop (𝓝 1) := by
  classical
  obtain ⟨δ,hδ,_hδε,h33,h16⟩ := exists_structure_tolerance hab hε
  apply triangle_conditional_event_tendsto hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
    hη hδ n p hn hp hpzero hsparse
  intro j hnj z hz
  obtain ⟨U,hU,φ,hnear⟩ := hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,triangle_close_bipod (n j) hnj (hp j).1 hab hδ h33 h16
    z U (hclass U hU) φ hnear⟩

/-- At coexistence, the actual union of the two matrix events has probability →1. -/
theorem triangle_phase_structure_tendsto
    {η a b ε : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hab : a<b) (hε : 0<ε)
    (hclass : ∀ U : Graphon, IsMinimizer (η^(1/3:ℝ)) U →
      IsConstant U (η^(1/3:ℝ)) ∨ IsBalanced U a b)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
      (phaseStructureEvent (n j) (p j) (η^(1/3:ℝ)) a b ε)) atTop (𝓝 1) := by
  classical
  obtain ⟨δ,hδ,hδε,h33,h16⟩ := exists_structure_tolerance hab hε
  apply triangle_conditional_event_tendsto hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
    hη hδ n p hn hp hpzero hsparse
  intro j hnj z hz
  obtain ⟨U,hU,φ,hnear⟩ := hz
  rcases hclass U hU with hconst|hbipod
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      triangle_close_constant (n j) hnj (hp j).1 hδε z U hconst φ hnear⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      triangle_close_bipod (n j) hnj (hp j).1 hab hδ h33 h16 z U hbipod φ hnear⟩)

/-- Full `thm:structure`: constant above, a unique balanced bipod below, and their union at coexistence. -/
theorem triangle_conditioned_phases (hmain : MainTheorem)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    (threshold^3<η → ∀ ε : ℝ, 0<ε →
      Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
        (constantStructureEvent (n j) (p j) (η^(1/3:ℝ)) ε)) atTop (𝓝 1)) ∧
    (η<threshold^3 → ∃ a b : ℝ, 0<a ∧ a<η^(1/3:ℝ) ∧ η^(1/3:ℝ)<b ∧ b<1 ∧
      IsBalancedMinimizer (η^(1/3:ℝ)) a b ∧
      (∀ c d : ℝ, IsBalancedMinimizer (η^(1/3:ℝ)) c d → c=a ∧ d=b) ∧
      ∀ ε : ℝ, 0<ε → Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
        (bipodStructureEvent (n j) (p j) a b ε)) atTop (𝓝 1)) ∧
    (η=threshold^3 → ∃ a b : ℝ, 0<a ∧ a<threshold ∧ threshold<b ∧ b<1 ∧
      IsBalancedMinimizer threshold a b ∧
      ∀ ε : ℝ, 0<ε → Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
        (phaseStructureEvent (n j) (p j) (η^(1/3:ℝ)) a b ε)) atTop (𝓝 1)) := by
  let r := η^(1/3:ℝ)
  have hr : r∈Ioo (0:ℝ) 1 := ⟨Real.rpow_pos_of_pos hη.1 _,Real.rpow_lt_one hη.1.le hη.2 (by norm_num)⟩
  have hc : r^3=η := by
    simpa only [r,one_div] using Real.rpow_inv_natCast_pow hη.1.le (by norm_num : (3:ℕ)≠0)
  have hcrit : threshold^3≤η ↔ threshold≤r := (threshold_le_cubeRoot_iff hη).symm
  refine ⟨?_,?_,?_⟩
  · intro hηabove ε hε
    have hrabove : threshold<r := by
      have hh : threshold≤r := hcrit.mp hηabove.le
      apply lt_of_le_of_ne hh
      intro he
      rw [← hc,he] at hηabove
      exact (lt_irrefl _ hηabove)
    exact triangle_constant_structure_tendsto hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
      hη hε (fun U hU => (hmain.above_transition r ⟨hrabove,hr.2⟩ U).mp hU) n p hn hp hpzero hsparse
  · intro hηbelow
    have hrbelow : r<threshold := by
      by_contra h
      exact (not_le_of_gt hηbelow) (hcrit.mpr (le_of_not_gt h))
    obtain ⟨a,b,ha,har,hrb,hb,hmin,hunique,hclass⟩ := hmain.below_transition r ⟨hr.1,hrbelow⟩
    refine ⟨a,b,ha,har,hrb,hb,hmin,hunique,fun ε hε => ?_⟩
    exact triangle_bipod_structure_tendsto hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
      hη (har.trans hrb) hε (fun U hU => (hclass U).mp hU) n p hn hp hpzero hsparse
  · intro hηcrit
    have hre : r=threshold := by
      apply (pow_left_inj₀ hr.1.le threshold_mem_Ioo.1.le (by norm_num : (3:ℕ)≠0)).mp
      exact hc.trans hηcrit
    obtain ⟨a,b,ha,har,hrb,hb,hmin,hclass⟩ := hmain.at_transition
    refine ⟨a,b,ha,har,hrb,hb,hmin,fun ε hε => ?_⟩
    apply triangle_phase_structure_tendsto hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
      hη (har.trans hrb) hε _ n p hn hp hpzero hsparse
    intro U hU
    change IsMinimizer r U at hU
    change IsConstant U r ∨ IsBalanced U a b
    rw [hre] at hU ⊢
    exact (hclass U).mp hU


/-- The conditioned-structure corollary assembled directly from the outstanding numerical replays. -/
theorem triangle_conditioned_phases_of_remaining_replays
    (external : Section07.KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : Section07.PositiveKernelSpectralTheorem)
    (hnJobs : Section05.RemainingNonapexJobResults) (haJobs : Section05.ApexJobResults)
    (hABB : Certificate.FamilyABBLocal)
    (hExterior : Certificate.FamilyABBLocal → Section08.CompactFamilyCertificate)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    (threshold^3<η → ∀ ε : ℝ, 0<ε →
      Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
        (constantStructureEvent (n j) (p j) (η^(1/3:ℝ)) ε)) atTop (𝓝 1)) ∧
    (η<threshold^3 → ∃ a b : ℝ, 0<a ∧ a<η^(1/3:ℝ) ∧ η^(1/3:ℝ)<b ∧ b<1 ∧
      IsBalancedMinimizer (η^(1/3:ℝ)) a b ∧
      (∀ c d : ℝ, IsBalancedMinimizer (η^(1/3:ℝ)) c d → c=a ∧ d=b) ∧
      ∀ ε : ℝ, 0<ε → Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
        (bipodStructureEvent (n j) (p j) a b ε)) atTop (𝓝 1)) ∧
    (η=threshold^3 → ∃ a b : ℝ, 0<a ∧ a<threshold ∧ threshold<b ∧ b<1 ∧
      IsBalancedMinimizer threshold a b ∧
      ∀ ε : ℝ, 0<ε → Tendsto (fun j => triangleConditionalEventMass (n j) (p j) (η^(1/3:ℝ))
        (phaseStructureEvent (n j) (p j) (η^(1/3:ℝ)) a b ε)) atTop (𝓝 1)) :=
  triangle_conditioned_phases hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
    (mainTheorem_of_remaining_replays external hSampling hSpectral hdyadic hcompact hpull hcount
      hnJobs haJobs hABB hExterior) hη n p hn hp hpzero hsparse

end
end SparseLowerTail.Section03

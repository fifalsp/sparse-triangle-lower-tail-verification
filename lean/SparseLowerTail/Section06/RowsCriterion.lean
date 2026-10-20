import SparseLowerTail.Section06.RowsBipodal

/-! The manuscript's separate restricted-row hypotheses imply the proved bipodal criterion. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section02 Section04

/-- `lem:rowsbipodal` in its exact two-restricted-rectangles formulation.
The row profiles need not themselves be measurable. -/
theorem bipodal_of_two_restricted_rows {P : Set ℝ} (hP : MeasurableSet P)
    (hmass : unitMeasure.real P∈Ioo (0:ℝ) 1) (U : Graphon) (f g : ℝ → ℝ)
    (hleft : ∀ᵐ p ∂squareMeasure.restrict (P×ˢuniv), U p=f p.2)
    (hright : ∀ᵐ p ∂squareMeasure.restrict (Pᶜ×ˢuniv), U p=g p.2) :
    ∃ a d b : ℝ, IsBipodal U (unitMeasure.real P) a d b := by
  classical
  have hp : unitMeasure P≠0 := by
    intro hz
    have hh : unitMeasure.real P=0 := by simp [Measure.real,hz]
    linarith [hmass.1]
  have hpc : unitMeasure Pᶜ≠0 := by
    intro hz
    have hh : unitMeasure.real Pᶜ=0 := by simp [Measure.real,hz]
    rw [measureReal_compl hP,measureReal_univ_eq_one] at hh
    linarith [hmass.2]
  apply bipodal_of_two_rows hP hp hpc
  have hl := (ae_restrict_iff' (hP.prod MeasurableSet.univ)).mp hleft
  have hr := (ae_restrict_iff' (hP.compl.prod MeasurableSet.univ)).mp hright
  filter_upwards [hl,hr] with p hpl hpr
  by_cases hx : p.1∈P
  · simp only [hx,if_true]
    exact hpl ⟨hx,mem_univ _⟩
  · simp only [hx,if_false]
    exact hpr ⟨hx,mem_univ _⟩

end SparseLowerTail.Section06

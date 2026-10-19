import SparseLowerTail.Section04.Rescaling

/-! The final infimum assertion in `lem:truncation`. -/
noncomputable section
open Set
namespace SparseLowerTail.NonnegativeKernel

/-- The variational problem extended to all bounded nonnegative kernels. -/
def variationalValue (r : ℝ) : ℝ :=
  sInf {v | ∃ W : NonnegativeKernel, W.triangle ≤ r^3 ∧ W.cost = v}

/-- Allowing kernels to exceed one does not change the infimum. -/
theorem variationalValue_eq_value {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    variationalValue r = SparseLowerTail.value r := by
  let S := {v : ℝ | ∃ W : NonnegativeKernel, W.triangle ≤ r^3 ∧ W.cost = v}
  have hne : S.Nonempty := by
    refine ⟨entropy r, ofGraphon (constant r hr), ?_, ?_⟩ <;> simp
  have hb : BddBelow S := by
    refine ⟨SparseLowerTail.value r, ?_⟩
    rintro v ⟨W,hW,rfl⟩
    exact value_le_cost W hW
  change sInf S = SparseLowerTail.value r
  apply le_antisymm
  · unfold SparseLowerTail.value
    apply le_csInf
    · exact ⟨SparseLowerTail.cost (constant r hr), constant r hr, constant_feasible r hr, rfl⟩
    · rintro v ⟨U,hU,rfl⟩
      apply csInf_le hb
      exact ⟨ofGraphon U, hU, rfl⟩
  · apply le_csInf hne
    rintro v ⟨W,hW,rfl⟩
    exact value_le_cost W hW

end SparseLowerTail.NonnegativeKernel

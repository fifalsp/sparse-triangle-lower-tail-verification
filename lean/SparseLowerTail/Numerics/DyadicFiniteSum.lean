import SparseLowerTail.Numerics.DyadicInterval

/-! Finite sums of checked dyadic enclosures. -/
namespace SparseLowerTail.Numerics.DyadicInterval

def sumFin : {n : ℕ} → (Fin n → DyadicInterval) → DyadicInterval
  | 0,_ => point 0
  | n+1,I => (I 0).add (sumFin (fun i : Fin n => I i.succ))

theorem sumFin_contains {n : ℕ} {I : Fin n → DyadicInterval} {x : Fin n → ℝ}
    (hx : ∀ i,(I i).contains (x i)) : (sumFin I).contains (∑ i,x i) := by
  induction n with
  | zero => simpa [sumFin] using point_contains 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact add_contains (hx 0) (ih (fun i => hx i.succ))

/-- An absolute bound in units of the fixed dyadic scale. -/
def absBound (I : DyadicInterval) : ℤ := max (-I.lower) I.upper

theorem abs_le_absBound {I : DyadicInterval} {x : ℝ} (hx : I.contains x) :
    |x| ≤ (I.absBound : ℝ)/scale := by
  apply abs_le.mpr
  constructor
  · have h : -(I.lower : ℝ)≤(I.absBound : ℝ) := by
      exact_mod_cast le_max_left (-I.lower) I.upper
    have hh := div_le_div_of_nonneg_right h scale_real_pos.le
    have hl := hx.1
    rw [neg_div] at hh
    linarith
  · have h : (I.upper : ℝ)≤(I.absBound : ℝ) := by
      exact_mod_cast le_max_right (-I.lower) I.upper
    exact hx.2.trans (div_le_div_of_nonneg_right h scale_real_pos.le)

end SparseLowerTail.Numerics.DyadicInterval

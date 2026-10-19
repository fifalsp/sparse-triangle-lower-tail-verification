import SparseLowerTail.Section05.LogBoxSubdivision

/-! Exact justification of the ordered-box tightening used by the Arb search.
Only inequalities implied by q₀≥q₁≥q₂ are added, so no ordered point is lost. -/
noncomputable section
namespace SparseLowerTail.Section05

theorem LogBox.mem_region_iff (B : LogBox) (q : EdgeTriple) :
    q ∈ B.region ↔
      ((B.lower 0:ℝ) ≤ q.1.1 ∧ q.1.1 ≤ (B.upper 0:ℝ)) ∧
      ((B.lower 1:ℝ) ≤ q.1.2 ∧ q.1.2 ≤ (B.upper 1:ℝ)) ∧
      ((B.lower 2:ℝ) ≤ q.2 ∧ q.2 ≤ (B.upper 2:ℝ)) := by
  constructor
  · intro h
    exact ⟨h 0,h 1,h 2⟩
  · rintro ⟨hx,hy,hz⟩ i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz

/-- The exact max/min tightening in verification/cover/verify_endpoint.py. -/
def LogBox.tightenOrdered (B : LogBox) : LogBox :=
  ⟨![max (max (B.lower 0) (B.lower 1)) (B.lower 2),max (B.lower 1) (B.lower 2),B.lower 2],
    ![B.upper 0,min (B.upper 0) (B.upper 1),min (min (B.upper 0) (B.upper 1)) (B.upper 2)]⟩

theorem LogBox.mem_tightenOrdered_iff (B : LogBox) (q : EdgeTriple)
    (hxy : q.1.2 ≤ q.1.1) (hyz : q.2 ≤ q.1.2) :
    q ∈ B.tightenOrdered.region ↔ q ∈ B.region := by
  simp only [LogBox.mem_region_iff,LogBox.tightenOrdered,Matrix.cons_val,
    Rat.cast_max,Rat.cast_min,max_le_iff,le_min_iff]
  constructor
  · rintro ⟨hx,hy,hz⟩
    exact ⟨⟨hx.1.1.1,hx.2⟩,⟨hy.1.1,hy.2.2⟩,⟨hz.1,hz.2.2⟩⟩
  · rintro ⟨hx,hy,hz⟩
    exact ⟨⟨⟨⟨hx.1,hy.1.trans hxy⟩,hz.1.trans (hyz.trans hxy)⟩,hx.2⟩,
      ⟨⟨hy.1,hz.1.trans hyz⟩,hxy.trans hx.2,hy.2⟩,
      ⟨hz.1,⟨hyz.trans (hxy.trans hx.2),hyz.trans hy.2⟩,hz.2⟩⟩

/-- Tightening preserves exactly the intersection with the sorted domain. -/
theorem LogBox.tightenOrdered_inter (B : LogBox) (Q : ℝ) :
    B.tightenOrdered.region ∩ orderedLogDomain Q = B.region ∩ orderedLogDomain Q := by
  ext q
  constructor
  · rintro ⟨hB,hD⟩
    exact ⟨(B.mem_tightenOrdered_iff q hD.2.2.1 hD.2.1).mp hB,hD⟩
  · rintro ⟨hB,hD⟩
    exact ⟨(B.mem_tightenOrdered_iff q hD.2.2.1 hD.2.1).mpr hB,hD⟩

/-- A checked subtree on the tightened box is valid on the original box's
ordered portion. The subtree's analytic leaves must still be supplied as proofs. -/
theorem CheckedLogBoxTree.sound_of_ordered_tightening {B : LogBox} {Q : ℝ}
    {P : EdgeTriple → Prop} (T : CheckedLogBoxTree (orderedLogDomain Q) P B.tightenOrdered) :
    ∀ q ∈ B.region, q ∈ orderedLogDomain Q → P q := by
  intro q hB hD
  apply T.sound q _ hD
  exact (B.mem_tightenOrdered_iff q hD.2.2.1 hD.2.1).mpr hB

end SparseLowerTail.Section05

import SparseLowerTail.Section08.FamilyCompactReplay

/-! Literal ordered zero-set conclusion of Appendix A.3, Proposition A.5.
The finite compact certificate remains an explicit internal hypothesis. -/
noncomputable section
namespace SparseLowerTail.Certificate.ManuscriptCompactConclusion
open Numerics Section02 Section04 Set

private theorem log_coordinate_a {z t : ℝ} (h : Real.exp (-t)=branchA z) :
    t=qA z := by
  have hh := congrArg Real.log h
  rw [Real.log_exp] at hh
  unfold qA
  linarith

private theorem log_coordinate_b {z t : ℝ} (h : Real.exp (-t)=branchB z) :
    t= -Real.log (branchB z) := by
  have hh := congrArg Real.log h
  rw [Real.log_exp] at hh
  linarith

/-- Sorting removes the two forbidden placements of the a-edge. -/
theorem ordered_pattern_iff_contacts {z : ℝ} (hz : 0<z) (hz1 : z<1)
    {q : FamilyVector} (hs21 : q 2≤q 1) (hs10 : q 1≤q 0) :
    AllowedPattern (branchA z) (branchB z)
      (Real.exp (-q 0)) (Real.exp (-q 1)) (Real.exp (-q 2)) ↔
    q=familyContactAAA z ∨ q=familyContactABB z := by
  constructor
  · intro hp
    rcases hp with ha | habb | hbab | hbba
    · left
      funext i
      fin_cases i
      · exact log_coordinate_a ha.1
      · exact log_coordinate_a ha.2.1
      · exact log_coordinate_a ha.2.2
    · right
      funext i
      fin_cases i
      · exact log_coordinate_a habb.1
      · exact log_coordinate_b habb.2.1
      · exact log_coordinate_b habb.2.2
    · have horder := Real.exp_le_exp.mpr (neg_le_neg hs10)
      rw [hbab.1,hbab.2.1] at horder
      exact (not_le_of_gt (branchA_lt_branchB hz1) horder).elim
    · have horder := Real.exp_le_exp.mpr (neg_le_neg hs21)
      rw [hbba.2.1,hbba.2.2] at horder
      exact (not_le_of_gt (branchA_lt_branchB hz1) horder).elim
  · rintro (rfl | rfl)
    · exact allowedPattern_of_familyContact hz false
    · exact allowedPattern_of_familyContact hz true

/-- Exact nonnegativity and both directions of the ordered zero set, from
precisely the existing compact numerical certificate. -/
theorem compact_nonnegative_and_exact_zeros
    (hfinite : Section08.CompactFamilyCertificate)
    {z : ℝ} (hz : 0<z) (hL : branchLog z∈Icc (39/10:ℝ) (19/2))
    {q : FamilyVector} (hq : ∀i,q i∈Icc (0:ℝ) 12)
    (hs21 : q 2≤q 1) (hs10 : q 1≤q 0) :
    0≤familyPhi z q ∧
      (familyPhi z q=0 ↔ q=familyContactAAA z ∨ q=familyContactABB z) := by
  have hz40 := family_parameter_lt_one_fortieth hz hL.1
  have hz1 : z<1 := by linarith
  have hg := (gamma_branch_neg hz hz40.le).ne
  have hc := hfinite z hz hL (q 0) (hq 0) (q 1) (hq 1) (q 2) (hq 2)
  refine ⟨hc.1,?_⟩
  constructor
  · intro he
    exact (ordered_pattern_iff_contacts hz hz1 hs21 hs10).mp (hc.2 he)
  · rintro (rfl | rfl)
    · exact familyContactAAA_value hz hz1 hg
    · exact familyContactABB_value hz hz1 hg

/-- Proposition A.5 in the manuscript's independent L coordinate. -/
theorem compact_statement_in_L (hfinite : Section08.CompactFamilyCertificate)
    {L : ℝ} (hL : L∈Icc (39/10:ℝ) (19/2))
    {q : FamilyVector} (hq : ∀i,q i∈Icc (0:ℝ) 12)
    (hs21 : q 2≤q 1) (hs10 : q 1≤q 0) :
    0≤familyPhi (Real.exp (-L)) q ∧
      (familyPhi (Real.exp (-L)) q=0 ↔
        q=familyContactAAA (Real.exp (-L)) ∨ q=familyContactABB (Real.exp (-L))) := by
  have he : branchLog (Real.exp (-L))=L := by simp
  exact compact_nonnegative_and_exact_zeros hfinite (Real.exp_pos _)
    (by simpa only [he] using hL) hq hs21 hs10

/-- The source of the remaining hypothesis can be a checked finite table;
this adapter adds no new numerical or analytic premise. -/
theorem compact_statement_of_table
    (table : RegisterTree (Option (ReplayBox 4))) (tree : BoxReplay 4)
    (htree : tree.Valid table.get familyCompactInitialBox)
    (hleaf : table.All (ReplayBoxProperty familyCompactProperty))
    {L : ℝ} (hL : L∈Icc (39/10:ℝ) (19/2))
    {q : FamilyVector} (hq : ∀i,q i∈Icc (0:ℝ) 12)
    (hs21 : q 2≤q 1) (hs10 : q 1≤q 0) :
    0≤familyPhi (Real.exp (-L)) q ∧
      (familyPhi (Real.exp (-L)) q=0 ↔
        q=familyContactAAA (Real.exp (-L)) ∨ q=familyContactABB (Real.exp (-L))) :=
  compact_statement_in_L (compactFamilyCertificate_of_table table tree htree hleaf)
    hL hq hs21 hs10

end SparseLowerTail.Certificate.ManuscriptCompactConclusion

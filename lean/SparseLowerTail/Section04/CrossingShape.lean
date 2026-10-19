import SparseLowerTail.Section04.Ray
import Mathlib.Order.Monotone.Union

/-!
# Shape of the normalized cost gap

The shape argument in `thm:crossing`. The statements below expose the level-set
facts about rho which are supplied by unimodality and the two inverse branches.
They prove the calculus/comparison step; they do not assume the desired cost
comparison or the existence of the transition.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section04

theorem deriv_rayGap_neg {r z : ℝ} (hr : 0 < r) (hz : z ∈ Ioo (0 : ℝ) 1)
    (h : branchRho z < r) : deriv (rayGap r) z < 0 := by
  rw [deriv_rayGap hz.1 hz.2]
  exact mul_neg_of_neg_of_pos (deriv_rayExcess_neg hz.1 hz.2)
    (sub_pos.mpr (Real.strictMonoOn_log (branchRho_mem_Ioo hz.1 hz.2).1 hr h))

theorem deriv_rayGap_pos {r z : ℝ} (hr : 0 < r) (hz : z ∈ Ioo (0 : ℝ) 1)
    (h : r < branchRho z) : 0 < deriv (rayGap r) z := by
  rw [deriv_rayGap hz.1 hz.2]
  exact mul_pos_of_neg_of_neg (deriv_rayExcess_neg hz.1 hz.2)
    (sub_neg.mpr (Real.strictMonoOn_log hr (branchRho_mem_Ioo hz.1 hz.2).1 h))

/-- Cost-gap shape below the spinodal, assuming only the corresponding
three level-set inequalities for rho. -/
theorem rayGap_shape {r l u : ℝ} (hr : 0 < r)
    (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (hleft : ∀ z ∈ Ioo (0 : ℝ) l, branchRho z < r)
    (hmiddle : ∀ z ∈ Ioo l u, r < branchRho z)
    (hright : ∀ z ∈ Ioo u 1, branchRho z < r) :
    StrictAntiOn (rayGap r) (Ioc (0 : ℝ) l) ∧
    StrictMonoOn (rayGap r) (Icc l u) ∧
    StrictAntiOn (rayGap r) (Icc u 1) := by
  have hc := continuousOn_rayGap r
  refine ⟨?_, ?_, ?_⟩
  · apply strictAntiOn_of_deriv_neg (convex_Ioc 0 l)
    · exact hc.mono (by intro z hz; exact ⟨hz.1, hz.2.trans (hlu.trans hu).le⟩)
    · intro z hz
      rw [interior_Ioc] at hz
      exact deriv_rayGap_neg hr ⟨hz.1, hz.2.trans (hlu.trans hu)⟩ (hleft z hz)
  · apply strictMonoOn_of_deriv_pos (convex_Icc l u)
    · exact hc.mono (by intro z hz; exact ⟨hl.trans_le hz.1, hz.2.trans hu.le⟩)
    · intro z hz
      rw [interior_Icc] at hz
      exact deriv_rayGap_pos hr ⟨hl.trans hz.1, hz.2.trans hu⟩ (hmiddle z hz)
  · apply strictAntiOn_of_deriv_neg (convex_Icc u 1)
    · exact hc.mono (by intro z hz; exact ⟨(hl.trans hlu).trans_le hz.1, hz.2⟩)
    · intro z hz
      rw [interior_Icc] at hz
      exact deriv_rayGap_neg hr ⟨(hl.trans hlu).trans hz.1, hz.2⟩ (hright z hz)

/-- Above the spinodal (including equality), a single exceptional point with
zero derivative does not prevent strict decrease of the cost gap. -/
theorem rayGap_strictAnti_of_single_exception {r s : ℝ} (hr : 0 < r)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hlevel : ∀ z ∈ Ioo (0 : ℝ) 1, z ≠ s → branchRho z < r) :
    StrictAntiOn (rayGap r) (Ioc (0 : ℝ) 1) := by
  have hc := continuousOn_rayGap r
  have hleft : StrictAntiOn (rayGap r) (Ioc (0 : ℝ) s) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 s)
    · exact hc.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hs.2.le⟩)
    · intro z hz
      rw [interior_Ioc] at hz
      exact deriv_rayGap_neg hr ⟨hz.1, hz.2.trans hs.2⟩
        (hlevel z ⟨hz.1, hz.2.trans hs.2⟩ (ne_of_lt hz.2))
  have hright : StrictAntiOn (rayGap r) (Icc s 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s 1)
    · exact hc.mono (by intro z hz; exact ⟨hs.1.trans_le hz.1, hz.2⟩)
    · intro z hz
      rw [interior_Icc] at hz
      exact deriv_rayGap_neg hr ⟨hs.1.trans hz.1, hz.2⟩
        (hlevel z ⟨hs.1.trans hz.1, hz.2⟩ (ne_of_gt hz.1))
  intro x hx y hy hxy
  by_cases hxs : x ≤ s
  · by_cases hys : y ≤ s
    · exact hleft ⟨hx.1, hxs⟩ ⟨hy.1, hys⟩ hxy
    · have hsy : s < y := lt_of_not_ge hys
      exact (hright ⟨le_rfl, hs.2.le⟩ ⟨hsy.le, hy.2⟩ hsy).trans_le
        (hleft.antitoneOn ⟨hx.1, hxs⟩ ⟨hs.1, le_rfl⟩ hxs)
  · exact hright ⟨(lt_of_not_ge hxs).le, hx.2⟩
      ⟨((lt_of_not_ge hxs).trans hxy).le, hy.2⟩ hxy

/-- The strictly decreasing terminal interval lies strictly above zero. -/
theorem rayGap_pos_on_right {r u : ℝ} (hu : u < 1)
    (h : StrictAntiOn (rayGap r) (Icc u 1)) {z : ℝ} (hz : z ∈ Ico u 1) :
    0 < rayGap r z := by
  have ht := h ⟨hz.1, hz.2.le⟩ ⟨hu.le, le_rfl⟩ hz.2
  simpa using ht

/-- On the first two intervals the gap has a unique minimum at the left root. -/
theorem rayGap_min_on_initial {r l u : ℝ} (hl : 0 < l) (hlu : l < u)
    (hleft : StrictAntiOn (rayGap r) (Ioc (0 : ℝ) l))
    (hmiddle : StrictMonoOn (rayGap r) (Icc l u)) {z : ℝ}
    (hz : z ∈ Ioc (0 : ℝ) u) :
    rayGap r l ≤ rayGap r z ∧ (rayGap r z = rayGap r l ↔ z = l) := by
  rcases lt_trichotomy z l with hzl | rfl | hlz
  · have h := hleft ⟨hz.1, hzl.le⟩ ⟨hl, le_rfl⟩ hzl
    exact ⟨h.le, ⟨fun he => False.elim (h.ne' he), fun he => False.elim (hzl.ne he)⟩⟩
  · exact ⟨le_rfl, by simp⟩
  · have h := hmiddle ⟨le_rfl, hlu.le⟩ ⟨hlz.le, hz.2⟩ hlz
    exact ⟨h.le, ⟨fun he => False.elim (h.ne' he), fun he => False.elim (hlz.ne' he)⟩⟩

/-- If the left-root gap is nonpositive, it is the unique global minimum
on the open parameter interval. This includes the transition itself. -/
theorem rayGap_unique_min_of_nonpos {r l u : ℝ} (hl : 0 < l) (hlu : l < u)
    (hu : u < 1) (hleft : StrictAntiOn (rayGap r) (Ioc (0 : ℝ) l))
    (hmiddle : StrictMonoOn (rayGap r) (Icc l u))
    (hright : StrictAntiOn (rayGap r) (Icc u 1)) (hgap : rayGap r l ≤ 0)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    rayGap r l ≤ rayGap r z ∧ (rayGap r z = rayGap r l ↔ z = l) := by
  by_cases hzu : z ≤ u
  · exact rayGap_min_on_initial hl hlu hleft hmiddle ⟨hz.1, hzu⟩
  · have huz := lt_of_not_ge hzu
    have hpos := rayGap_pos_on_right hu hright ⟨huz.le, hz.2⟩
    have hlt := hgap.trans_lt hpos
    exact ⟨hlt.le, ⟨fun he => False.elim (hlt.ne' he),
      fun he => False.elim ((hlu.trans huz).ne' he)⟩⟩

/-- Once the left-root gap is positive, the entire open ray is positive. -/
theorem rayGap_pos_of_left_root_pos {r l u : ℝ} (hl : 0 < l) (hlu : l < u)
    (hu : u < 1) (hleft : StrictAntiOn (rayGap r) (Ioc (0 : ℝ) l))
    (hmiddle : StrictMonoOn (rayGap r) (Icc l u))
    (hright : StrictAntiOn (rayGap r) (Icc u 1)) (hgap : 0 < rayGap r l)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : 0 < rayGap r z := by
  by_cases hzu : z ≤ u
  · exact hgap.trans_le (rayGap_min_on_initial hl hlu hleft hmiddle ⟨hz.1, hzu⟩).1
  · exact rayGap_pos_on_right hu hright ⟨(lt_of_not_ge hzu).le, hz.2⟩

end SparseLowerTail.Section04

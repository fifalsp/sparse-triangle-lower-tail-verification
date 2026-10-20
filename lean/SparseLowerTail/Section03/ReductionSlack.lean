import SparseLowerTail.Section03.ConditionalCostBounds

/-! Explicit finite slack choices for the conditioned-structure argument. -/
noncomputable section
open Set
namespace SparseLowerTail.Section03

/-- Choose the relaxed cube-root target directly, with both required errors small.
This discharges the manuscript's simultaneous continuity/slack choice. -/
theorem exists_reduction_cube_slack {r δ ω : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hδ : 0<δ) (hω : 0<ω) :
    ∃ ζ s : ℝ, 0<ζ ∧ s∈Ioo r 1 ∧ s^3=r^3+ζ ∧ ζ≤δ ∧ ζ≤ω/8 ∧ 1-r/s≤ω/8 := by
  let t := min ((1-r)/2) (min (δ/6) (min (ω/48) (ω*r/16)))
  have ht : 0<t := lt_min (by linarith [hr.2])
    (lt_min (by positivity) (lt_min (by positivity) (div_pos (mul_pos hω hr.1) (by norm_num))))
  have ht1 : t≤(1-r)/2 := min_le_left _ _
  have htδ : t≤δ/6 := (min_le_left _ _).trans' (min_le_right _ _)
  have htω : t≤ω/48 := (min_le_left _ _).trans' ((min_le_right _ _).trans (min_le_right _ _))
  have htr : t≤ω*r/16 := (min_le_right _ _).trans' ((min_le_right _ _).trans (min_le_right _ _))
  let s := r+t
  have hspos : 0<s := by dsimp [s]; linarith [hr.1]
  have hsone : s<1 := by dsimp [s]; linarith [hr.2]
  have hpoly : s^3-r^3=t*(s^2+s*r+r^2) := by dsimp [s]; ring
  have hfactorpos : 0<s^2+s*r+r^2 := by nlinarith [sq_pos_of_pos hr.1,mul_pos hspos hr.1]
  have hζpos : 0<s^3-r^3 := by rw [hpoly]; exact mul_pos ht hfactorpos
  have hfactor : s^2+s*r+r^2≤3 := by
    have hrs : s*r≤1 := (mul_le_mul_of_nonneg_right hsone.le hr.1.le).trans (by simpa using hr.2.le)
    nlinarith [sq_nonneg (1-s),sq_nonneg (1-r),mul_nonneg hspos.le (sub_nonneg.mpr hsone.le),
      mul_nonneg hr.1.le (sub_nonneg.mpr hr.2.le)]
  have hζbound : s^3-r^3≤3*t := by
    rw [hpoly]
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hfactor)]
  refine ⟨s^3-r^3,s,hζpos,⟨by dsimp [s]; linarith,hsone⟩,by ring,by linarith,by linarith,?_⟩
  have he : 1-r/s=(s-r)/s := by field_simp
  rw [he]
  apply (div_le_iff₀ hspos).mpr
  dsimp only [s]
  nlinarith [mul_nonneg hω.le ht.le]

end SparseLowerTail.Section03

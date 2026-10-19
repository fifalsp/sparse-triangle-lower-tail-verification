import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic

/-! Exact planar geometry for the critical certificate cover. All statements
are geometric facts over ℝ; no floating-point or area-based inference is used. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.Planar

/-- Signed twice-area, positive on the left of the oriented edge a→b. -/
def orient (a b p : ℝ × ℝ) : ℝ :=
  (b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1)

@[simp] theorem orient_self_left (a b : ℝ × ℝ) : orient a b a=0 := by simp [orient]
@[simp] theorem orient_self_right (a b : ℝ × ℝ) : orient a b b=0 := by dsimp [orient]; ring
theorem orient_cyclic (a b c : ℝ × ℝ) : orient a b c=orient b c a := by dsimp [orient]; ring
theorem orient_swap (a b p : ℝ × ℝ) : orient b a p= -orient a b p := by dsimp [orient]; ring

/-- The closed three-half-plane criterion, proved by explicit barycentric
coordinates. The positive orientation hypothesis rules out a degenerate triangle. -/
theorem mem_triangle_of_orient {a b c p : ℝ × ℝ} (hD : 0<orient a b c)
    (hab : 0≤orient a b p) (hbc : 0≤orient b c p) (hca : 0≤orient c a p) :
    p∈convexHull ℝ ({a,b,c} : Set (ℝ × ℝ)) := by
  let w : Fin 3 → ℝ := ![orient b c p/orient a b c,orient c a p/orient a b c,
    orient a b p/orient a b c]
  let v : Fin 3 → ℝ × ℝ := ![a,b,c]
  apply mem_convexHull_of_exists_fintype w v
  · intro i
    fin_cases i <;> dsimp [w] <;> exact div_nonneg (by assumption) hD.le
  · simp only [w,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
    have hsum : orient b c p+orient c a p+orient a b p=orient a b c := by dsimp [orient]; ring
    rw [← add_div,← add_div,← add_assoc,hsum,div_self (ne_of_gt hD)]
  · intro i
    fin_cases i <;> simp [v]
  · ext <;> simp only [w,v,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals field_simp [ne_of_gt hD]; dsimp [orient]; ring

/-- A rectangular closed box is exactly the convex hull of its four corners,
including boxes with zero width or height. -/
theorem rectangle_hull {x0 x1 y0 y1 : ℝ} (hx : x0≤x1) (hy : y0≤y1) :
    convexHull ℝ ({(x0,y0),(x1,y0),(x1,y1),(x0,y1)} : Set (ℝ × ℝ))=
      Icc x0 x1 ×ˢ Icc y0 y1 := by
  have he : ({(x0,y0),(x1,y0),(x1,y1),(x0,y1)} : Set (ℝ × ℝ))=
      ({x0,x1} : Set ℝ) ×ˢ ({y0,y1} : Set ℝ) := by
    ext p
    simp only [mem_insert_iff,mem_singleton_iff,mem_prod]
    rcases p with ⟨x,y⟩
    simp only [Prod.mk.injEq]
    tauto
  rw [he,convexHull_prod,convexHull_pair,convexHull_pair,segment_eq_Icc hx,segment_eq_Icc hy]

theorem mem_rectangle_hull {x0 x1 y0 y1 : ℝ} {p : ℝ × ℝ}
    (hx : p.1∈Icc x0 x1) (hy : p.2∈Icc y0 y1) :
    p∈convexHull ℝ ({(x0,y0),(x1,y0),(x1,y1),(x0,y1)} : Set (ℝ × ℝ)) := by
  rw [rectangle_hull (hx.1.trans hx.2) (hy.1.trans hy.2)]
  exact ⟨hx,hy⟩

/-- A convex quadrilateral split along a diagonal. The four non-strict side
conditions include all boundary points. -/
theorem mem_quadrilateral_of_orient {a b c d p : ℝ × ℝ}
    (habc : 0<orient a b c) (hacd : 0<orient a c d)
    (hab : 0≤orient a b p) (hbc : 0≤orient b c p)
    (hcd : 0≤orient c d p) (hda : 0≤orient d a p) :
    p∈convexHull ℝ ({a,b,c,d} : Set (ℝ × ℝ)) := by
  by_cases hac : 0≤orient a c p
  · have hh := mem_triangle_of_orient hacd hac hcd hda
    exact convexHull_mono (by intro x hx; simp only [mem_insert_iff,mem_singleton_iff] at *; tauto) hh
  · have hca : 0≤orient c a p := by rw [orient_swap]; linarith
    have hh := mem_triangle_of_orient habc hab hbc hca
    exact convexHull_mono (by intro x hx; simp only [mem_insert_iff,mem_singleton_iff] at *; tauto) hh

/-- Six consecutive oriented triangles cover any point satisfying all outer
half-plane inequalities and one of the two indicated endpoint ray brackets.
This finite sign-change argument includes every boundary point. -/
theorem six_fan_cover {a p : ℝ × ℝ} (v : Fin 7 → ℝ × ℝ)
    (hD : ∀ i : Fin 6,0<orient a (v i.castSucc) (v i.succ))
    (hs : ∀ i : Fin 6,0≤orient (v i.castSucc) (v i.succ) p)
    (hends : (0≤orient a (v 0) p ∧ orient a (v 4) p≤0) ∨
      (0≤orient a (v 3) p ∧ orient a (v 6) p≤0)) :
    ∃ i : Fin 6,p∈convexHull ℝ ({a,v i.castSucc,v i.succ} : Set (ℝ × ℝ)) := by
  have hm (i : Fin 6) (hl : 0≤orient a (v i.castSucc) p)
      (hr : orient a (v i.succ) p≤0) :
      p∈convexHull ℝ ({a,v i.castSucc,v i.succ} : Set (ℝ × ℝ)) := by
    apply mem_triangle_of_orient (hD i) hl (hs i)
    rw [orient_swap]
    linarith
  rcases hends with hl | hr
  · by_cases h1 : 0≤orient a (v 1) p
    · by_cases h2 : 0≤orient a (v 2) p
      · by_cases h3 : 0≤orient a (v 3) p
        · exact ⟨3,hm 3 h3 hl.2⟩
        · exact ⟨2,hm 2 h2 (le_of_not_ge h3)⟩
      · exact ⟨1,hm 1 h1 (le_of_not_ge h2)⟩
    · exact ⟨0,hm 0 hl.1 (le_of_not_ge h1)⟩
  · by_cases h4 : 0≤orient a (v 4) p
    · by_cases h5 : 0≤orient a (v 5) p
      · exact ⟨5,hm 5 h5 hr.2⟩
      · exact ⟨4,hm 4 h4 (le_of_not_ge h5)⟩
    · exact ⟨3,hm 3 hr.1 (le_of_not_ge h4)⟩

end SparseLowerTail.Section05.Planar

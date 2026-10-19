import SparseLowerTail.Section05.CoverGeometryConstants

/-! Exact coverage by the six apex triangles. The top closing triangle is
unnecessary below the apex height; all boundary cases are retained. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Planar

/-- Every actual apex triangle has strictly positive orientation. -/
theorem fan_orientation (i : Fin 6) :
    0<orient criticalPoint (fanVertex i.castSucc) (fanVertex i.succ) := by
  have hb := criticalPoint_box
  fin_cases i
  · change 0<orient criticalPoint (3766810728332683/9007199254740992,8336703342218073/18014398509481984) (934947282642115/2251799813685248,4150517416584649/9007199254740992)
    norm_num [orient,criticalPoint]
    nlinarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]
  · change 0<orient criticalPoint (934947282642115/2251799813685248,4150517416584649/9007199254740992) (3676738735785273/9007199254740992,4078459822546721/9007199254740992)
    norm_num [orient,criticalPoint]
    nlinarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]
  · change 0<orient criticalPoint (3676738735785273/9007199254740992,4078459822546721/9007199254740992) (1860887366029489/4503599627370496,248429814444825/562949953421312)
    norm_num [orient,criticalPoint]
    nlinarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]
  · change 0<orient criticalPoint (1860887366029489/4503599627370496,248429814444825/562949953421312) (8164125404497235/18014398509481984,248429814444825/562949953421312)
    norm_num [orient,criticalPoint]
    nlinarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]
  · change 0<orient criticalPoint (8164125404497235/18014398509481984,248429814444825/562949953421312) (8020010216421379/18014398509481984,1035377554332477/2251799813685248)
    norm_num [orient,criticalPoint]
    nlinarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]
  · change 0<orient criticalPoint (8020010216421379/18014398509481984,1035377554332477/2251799813685248) (7983981419402415/18014398509481984,4169432535019605/9007199254740992)
    norm_num [orient,criticalPoint]
    nlinarith [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]


/-- All points below the apex satisfying the six outer half-plane conditions
belong to an actual fan cell. No polygon-area or open-interior argument is used. -/
theorem mem_fan_of_outer_sides {p : ℝ × ℝ} (hp : p.2≤criticalCost)
    (hs : ∀ i : Fin 6,0≤orient (fanVertex i.castSucc) (fanVertex i.succ) p) :
    ∃ i : Fin 6,p∈cellRegion (i.castAdd 6) := by
  have hb := criticalPoint_box
  have h0x : (fanVertex 0).1≤criticalMean := by change 3766810728332683/9007199254740992≤criticalMean; linarith [hb.1]
  have h0y : criticalCost≤(fanVertex 0).2 := by change criticalCost≤8336703342218073/18014398509481984; linarith [hb.2.2.2]
  have h3x : (fanVertex 3).1≤criticalMean := by change 1860887366029489/4503599627370496≤criticalMean; linarith [hb.1]
  have h3y : (fanVertex 3).2≤criticalCost := by change 248429814444825/562949953421312≤criticalCost; linarith [hb.2.2.1]
  have h4x : criticalMean≤(fanVertex 4).1 := by change criticalMean≤8164125404497235/18014398509481984; linarith [hb.2.1]
  have h4y : (fanVertex 4).2≤criticalCost := by change 248429814444825/562949953421312≤criticalCost; linarith [hb.2.2.1]
  have h6x : criticalMean≤(fanVertex 6).1 := by change criticalMean≤7983981419402415/18014398509481984; linarith [hb.2.1]
  have h6y : criticalCost≤(fanVertex 6).2 := by change criticalCost≤4169432535019605/9007199254740992; linarith [hb.2.2.2]
  have hends : (0≤orient criticalPoint (fanVertex 0) p ∧ orient criticalPoint (fanVertex 4) p≤0) ∨
      (0≤orient criticalPoint (fanVertex 3) p ∧ orient criticalPoint (fanVertex 6) p≤0) := by
    dsimp only [orient,criticalPoint]
    by_cases hx : p.1≤criticalMean
    · left
      constructor
      · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h0y) (sub_nonpos.mpr hx)).trans
          (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h0x) (sub_nonpos.mpr hp)))
      · have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h4x) (sub_nonpos.mpr hp)
        have h2 := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h4y) (sub_nonpos.mpr hx)
        linarith
    · right
      have hx' := (lt_of_not_ge hx).le
      constructor
      · have h1 := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h3x) (sub_nonpos.mpr hp)
        have h2 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h3y) (sub_nonneg.mpr hx')
        linarith
      · have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h6x) (sub_nonpos.mpr hp)
        have h2 := mul_nonneg (sub_nonneg.mpr h6y) (sub_nonneg.mpr hx')
        linarith
  obtain ⟨i,hi⟩ := six_fan_cover fanVertex fan_orientation hs hends
  refine ⟨i,?_⟩
  fin_cases i <;> simpa [cellRegion,cellVertices,Matrix.cons_val] using hi

end SparseLowerTail.Section05.CoverGeometry

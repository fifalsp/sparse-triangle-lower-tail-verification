import SparseLowerTail.Section05.CoverFanGeometry

/-! Exact planar enclosure coverage by the twelve certificate cells.
The curved critical-region inclusion is a separate analytic prerequisite. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Planar

theorem mem_S1_of_bounds {p : ℝ × ℝ}
    (hx : p.1∈Icc (7872292148643627/36028797018963968:ℝ) (5944751508129055/18014398509481984))
    (hy : p.2∈Icc (8304637712871195/18014398509481984:ℝ) (8336703342218073/18014398509481984)) : p∈cellRegion 6 := by
  have he : cellVertices 6={(7872292148643627/36028797018963968,8304637712871195/18014398509481984),(5944751508129055/18014398509481984,8304637712871195/18014398509481984),(5944751508129055/18014398509481984,8336703342218073/18014398509481984),(7872292148643627/36028797018963968,8336703342218073/18014398509481984)} := rfl
  rw [cellRegion,he,Finset.coe_insert,Finset.coe_insert,Finset.coe_insert,Finset.coe_singleton]
  exact mem_rectangle_hull hx hy

theorem mem_S2_of_bounds {p : ℝ × ℝ}
    (hx : p.1∈Icc (5944751508129055/18014398509481984:ℝ) (3422735716801577/9007199254740992))
    (hy : p.2∈Icc (4003700068732371/9007199254740992:ℝ) (8336703342218073/18014398509481984)) : p∈cellRegion 7 := by
  have he : cellVertices 7={(5944751508129055/18014398509481984,4003700068732371/9007199254740992),(3422735716801577/9007199254740992,4003700068732371/9007199254740992),(3422735716801577/9007199254740992,8336703342218073/18014398509481984),(5944751508129055/18014398509481984,8336703342218073/18014398509481984)} := rfl
  rw [cellRegion,he,Finset.coe_insert,Finset.coe_insert,Finset.coe_insert,Finset.coe_singleton]
  exact mem_rectangle_hull hx hy

theorem mem_S3_of_bounds {p : ℝ × ℝ}
    (hx : p.1∈Icc (3422735716801577/9007199254740992:ℝ) (3766810728332683/9007199254740992))
    (hy : p.2∈Icc (4003700068732371/9007199254740992:ℝ) (8336703342218073/18014398509481984)) : p∈cellRegion 8 := by
  have he : cellVertices 8={(3422735716801577/9007199254740992,4003700068732371/9007199254740992),(3766810728332683/9007199254740992,4003700068732371/9007199254740992),(3766810728332683/9007199254740992,8336703342218073/18014398509481984),(3422735716801577/9007199254740992,8336703342218073/18014398509481984)} := rfl
  rw [cellRegion,he,Finset.coe_insert,Finset.coe_insert,Finset.coe_insert,Finset.coe_singleton]
  exact mem_rectangle_hull hx hy

theorem mem_B1_of_bounds {p : ℝ × ℝ}
    (hx : p.1∈Icc (7872292148643627/36028797018963968:ℝ) (5944751508129055/18014398509481984))
    (hy : p.2∈Icc (3512807709348987/9007199254740992:ℝ) (519602807007871/1125899906842624)) : p∈cellRegion 10 := by
  have he : cellVertices 10={(7872292148643627/36028797018963968,3512807709348987/9007199254740992),(5944751508129055/18014398509481984,3512807709348987/9007199254740992),(5944751508129055/18014398509481984,519602807007871/1125899906842624),(7872292148643627/36028797018963968,519602807007871/1125899906842624)} := rfl
  rw [cellRegion,he,Finset.coe_insert,Finset.coe_insert,Finset.coe_insert,Finset.coe_singleton]
  exact mem_rectangle_hull hx hy

theorem mem_B2_of_bounds {p : ℝ × ℝ}
    (hx : p.1∈Icc (5944751508129055/18014398509481984:ℝ) (2296835809958953/4503599627370496))
    (hy : p.2∈Icc (6034823500676465/18014398509481984:ℝ) (8016407336719483/18014398509481984)) : p∈cellRegion 11 := by
  have he : cellVertices 11={(5944751508129055/18014398509481984,6034823500676465/18014398509481984),(2296835809958953/4503599627370496,6034823500676465/18014398509481984),(2296835809958953/4503599627370496,8016407336719483/18014398509481984),(5944751508129055/18014398509481984,8016407336719483/18014398509481984)} := rfl
  rw [cellRegion,he,Finset.coe_insert,Finset.coe_insert,Finset.coe_insert,Finset.coe_singleton]
  exact mem_rectangle_hull hx hy

/-- R1's exact slanted-side criterion. -/
theorem mem_R1_of_bounds {p : ℝ × ℝ}
    (hx : p.1≤(2296835809958953/4503599627370496:ℝ))
    (hy : p.2∈Icc (248429814444825/562949953421312:ℝ) (4169432535019605/9007199254740992))
    (hside : 0≤orient (fanVertex 6) (fanVertex 4) p) : p∈cellRegion 9 := by
  have he : cellVertices 9={(8164125404497235/18014398509481984,248429814444825/562949953421312),(2296835809958953/4503599627370496,248429814444825/562949953421312),(2296835809958953/4503599627370496,4169432535019605/9007199254740992),(7983981419402415/18014398509481984,4169432535019605/9007199254740992)} := rfl
  rw [cellRegion,he,Finset.coe_insert,Finset.coe_insert,Finset.coe_insert,Finset.coe_singleton]
  apply mem_quadrilateral_of_orient
  · norm_num [orient]
  · norm_num [orient]
  · dsimp [orient]; nlinarith [hy.1]
  · dsimp [orient]; nlinarith
  · dsimp [orient]; nlinarith [hy.2]
  · exact hside

/-- The two rational outward rectangles used in planar_coverage.py.
Their endpoints are decimal rationals, unlike the dyadic cell coordinates. -/
def outerBoxes : Set (ℝ × ℝ) :=
  (Icc (2186/10000:ℝ) (3301/10000) ×ˢ Icc (391/1000:ℝ) (4627799/10000000)) ∪
  (Icc (3301/10000:ℝ) (5095/10000) ×ˢ Icc (3355/10000:ℝ) (4627799/10000000))

/-- Exact planar coverage below the actual apex height. Closed side inequalities
cover the boundaries directly; no zero-area remainder is discarded. -/
theorem outerBoxes_below_apex_covered {p : ℝ × ℝ} (hp : p∈outerBoxes)
    (hF : p.2≤criticalCost) : ∃ i : Fin 12,p∈cellRegion i := by
  have hmlo : (2186/10000:ℝ)≤p.1 := by
    rcases hp with hp | hp <;> linarith [hp.1.1]
  have hmhi : p.1≤(5095/10000:ℝ) := by
    rcases hp with hp | hp <;> linarith [hp.1.2]
  have hFlo : (3355/10000:ℝ)≤p.2 := by
    rcases hp with hp | hp <;> linarith [hp.2.1]
  have hFhi : p.2≤(4627799/10000000:ℝ) := hF.trans criticalPoint_box.2.2.2
  by_cases hx1 : p.1≤(5944751508129055/18014398509481984:ℝ)
  · have hFleft : (391/1000:ℝ)≤p.2 := by
      rcases hp with hp | hp
      · exact hp.2.1
      · linarith [hp.1.1]
    by_cases hy1 : p.2≤(519602807007871/1125899906842624:ℝ)
    · exact ⟨10,mem_B1_of_bounds ⟨by linarith,hx1⟩ ⟨by linarith,hy1⟩⟩
    · exact ⟨6,mem_S1_of_bounds ⟨by linarith,hx1⟩ ⟨by linarith,by linarith⟩⟩
  · by_cases hy2 : p.2≤(8016407336719483/18014398509481984:ℝ)
    · exact ⟨11,mem_B2_of_bounds ⟨by linarith,by linarith⟩ ⟨by linarith,hy2⟩⟩
    · by_cases hx2 : p.1≤(3422735716801577/9007199254740992:ℝ)
      · exact ⟨7,mem_S2_of_bounds ⟨by linarith,hx2⟩ ⟨by linarith,by linarith⟩⟩
      · by_cases hx3 : p.1≤(fanVertex 0).1
        · exact ⟨8,mem_S3_of_bounds ⟨by linarith,hx3⟩ ⟨by linarith,by linarith⟩⟩
        · by_cases hside : 0≤orient (fanVertex 6) (fanVertex 4) p
          · exact ⟨9,mem_R1_of_bounds (by linarith) ⟨by linarith,by linarith⟩ hside⟩
          · have hleft : (3766810728332683/9007199254740992:ℝ)≤p.1 := le_of_not_ge hx3
            have hbottom : (8016407336719483/18014398509481984:ℝ)≤p.2 := le_of_not_ge hy2
            have hdiag : 0≤orient (8164125404497235/18014398509481984,248429814444825/562949953421312) (7983981419402415/18014398509481984,4169432535019605/9007199254740992) p := by
              change 0≤orient (fanVertex 4) (fanVertex 6) p
              rw [orient_swap]
              linarith
            have hs : ∀ i : Fin 6,0≤orient (fanVertex i.castSucc) (fanVertex i.succ) p := by
              intro i
              fin_cases i
              · change 0≤orient (3766810728332683/9007199254740992,8336703342218073/18014398509481984) (934947282642115/2251799813685248,4150517416584649/9007199254740992) p
                norm_num [orient]
                nlinarith only [hleft,hbottom,hFhi]
              · change 0≤orient (934947282642115/2251799813685248,4150517416584649/9007199254740992) (3676738735785273/9007199254740992,4078459822546721/9007199254740992) p
                norm_num [orient]
                nlinarith only [hleft,hbottom,hFhi]
              · change 0≤orient (3676738735785273/9007199254740992,4078459822546721/9007199254740992) (1860887366029489/4503599627370496,248429814444825/562949953421312) p
                norm_num [orient]
                nlinarith only [hleft,hbottom,hFhi]
              · change 0≤orient (1860887366029489/4503599627370496,248429814444825/562949953421312) (8164125404497235/18014398509481984,248429814444825/562949953421312) p
                norm_num [orient]
                nlinarith only [hleft,hbottom,hFhi]
              · change 0≤orient (8164125404497235/18014398509481984,248429814444825/562949953421312) (8020010216421379/18014398509481984,1035377554332477/2251799813685248) p
                norm_num [orient]
                norm_num [orient] at hdiag
                nlinarith only [hdiag,hbottom,hFhi]
              · change 0≤orient (8020010216421379/18014398509481984,1035377554332477/2251799813685248) (7983981419402415/18014398509481984,4169432535019605/9007199254740992) p
                norm_num [orient]
                norm_num [orient] at hdiag
                nlinarith only [hdiag,hbottom,hFhi]
            obtain ⟨i,hi⟩ := mem_fan_of_outer_sides hF hs
            exact ⟨i.castAdd 6,hi⟩

end SparseLowerTail.Section05.CoverGeometry

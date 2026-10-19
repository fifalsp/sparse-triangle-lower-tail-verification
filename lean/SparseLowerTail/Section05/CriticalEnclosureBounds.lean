import SparseLowerTail.Section05.CoverPlanarCoverage

/-! One-variable analytic bounds for the curved critical-region enclosure.
Rational log endpoints and cube-root witnesses are checked separately. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Section02 Section04 Numerics

/-- A positive lower bound on β across an interval from one log upper bound. -/
theorem beta_interval_lower {lo hi m H : ℝ} (hlo : 0<lo) (hhi : hi<1)
    (hm : m∈Icc lo hi) (hlog : Real.log hi≤H) (hn : 0≤lo-1-H) :
    (lo-1-H)/(1-lo)^2≤beta m := by
  have hm0 : 0<m := hlo.trans_le hm.1
  have hm1 : m<1 := hm.2.trans_lt hhi
  have hlo1 : lo<1 := hm.1.trans_lt hm1
  have hnumer : lo-1-H≤m-1-Real.log m := by
    have hh := (Real.log_le_log hm0 hm.2).trans hlog
    linarith [hm.1]
  have hden : (1-m)^2≤(1-lo)^2 := by nlinarith [hm.1]
  unfold beta
  apply (div_le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hlo1))
    (sq_pos_of_pos (sub_pos.mpr hm1))).mpr
  calc
    _ ≤ (lo-1-H)*(1-lo)^2 := mul_le_mul_of_nonneg_left hden hn
    _ ≤ _ := mul_le_mul_of_nonneg_right hnumer (sq_nonneg _)

/-- A rational cuberoot witness gives a lower bound on the two-thirds power. -/
theorem square_le_deficit_rpow {q z : ℝ} (hq : 0≤q) (hz : q^3≤z) :
    q^2≤(max z 0)^(2/3:ℝ) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hq 3) (hz.trans (le_max_left z 0))
    (by norm_num : (0:ℝ)≤2/3)
  have he : (q^3)^(2/3:ℝ)=q^2 := by
    rw [← Real.rpow_natCast q 3,← Real.rpow_mul hq]
    norm_num
  rwa [he] at hh

/-- Exact interval lower bound for the actual curved boundary. -/
theorem criticalFB1_interval_lower {lo hi m L H q T : ℝ}
    (hlo : 0<lo) (hhi : hi<1) (hm : m∈Icc lo hi)
    (hlog : Bounds (Real.log hi) L H) (hn : 0≤lo-1-H)
    (hq : 0≤q) (ht : criticalTriangle≤T) (hroot : q^3≤lo^3-T) :
    hi*L-hi+1+((lo-1-H)/(1-lo)^2)*q^2≤criticalFB1 m := by
  have hm0 : 0<m := hlo.trans_le hm.1
  have hm1 : m<1 := hm.2.trans_lt hhi
  have hhi0 : 0<hi := hm0.trans_le hm.2
  have he : hi*L-hi+1≤entropy m := by
    have hh := strictAntiOn_entropy.antitoneOn ⟨hm0.le,hm1.le⟩ ⟨hhi0.le,hhi.le⟩ hm.2
    have hlogmul := mul_le_mul_of_nonneg_left hlog.1 hhi0.le
    unfold entropy at hh ⊢
    linarith
  have hb := beta_interval_lower hlo hhi hm hlog.2 hn
  have hb0 : 0≤(lo-1-H)/(1-lo)^2 := div_nonneg hn (sq_nonneg _)
  have hm3 : lo^3≤m^3 := by gcongr; exact hm.1
  have hpow := square_le_deficit_rpow hq (show q^3≤m^3-criticalTriangle by linarith)
  have hp := mul_le_mul hb hpow (sq_nonneg q) (hb0.trans hb)
  exact add_le_add he hp

end SparseLowerTail.Section05.CoverGeometry

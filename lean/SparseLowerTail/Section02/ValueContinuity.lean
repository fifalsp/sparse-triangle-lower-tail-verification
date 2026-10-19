import SparseLowerTail.Section02.Push
import SparseLowerTail.Section04.EulerLagrange

/-!
# Continuity of the unrestricted variational value

Manuscript `lem:existence`(b), without an attainment assumption. Taking infima
over scaled competitors gives the quantitative bound directly.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section02

theorem antitoneOn_value : AntitoneOn value (Icc (0 : ℝ) 1) := by
  intro s hs r _ hsr
  apply le_csInf
    (show {v | ∃ U : Graphon, Feasible s U ∧ cost U = v}.Nonempty from
      ⟨_, constant s hs, constant_feasible s hs, rfl⟩)
  rintro v ⟨U, hU, rfl⟩
  apply value_le_cost
  exact hU.trans (pow_le_pow_left₀ hs.1 hsr 3)

theorem value_sub_le_scale_loss {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hr : r ≤ 1) : value s - value r ≤ 1 - s/r := by
  have hrp : 0 < r := hs.trans_le hsr
  have hscale : s/r ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos hs hrp, (div_le_one hrp).mpr hsr⟩
  have hlo : value s - (1-s/r) ≤ value r := by
    apply le_csInf
      (show {v | ∃ U : Graphon, Feasible r U ∧ cost U = v}.Nonempty from
        ⟨_, constant r ⟨hrp.le, hr⟩, constant_feasible r ⟨hrp.le, hr⟩, rfl⟩)
    rintro v ⟨U, hU, rfl⟩
    have hf : Feasible s (scaledGraphon U (s/r) ⟨hscale.1.le, hscale.2⟩) := by
      change triangle _ ≤ s^3
      rw [triangle_scaledGraphon]
      calc
        (s/r)^3*triangle U ≤ (s/r)^3*r^3 :=
          mul_le_mul_of_nonneg_left hU (pow_nonneg hscale.1.le _)
        _ = s^3 := by rw [← mul_pow, div_mul_cancel₀ _ hrp.ne']
    have hv := value_le_cost hf
    have hc := Section04.scaledGraphon_cost_le U hscale
    change cost (scaledGraphon U (s/r) ⟨hscale.1.le, hscale.2⟩) ≤ cost U + 1-s/r at hc
    linarith
  linarith

/-- Exact quantitative conclusion in `lem:existence`(b). -/
theorem value_difference_bounds {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hr : r ≤ 1) : 0 ≤ value s - value r ∧ value s - value r ≤ 1-s/r := by
  exact ⟨sub_nonneg.mpr (antitoneOn_value ⟨hs.le, hsr.trans hr⟩
    ⟨hs.le.trans hsr, hr⟩ hsr), value_sub_le_scale_loss hs hsr hr⟩

/-- Uniform Lipschitz estimate away from target zero. -/
theorem value_abs_sub_le {a s r : ℝ} (ha : 0 < a)
    (hs : s ∈ Icc a 1) (hr : r ∈ Icc a 1) :
    |value s-value r| ≤ |s-r|/a := by
  have ordered : ∀ {s r : ℝ}, s ∈ Icc a 1 → r ∈ Icc a 1 → s ≤ r →
      |value s-value r| ≤ |s-r|/a := by
    intro s r hs hr hsr
    have hsp := ha.trans_le hs.1
    have hrp := ha.trans_le hr.1
    obtain ⟨hlo,hhi⟩ := value_difference_bounds hsp hsr hr.2
    rw [abs_of_nonneg hlo, abs_of_nonpos (sub_nonpos.mpr hsr), neg_sub]
    calc
      value s-value r ≤ 1-s/r := hhi
      _ = (r-s)/r := by field_simp
      _ ≤ (r-s)/a := div_le_div_of_nonneg_left (sub_nonneg.mpr hsr) ha hr.1
  rcases le_total s r with hsr | hrs
  · exact ordered hs hr hsr
  · simpa only [abs_sub_comm] using ordered hr hs hrs

theorem continuousOn_value : ContinuousOn value (Ioo (0 : ℝ) 1) := by
  intro r hr
  have hrp := hr.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (r/2) (ε*(r/2)), lt_min (by linarith) (mul_pos hε (by linarith)), ?_⟩
  intro s hs hdist
  have hd : |s-r| < min (r/2) (ε*(r/2)) := by simpa [Real.dist_eq] using hdist
  have hsr : r/2 ≤ s := by
    have hab := (abs_lt.mp (hd.trans_le (min_le_left _ _))).1
    linarith
  have hb := value_abs_sub_le (show 0 < r/2 by linarith)
    (show s ∈ Icc (r/2) 1 from ⟨hsr, hs.2.le⟩)
    (show r ∈ Icc (r/2) 1 from ⟨by linarith, hr.2.le⟩)
  rw [Real.dist_eq]
  apply hb.trans_lt
  apply (div_lt_iff₀ (show 0 < r/2 by linarith)).mpr
  exact hd.trans_le (min_le_right _ _)

end SparseLowerTail.Section02

import SparseLowerTail.Section02.Bregman
import SparseLowerTail.Section04.BalancedStationary

/-! Full quantitative graphon mean gap, manuscript lem:meangap.
The squared deviation is the actual integral of (U-s)^2 on the unit square. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section02

/-- The square of the L² distance from the constant s. -/
def squareDeviation (U : Graphon) (s : ℝ) : ℝ := ∫ p, (U p-s)^2 ∂squareMeasure

theorem edgeDensity_mem_Icc (U : Graphon) : edgeDensity U ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact integral_nonneg_of_ae (U.bounded.mono fun _ h => h.1)
  · have h := integral_mono_ae (graphon_integrable U) (integrable_const (1:ℝ))
      (U.bounded.mono fun _ h => h.2)
    simpa using h

theorem constant_value_mem_Icc {U : Graphon} {c : ℝ} (hc : IsConstant U c) : c ∈ Icc (0:ℝ) 1 := by
  obtain ⟨p, hp, he⟩ := (U.bounded.and hc).exists
  simpa only [he] using hp

theorem edgeDensity_zero_iff (U : Graphon) : edgeDensity U = 0 ↔ IsConstant U 0 :=
  integral_eq_zero_iff_of_nonneg_ae (U.bounded.mono fun _ h => h.1) (graphon_integrable U)

theorem edgeDensity_one_iff (U : Graphon) : edgeDensity U = 1 ↔ IsConstant U 1 := by
  have hi := (integrable_const (1:ℝ)).sub (graphon_integrable U)
  have hn : 0 ≤ᵐ[squareMeasure] (fun p => 1-U p) :=
    U.bounded.mono fun _ h => sub_nonneg.mpr h.2
  have he := integral_eq_zero_iff_of_nonneg_ae hn hi
  rw [integral_sub (integrable_const (1:ℝ)) (graphon_integrable U)] at he
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at he
  constructor
  · intro hm
    have hz : (fun p => 1-U p) =ᵐ[squareMeasure] 0 := he.mp (by change 1-edgeDensity U=0; rw [hm]; ring)
    filter_upwards [hz] with p hp
    change 1-U p=0 at hp
    linarith
  · intro hc
    have hz : (fun p => 1-U p) =ᵐ[squareMeasure] 0 := by
      filter_upwards [hc] with p hp
      change 1-U p=0
      change U p=1 at hp
      rw [hp]
      ring
    have h := he.mpr hz
    change 1-edgeDensity U=0 at h
    linarith

theorem edgeDensity_mem_Ioo_of_nonconstant {U : Graphon} (hn : ¬∃ c, IsConstant U c) :
    edgeDensity U ∈ Ioo (0:ℝ) 1 := by
  have hm := edgeDensity_mem_Icc U
  constructor
  · by_contra h
    have he : edgeDensity U=0 := le_antisymm (le_of_not_gt h) hm.1
    exact hn ⟨0, (edgeDensity_zero_iff U).mp he⟩
  · by_contra h
    have he : edgeDensity U=1 := le_antisymm hm.2 (le_of_not_gt h)
    exact hn ⟨1, (edgeDensity_one_iff U).mp he⟩

theorem squareDeviation_integrable (U : Graphon) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    Integrable (fun p => (U p-s)^2) squareMeasure := by
  apply Integrable.of_bound (((U.measurable.sub_const s).pow_const 2).aestronglyMeasurable) 1
  filter_upwards [U.bounded] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [hp.1, hp.2, hs.1, hs.2, sq_nonneg (U p-s)]

theorem squareDeviation_nonneg (U : Graphon) (s : ℝ) : 0 ≤ squareDeviation U s :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem squareDeviation_eq_zero_iff (U : Graphon) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    squareDeviation U s=0 ↔ IsConstant U s := by
  have he := integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun p => sq_nonneg (U p-s))) (squareDeviation_integrable U hs)
  constructor
  · intro h
    have hz := he.mp h
    filter_upwards [hz] with p hp
    change (U p-s)^2=0 at hp
    nlinarith [hp]
  · intro h
    apply he.mpr
    filter_upwards [h] with p hp
    change U p=s at hp
    change (U p-s)^2=0
    rw [hp]
    ring

/-- Integrating the full Bregman inequality, with its affine mean term retained. -/
theorem graphon_bregman (U : Graphon) {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    entropy s + (edgeDensity U-s)*Real.log s + beta s*squareDeviation U s ≤ cost U := by
  have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hvar := squareDeviation_integrable U hs'
  have hdev := (graphon_integrable U).sub (integrable_const s)
  have hrhs := ((cost_integrable U).sub (integrable_const (entropy s))).sub (hdev.mul_const (Real.log s))
  have hi := integral_mono_ae (hvar.const_mul (beta s)) hrhs
    (U.bounded.mono fun _ h => entropy_bregman hs h)
  simp only [Pi.sub_apply] at hi
  rw [integral_const_mul, integral_sub (f := fun p => entropy (U p)-entropy s)
      (g := fun p => (U p-s)*Real.log s) ((cost_integrable U).sub (integrable_const (entropy s)))
      (hdev.mul_const (Real.log s)),
    integral_sub (cost_integrable U) (integrable_const (entropy s)), integral_mul_const,
    integral_sub (f := U.toFun) (g := fun _ => s) (graphon_integrable U) (integrable_const s)] at hi
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
  change beta s*squareDeviation U s ≤ cost U-entropy s-(edgeDensity U-s)*Real.log s at hi
  linarith

/-- The quantitative inequality in lem:meangap, before asserting strictness. -/
theorem graphon_mean_bregman (U : Graphon) (hm : edgeDensity U ∈ Ioo (0:ℝ) 1) :
    entropy (edgeDensity U)+beta (edgeDensity U)*squareDeviation U (edgeDensity U) ≤ cost U := by
  simpa using graphon_bregman U hm

/-- Strictness follows from a positive squared L² deviation, not a qualitative Jensen assumption. -/
theorem graphon_mean_gap {U : Graphon} (hn : ¬∃ c, IsConstant U c) :
    edgeDensity U ∈ Ioo (0:ℝ) 1 ∧
    entropy (edgeDensity U)+beta (edgeDensity U)*squareDeviation U (edgeDensity U) ≤ cost U ∧
    entropy (edgeDensity U) < cost U := by
  have hm := edgeDensity_mem_Ioo_of_nonconstant hn
  have hv : 0 < squareDeviation U (edgeDensity U) := by
    apply lt_of_le_of_ne (squareDeviation_nonneg U _)
    intro he
    exact hn ⟨_, (squareDeviation_eq_zero_iff U ⟨hm.1.le, hm.2.le⟩).mp he.symm⟩
  have hbeta : 0 < beta (edgeDensity U) := lt_of_lt_of_le (by norm_num) (beta_ge_half hm)
  have hb := graphon_mean_bregman U hm
  exact ⟨hm, hb, by nlinarith [mul_pos hbeta hv]⟩

/-- The strict edge-density conclusion in lem:meangap. -/
theorem edgeDensity_gt_target {r : ℝ} {U : Graphon} (hr : r ∈ Ioo (0:ℝ) 1)
    (hcost : cost U ≤ entropy r) (hn : ¬∃ c, IsConstant U c) : r < edgeDensity U := by
  obtain ⟨hm, _, hg⟩ := graphon_mean_gap hn
  by_contra h
  have hle := Section04.strictAntiOn_entropy.antitoneOn ⟨hm.1.le, hm.2.le⟩ ⟨hr.1.le, hr.2.le⟩
    (le_of_not_gt h)
  linarith

/-- The constant case of lem:meangap, including arbitrary a.e. representatives. -/
theorem constant_of_cost_le_target {r c : ℝ} {U : Graphon} (hr : r ∈ Ioo (0:ℝ) 1)
    (hc : IsConstant U c) (hfeas : Feasible r U) (hcost : cost U ≤ entropy r) : c=r := by
  have hci := constant_value_mem_Icc hc
  have ht : c^3 ≤ r^3 := by
    have he := triangle_congr_ae (U:=U) (W:=constant c hci) hc
    simpa [Feasible, he] using hfeas
  have hcr : c ≤ r := (show Odd (3:ℕ) by decide).strictMono_pow.le_iff_le.mp ht
  have he : cost U=entropy c := by
    have he := cost_congr_ae (U:=U) (W:=constant c hci) hc
    simpa using he
  rcases lt_or_eq_of_le hcr with hlt | heq
  · have h := Section04.strictAntiOn_entropy hci ⟨hr.1.le, hr.2.le⟩ hlt
    linarith
  · exact heq

end SparseLowerTail.Section02

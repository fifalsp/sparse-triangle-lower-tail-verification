import SparseLowerTail.Section06.UniformApproximation
import SparseLowerTail.Section02.Patterns

/-! Edge-density control of the row-class masses in local rigidity. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section02 Section04

theorem edgeDensity_cut_bound (U W : Graphon) :
    |edgeDensity U-edgeDensity W|≤cutNorm (fun p => U p-W p) := by
  have h := abs_weighted_integral_le_cutNorm ((graphon_integrable U).sub (graphon_integrable W))
    (f:=fun _ => 1) (g:=fun _ => 1) aemeasurable_const aemeasurable_const
    (Eventually.of_forall fun _ => by constructor <;> norm_num)
    (Eventually.of_forall fun _ => by constructor <;> norm_num)
  simp only [one_mul,Pi.sub_apply,integral_sub (graphon_integrable U) (graphon_integrable W)] at h
  exact h

theorem edgeDensity_uniform_bound (U W : Graphon) {ζ : ℝ}
    (hu : ∀ᵐ p ∂squareMeasure,|U p-W p|≤ζ) : |edgeDensity U-edgeDensity W|≤ζ := by
  rw [edgeDensity,edgeDensity,← integral_sub (graphon_integrable U) (graphon_integrable W)]
  simpa only [Real.norm_eq_abs,measureReal_univ_eq_one,mul_one] using norm_integral_le_of_norm_le_const (μ:=squareMeasure) (f:=fun p => U p-W p) (by
    simpa only [Real.norm_eq_abs] using hu)

theorem edgeDensity_twoBlock_general {P : Set ℝ} (hP : MeasurableSet P)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    edgeDensity (twoBlock P hP a b ha hb)=
      (a+b)/2-2*(b-a)*(unitMeasure.real P-1/2)^2 := by
  have hc : unitMeasure.real P∈Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  have hm : unitMeasure P=ENNReal.ofReal (unitMeasure.real P) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have h := edgeDensity_bipodalGraphon hP hc hm ha ha hb
  change edgeDensity (twoBlock P hP a b ha hb)=_ at h
  rw [h]
  ring

/-- A near-balanced edge density forces the mass of either row class near 1/2. -/
theorem row_partition_mass_bound (U : Graphon) {P Q : Set ℝ}
    (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal)) (hQ : MeasurableSet Q)
    {a b ζ : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hu : ∀ᵐ p ∂squareMeasure,|U p-blockValue Q a b p|≤ζ) :
    2*(b-a)*(unitMeasure.real Q-1/2)^2≤
      cutNorm (fun p => U p-twoBlock P hP a b ha hb p)+ζ := by
  let B := twoBlock P hP a b ha hb
  let W := twoBlock Q hQ a b ha hb
  have h1 := edgeDensity_cut_bound U B
  have h2 := edgeDensity_uniform_bound U W hu
  rw [edgeDensity_twoBlock hP hm a b ha hb] at h1
  rw [edgeDensity_twoBlock_general hQ ha hb] at h2
  have hh1 := (abs_le.mp h1).1
  have hh2 := (abs_le.mp h2).2
  linarith

/-- A measurable row-class partition together with its uniform graphon approximation. -/
theorem exists_uniform_row_partition {r : ℝ} (hr : r∈Ioo (0:ℝ) 1)
    {U : Graphon} (hU : IsMinimizer r U) {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) {a b μ ε : ℝ}
    (ha : 0<a) (hab : a<b) (hb : b<1) (hμ : 0<μ) (hEL : BalancedEL a b μ)
    (hε : 0≤ε) (hclose : ∀ᵐ x ∂unitMeasure,
      min (profileL2Sq (fun y => U (x,y)) (blockProfile P a b))
        (profileL2Sq (fun y => U (x,y)) (blockProfile P b a))≤ε^2) :
    ∃ Q : Set ℝ,MeasurableSet Q ∧
      (∀ᵐ x ∂unitMeasure,profileL2Sq (fun y => U (x,y)) (assignedProfile P Q a b x)≤ε^2) ∧
      (∀ᵐ p ∂squareMeasure,|U p-blockValue Q a b p|≤
        2*graphonMultiplier U r*ε+|graphonMultiplier U r-μ|) ∧
      2*(b-a)*(unitMeasure.real Q-1/2)^2≤
        cutNorm (fun p => U p-twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩ p)+
        (2*graphonMultiplier U r*ε+|graphonMultiplier U r-μ|) := by
  classical
  obtain ⟨Q,hQ,hrows⟩ := exists_row_partition U (blockProfile_boundedObservable hP a b)
    (blockProfile_boundedObservable hP b a) hclose
  have hnear : ∀ᵐ x ∂unitMeasure,profileL2Sq (fun y => U (x,y)) (assignedProfile P Q a b x)≤ε^2 := by
    filter_upwards [hrows] with x hx
    by_cases hxQ:x∈Q
    · have he : assignedProfile P Q a b x=blockProfile P a b := by funext y; simp [assignedProfile,hxQ]
      rw [he];exact hx.1 hxQ
    · have he : assignedProfile P Q a b x=blockProfile P b a := by funext y; simp [assignedProfile,hxQ]
      rw [he];exact hx.2 hxQ
  have hu := minimizer_uniform_approximation hr hU hP hm ha hab hb hμ hEL hε hnear
  exact ⟨Q,hQ,hnear,hu,row_partition_mass_bound U hP hm hQ
    ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩ hu⟩

end SparseLowerTail.Section06

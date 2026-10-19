import SparseLowerTail.Section04.BipodalGraphon

/-! The measurable-partition part of `lem:parity` and `lem:patterns`(c).
The four allowed triangle patterns determine a two-block partition by Fubini.
Relabeling equivalence is a separate obligation (`lem:relabelB`). -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section02
open Section04 TriangleIntegration

def AllowedPattern (a b x y z : ℝ) : Prop :=
  (x=a ∧ y=a ∧ z=a) ∨ (x=a ∧ y=b ∧ z=b) ∨
  (x=b ∧ y=a ∧ z=b) ∨ (x=b ∧ y=b ∧ z=a)

/-- The number of b-valued edges in a sampled triangle. -/
def countB (b x y z : ℝ) : ℕ := by
  classical
  exact (if x=b then 1 else 0)+(if y=b then 1 else 0)+(if z=b then 1 else 0)

theorem allowedPattern_of_even {a b x y z : ℝ} (hne : a ≠ b)
    (hx : x=a ∨ x=b) (hy : y=a ∨ y=b) (hz : z=a ∨ z=b)
    (he : Even (countB b x y z)) : AllowedPattern a b x y z := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  all_goals simp_all [AllowedPattern,countB]
  exact False.elim ((by decide : ¬Even (3:ℕ)) he)

private theorem pattern_partition {a b x y z : ℝ} (hne : a ≠ b)
    (hp : AllowedPattern a b x y z) : x = if (z=b ↔ y=b) then a else b := by
  classical
  rcases hp with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals simp [hne]

/-- Fubini recovers an actual measurable two-block partition from triangle
patterns. No finite-block ansatz or stationarity premise is used. -/
theorem bipodal_of_patterns {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hne : a ≠ b) {U : Graphon}
    (hp : ∀ᵐ p ∂tripleMeasure, AllowedPattern a b (X U p) (Y U p) (Z U p)) :
    ∃ c : ℝ, IsBipodal U c a a b := by
  classical
  let v := U.measurable.mk U.toFun
  have hv : Measurable v := U.measurable.measurable_mk
  have heq : U.toFun =ᵐ[squareMeasure] v := U.measurable.ae_eq_mk
  have hpv : ∀ᵐ p ∂tripleMeasure,
      AllowedPattern a b (v p.1) (v (p.1.2,p.2)) (v (p.1.1,p.2)) := by
    filter_upwards [hp, edgeX_qmp.ae heq, edgeY_qmp.ae heq, edgeZ_qmp.ae heq]
      with p hp hx hy hz
    simpa only [X,Y,Z,hx,hy,hz] using hp
  have hs : ∀ᵐ p ∂unitMeasure.prod squareMeasure,
      AllowedPattern a b (v p.2) (v (p.2.2,p.1)) (v (p.2.1,p.1)) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpv
  obtain ⟨z,hz⟩ := (Measure.ae_ae_of_ae_prod hs).exists
  let P : Set ℝ := {x | v (x,z)=b} ∩ Icc 0 1
  have hP : MeasurableSet P :=
    (measurableSet_eq_fun (hv.comp (measurable_id.prodMk measurable_const))
      measurable_const).inter measurableSet_Icc
  have hsub : P ⊆ Icc (0:ℝ) 1 := inter_subset_right
  let c := unitMeasure.real P
  have hc : c ∈ Icc (0:ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hm : unitMeasure P = ENNReal.ofReal c := by
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  refine ⟨c,hc,ha,ha,hb,P,hP,hsub,hm,?_⟩
  have hi : ∀ᵐ x ∂unitMeasure, x ∈ Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [heq,hz, Measure.quasiMeasurePreserving_fst.ae hi,
    Measure.quasiMeasurePreserving_snd.ae hi] with p he hp hx hy
  rw [he, pattern_partition hne hp]
  have hxP : p.1 ∈ P ↔ v (p.1,z)=b := by simp [P,hx]
  have hyP : p.2 ∈ P ↔ v (p.2,z)=b := by simp [P,hy]
  simp only [bipodalBlockValue, hxP, hyP]
  split_ifs <;> simp_all

theorem edgeDensity_bipodalGraphon {P : Set ℝ} (hP : MeasurableSet P) {c : ℝ}
    (hc : c ∈ Icc 0 1) (hm : unitMeasure P = ENNReal.ofReal c)
    {a d b : ℝ} (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    edgeDensity (bipodalGraphon P hP a d b ha hd hb) =
      c^2*a+(1-c)^2*d+2*c*(1-c)*b := by
  classical
  let W := bipodalGraphon P hP a d b ha hd hb
  have hi := graphon_integrable W
  rw [edgeDensity, integral_prod _ hi]
  have hrow : ∀ x, (∫ y, W (x,y) ∂unitMeasure) =
      if x ∈ P then c*a+(1-c)*b else c*b+(1-c)*d := by
    intro x
    change (∫ y, bipodalBlockValue P a d b (x,y) ∂unitMeasure) = _
    by_cases hx : x ∈ P
    all_goals simp only [bipodalBlockValue,hx,if_true,if_false]
    all_goals exact integral_partition hP hc hm _ _
  change (∫ x, (∫ y, W (x,y) ∂unitMeasure) ∂unitMeasure) = _
  simp_rw [hrow]
  rw [integral_partition hP hc hm]
  ring

/-- An equal-diagonal two-block graphon with the balanced edge density has
equal block masses, without invoking stationarity. -/
theorem balanced_of_bipodal_edgeDensity {U : Graphon} {c a b : ℝ}
    (hB : IsBipodal U c a a b) (hne : a ≠ b)
    (he : edgeDensity U = (a+b)/2) : IsBalanced U a b := by
  obtain ⟨hc,ha,hd,hb,P,hP,hsub,hm,heq⟩ := hB
  have hi : edgeDensity U = c^2*a+(1-c)^2*a+2*c*(1-c)*b := by
    calc
      edgeDensity U = edgeDensity (bipodalGraphon P hP a a b ha hd hb) :=
        integral_congr_ae heq
      _ = _ := edgeDensity_bipodalGraphon hP hc hm ha hd hb
  have hz : (a-b)*(2*c-1)^2 = 0 := by nlinarith [he,hi]
  have hs : (2*c-1)^2 = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
  have hh : c = 1/2 := by nlinarith [sq_nonneg (2*c-1)]
  exact Section04.IsBipodal.isBalanced_of_parameters
    (show IsBipodal U c a a b from ⟨hc,ha,hd,hb,P,hP,hsub,hm,heq⟩) rfl hh

/-- `lem:patterns`(c) in measurable-partition form. -/
theorem balanced_of_patterns {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hne : a ≠ b) {U : Graphon}
    (hp : ∀ᵐ p ∂tripleMeasure, AllowedPattern a b (X U p) (Y U p) (Z U p))
    (he : edgeDensity U = (a+b)/2) : IsBalanced U a b := by
  obtain ⟨c,hB⟩ := bipodal_of_patterns ha hb hne hp
  exact balanced_of_bipodal_edgeDensity hB hne he

/-- The parity hypothesis in `lem:parity` gives exactly the four allowed patterns. -/
theorem patterns_of_even {a b : ℝ} (hne : a ≠ b) {U : Graphon}
    (hvalues : ∀ᵐ p ∂squareMeasure, U p=a ∨ U p=b)
    (hparity : ∀ᵐ p ∂tripleMeasure, Even (countB b (X U p) (Y U p) (Z U p))) :
    ∀ᵐ p ∂tripleMeasure, AllowedPattern a b (X U p) (Y U p) (Z U p) := by
  filter_upwards [edgeX_qmp.ae hvalues,edgeY_qmp.ae hvalues,edgeZ_qmp.ae hvalues,hparity]
    with p hx hy hz he
  exact allowedPattern_of_even hne hx hy hz he

/-- `lem:parity`, in actual measurable-partition form. -/
theorem parity_partition {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hne : a ≠ b) {U : Graphon}
    (hvalues : ∀ᵐ p ∂squareMeasure, U p=a ∨ U p=b)
    (hparity : ∀ᵐ p ∂tripleMeasure, Even (countB b (X U p) (Y U p) (Z U p))) :
    (∃ c : ℝ, IsBipodal U c a a b) ∧
      (edgeDensity U = (a+b)/2 → IsBalanced U a b) := by
  have hp := patterns_of_even hne hvalues hparity
  exact ⟨bipodal_of_patterns ha hb hne hp, balanced_of_patterns ha hb hne hp⟩

end SparseLowerTail.Section02

import SparseLowerTail.Section06.RowPartition

/-! The row partition gives uniform approximation by an actual two-block kernel,
using the Euler--Lagrange equation. Step 3 of `thm:rigidity`. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section02 Section04

def assignedProfile (P Q : Set ℝ) (a b : ℝ) (x y : ℝ) : ℝ := by
  classical
  exact if x∈Q then blockProfile P a b y else blockProfile P b a y

theorem blockProfile_mem (P : Set ℝ) {a b : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (x : ℝ) :
    blockProfile P a b x∈Icc (0:ℝ) 1 := by
  simp only [blockProfile]
  split_ifs <;> assumption

theorem assignedProfile_mem (P Q : Set ℝ) {a b : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (x y : ℝ) :
    assignedProfile P Q a b x y∈Icc (0:ℝ) 1 := by
  classical
  by_cases hx:x∈Q
  · simpa only [assignedProfile,if_pos hx] using blockProfile_mem P ha hb y
  · simpa only [assignedProfile,if_neg hx] using blockProfile_mem P hb ha y

theorem assignedProfile_bounded {P : Set ℝ} (hP : MeasurableSet P)
    (Q : Set ℝ) (a b x : ℝ) : BoundedObservable unitMeasure (assignedProfile P Q a b x) := by
  classical
  by_cases hx:x∈Q
  · have he : assignedProfile P Q a b x=blockProfile P a b := by funext y; simp [assignedProfile,hx]
    rw [he]; exact blockProfile_boundedObservable hP a b
  · have he : assignedProfile P Q a b x=blockProfile P b a := by funext y; simp [assignedProfile,hx]
    rw [he]; exact blockProfile_boundedObservable hP b a

theorem integral_blockProfile_product {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) (a b c d : ℝ) :
    (∫ x,blockProfile P a b x*blockProfile P c d x ∂unitMeasure)=(a*c+b*d)/2 := by
  classical
  have he : (fun x => blockProfile P a b x*blockProfile P c d x)=blockProfile P (a*c) (b*d) := by
    ext x; by_cases hx:x∈P <;> simp [blockProfile,hx]
  rw [he,integral_blockProfile hP hm]

theorem assignedProfile_inner {P : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) (Q : Set ℝ) (a b x y : ℝ) :
    (∫ z,assignedProfile P Q a b x z*assignedProfile P Q a b y z ∂unitMeasure)=
      blockValue Q ((a^2+b^2)/2) (a*b) (x,y) := by
  classical
  by_cases hx:x∈Q <;> by_cases hy:y∈Q <;>
    simp only [assignedProfile,blockValue,hx,hy,if_true,if_false] <;>
    rw [integral_blockProfile_product hP hm] <;> ring

/-- The exponential is 1-Lipschitz on the nonpositive half-line. -/
theorem exp_neg_abs_sub_le {s t : ℝ} (hs : 0≤s) (ht : 0≤t) :
    |Real.exp (-s)-Real.exp (-t)|≤|s-t| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.exp) (C:=1) (fun x (_ : x∈Iic (0:ℝ)) => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos x)]
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hx)
    (convex_Iic (0:ℝ)) (show -t∈Iic (0:ℝ) from neg_nonpos.mpr ht)
    (show -s∈Iic (0:ℝ) from neg_nonpos.mpr hs)
  simpa only [Real.norm_eq_abs,one_mul,neg_sub_neg,abs_sub_comm t s] using h

/-- Product perturbation followed by the Euler exponential. -/
theorem exp_codegree_error {ν μ C D ε : ℝ} (hν : 0≤ν) (hμ : 0≤μ)
    (hC : 0≤C) (hD : D∈Icc (0:ℝ) 1) (he : |C-D|≤2*ε) :
    |Real.exp (-ν*C)-Real.exp (-μ*D)|≤2*ν*ε+|ν-μ| := by
  have heq : ν*C-μ*D=ν*(C-D)+(ν-μ)*D := by ring
  have h := exp_neg_abs_sub_le (mul_nonneg hν hC) (mul_nonneg hμ hD.1)
  simp only [← neg_mul] at h
  apply h.trans
  rw [heq]
  have h1 := mul_le_mul_of_nonneg_left he hν
  have h2 := mul_le_mul_of_nonneg_left hD.2 (abs_nonneg (ν-μ))
  have h3 := abs_add_le (ν*(C-D)) ((ν-μ)*D)
  rw [abs_mul,abs_mul,abs_of_nonneg hν,abs_of_nonneg hD.1] at h3
  nlinarith

/-- Codegrees are uniformly close to the inner products of the assigned wells. -/
theorem codegree_assigned_error (U : Graphon) {P Q : Set ℝ}
    (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal)) {a b ε : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hε : 0≤ε)
    (hrows : ∀ᵐ x ∂unitMeasure,
      profileL2Sq (fun y => U (x,y)) (assignedProfile P Q a b x)≤ε^2) :
    ∀ᵐ p ∂squareMeasure,
      |codegree U p.1 p.2-blockValue Q ((a^2+b^2)/2) (a*b) p|≤2*ε := by
  have hrowdata : ∀ᵐ x ∂unitMeasure,
      BoundedObservable unitMeasure (fun y => U (x,y)) ∧
      (∀ᵐ y ∂unitMeasure,U (x,y)∈Icc (0:ℝ) 1) ∧
      profileL2Sq (fun y => U (x,y)) (assignedProfile P Q a b x)≤ε^2 := by
    filter_upwards [boundedObservable_slices (graphon_boundedObservable U),
      Measure.ae_ae_of_ae_prod U.bounded,hrows] with x hx hb hd
    exact ⟨hx,hb,hd⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrowdata,
    Measure.quasiMeasurePreserving_snd.ae hrowdata] with p hx hy
  have h := profile_inner_error_le hx.1 hy.1 (assignedProfile_bounded hP Q a b p.1)
    (assignedProfile_bounded hP Q a b p.2) hy.2.1
    (Eventually.of_forall fun z => assignedProfile_mem P Q ha hb p.1 z) hε hx.2.2 hy.2.2
  rw [assignedProfile_inner hP hm] at h
  exact h

/-- Actual Euler--Lagrange graphons are uniformly close to the two-block kernel
on their row-class partition. -/
theorem minimizer_uniform_approximation {r : ℝ} (hr : r∈Ioo (0:ℝ) 1)
    {U : Graphon} (hU : IsMinimizer r U) {P Q : Set ℝ} (hP : MeasurableSet P)
    (hm : unitMeasure P=(1/2:ENNReal)) {a b μ ε : ℝ}
    (ha : 0<a) (hab : a<b) (hb : b<1) (hμ : 0<μ) (hEL : BalancedEL a b μ)
    (hε : 0≤ε) (hrows : ∀ᵐ x ∂unitMeasure,
      profileL2Sq (fun y => U (x,y)) (assignedProfile P Q a b x)≤ε^2) :
    ∀ᵐ p ∂squareMeasure,
      |U p-blockValue Q a b p|≤2*graphonMultiplier U r*ε+|graphonMultiplier U r-μ| := by
  classical
  have haI : a∈Icc (0:ℝ) 1 := ⟨ha.le,(hab.trans hb).le⟩
  have hbI : b∈Icc (0:ℝ) 1 := ⟨(ha.trans hab).le,hb.le⟩
  have haa : (a^2+b^2)/2∈Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [sq_nonneg (1-a),sq_nonneg (1-b),mul_nonneg haI.1 (sub_nonneg.mpr haI.2),
        mul_nonneg hbI.1 (sub_nonneg.mpr hbI.2)]
  have habI : a*b∈Icc (0:ℝ) 1 := ⟨mul_nonneg haI.1 hbI.1,by nlinarith [mul_le_mul haI.2 hbI.2 hbI.1 (by norm_num : (0:ℝ)≤1)]⟩
  have hblock : ∀ p : ℝ × ℝ,blockValue Q a b p=
      Real.exp (-μ*blockValue Q ((a^2+b^2)/2) (a*b) p) := by
    intro p
    have h1 : a=Real.exp (-μ*((a^2+b^2)/2)) := by
      rw [← mul_div_assoc,← hEL.1,Real.exp_log ha]
    have h2 : b=Real.exp (-μ*(a*b)) := by
      rw [← mul_assoc,← hEL.2,Real.exp_log (ha.trans hab)]
    by_cases hx:p.1∈Q <;> by_cases hy:p.2∈Q <;>
      simp only [blockValue,hx,hy,if_true,if_false] <;> first | exact h1 | exact h2
  have hbd : ∀ p : ℝ × ℝ,blockValue Q ((a^2+b^2)/2) (a*b) p∈Icc (0:ℝ) 1 := by
    intro p
    simp only [blockValue]
    split_ifs <;> assumption
  filter_upwards [minimizer_exp_equation hr hU,codegree_mem_Icc_ae U,
    codegree_assigned_error U hP hm haI hbI hε hrows] with p he hc hd
  rw [he,hblock]
  exact exp_codegree_error (minimizer_multiplier_pos hr hU).le hμ.le hc.1 (hbd p) hd

end SparseLowerTail.Section06

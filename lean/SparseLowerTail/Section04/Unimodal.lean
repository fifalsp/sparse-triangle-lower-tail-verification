import SparseLowerTail.Section04.Ray
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.IntermediateValue

/-! The unimodality calculation in manuscript `lem:unimodal`. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section04

/-- The rational-logarithmic sign function in `lem:unimodal`. -/
def shapeTheta (z : ℝ) : ℝ := Real.log z + (1-z)/(1+z) +
  (z^2+1)*(1-z)^3/(2*z*(z^2+3)*(1+z))
/-- The polynomial controlling the derivative of θ. -/
def shapePolynomial (z : ℝ) : ℝ := -z^6+2*z^5-5*z^4+20*z^3-15*z^2+18*z-3

theorem hasDerivAt_shapePolynomial (z : ℝ) :
    HasDerivAt shapePolynomial
      (18-30*z+40*z^2-2*z^2*(3*z^3-5*z^2+10*z-10)) z := by
  have hi := hasDerivAt_id z
  convert (((((((hi.pow 6).neg.add ((hi.pow 5).const_mul 2)).sub
    ((hi.pow 4).const_mul 5)).add ((hi.pow 3).const_mul 20)).sub
    ((hi.pow 2).const_mul 15)).add (hi.const_mul 18)).sub_const 3) using 1
  norm_num
  ring

theorem shapePolynomial_deriv_pos {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    0 < deriv shapePolynomial z := by
  rw [(hasDerivAt_shapePolynomial z).deriv]
  have hc : 3*z^3-5*z^2+10*z-10 ≤ 0 := by
    have h1 : z^2 * (3*z-5) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z) (by linarith [hz.2])
    nlinarith [hz.2]
  have hprod : 0 ≤ -(2*z^2*(3*z^3-5*z^2+10*z-10)) := by
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc)
  have hquad : 0 < 18-30*z+40*z^2 := by nlinarith [sq_nonneg (z-3/8)]
  linarith

theorem strictMonoOn_shapePolynomial : StrictMonoOn shapePolynomial (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact fun z _ => (hasDerivAt_shapePolynomial z).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact shapePolynomial_deriv_pos ⟨le_of_lt hz.1, le_of_lt hz.2⟩

@[simp] theorem shapePolynomial_zero : shapePolynomial 0 = -3 := by norm_num [shapePolynomial]
@[simp] theorem shapePolynomial_one : shapePolynomial 1 = 16 := by norm_num [shapePolynomial]

/-- The polynomial has precisely one zero in the unit interval. -/
theorem existsUnique_shapePolynomial_zero :
    ∃! z : ℝ, z ∈ Ioo (0 : ℝ) 1 ∧ shapePolynomial z = 0 := by
  have hc : ContinuousOn shapePolynomial (Icc (0 : ℝ) 1) :=
    fun z _ => (hasDerivAt_shapePolynomial z).continuousAt.continuousWithinAt
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
    (show (0 : ℝ) ∈ Icc (shapePolynomial 0) (shapePolynomial 1) by norm_num)
  have hzi : z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · by_contra h
      have : z = 0 := le_antisymm (le_of_not_gt h) hz.1
      subst z
      norm_num at he
    · by_contra h
      have : z = 1 := le_antisymm hz.2 (le_of_not_gt h)
      subst z
      norm_num at he
  refine ⟨z, ⟨hzi, he⟩, ?_⟩
  intro y hy
  exact strictMonoOn_shapePolynomial.injOn ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ hz (hy.2.trans he.symm)

/-- Exact differentiated rational expression from `lem:unimodal`. -/
theorem hasDerivAt_shapeTheta {z : ℝ} (hz : 0 < z) :
    HasDerivAt shapeTheta (shapePolynomial z / (2*z^2*(z^2+3)^2)) z := by
  have hi := hasDerivAt_id z
  have hminus : HasDerivAt (fun x : ℝ => 1-x) (-1) z := by simpa using hi.const_sub 1
  have hplus : HasDerivAt (fun x : ℝ => 1+x) 1 z := by simpa using hi.const_add 1
  have hsq1 := (hi.pow 2).add_const 1
  have hsq3 := (hi.pow 2).add_const 3
  have hn : 1+z ≠ 0 := by linarith
  have hn2 : z^2+3 ≠ 0 := by positivity
  have hz0 := ne_of_gt hz
  have hd0 : 2*z*(z^2+3)*(1+z) ≠ 0 := by positivity
  have ht := ((Real.hasDerivAt_log hz0).add (hminus.div hplus hn)).add
    ((hsq1.mul (hminus.pow 3)).div (((hi.const_mul 2).mul hsq3).mul hplus) hd0)
  convert ht using 1
  simp only [Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold shapePolynomial
  field_simp
  ring

@[simp] theorem shapeTheta_one : shapeTheta 1 = 0 := by norm_num [shapeTheta]

/-- The removable product zθ(z), useful at the zero endpoint. -/
def weightedTheta (z : ℝ) : ℝ := z * Real.log z + z*(1-z)/(1+z) +
  (z^2+1)*(1-z)^3/(2*(z^2+3)*(1+z))

@[simp] theorem weightedTheta_zero : weightedTheta 0 = 1/6 := by norm_num [weightedTheta]

theorem weightedTheta_eq {z : ℝ} (hz : 0 < z) : weightedTheta z = z * shapeTheta z := by
  have hn : 1+z ≠ 0 := by linarith
  have hn2 : z^2+3 ≠ 0 := by positivity
  have hz0 := ne_of_gt hz
  unfold weightedTheta shapeTheta
  field_simp

theorem continuousAt_weightedTheta_zero : ContinuousAt weightedTheta 0 := by
  have h1 : ContinuousAt (fun z : ℝ => z * Real.log z) 0 := Real.continuous_mul_log.continuousAt
  unfold weightedTheta
  apply ContinuousAt.add
  · exact h1.add ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.add continuousAt_id) (by norm_num))
  · apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num

/-- The endpoint calculation zθ(z) → 1/6 appearing in `lem:unimodal`. -/
theorem tendsto_mul_shapeTheta_zero :
    Tendsto (fun z : ℝ => z * shapeTheta z) (𝓝[>] 0) (𝓝 (1/6)) := by
  have h : Tendsto weightedTheta (𝓝[>] (0 : ℝ)) (𝓝 (weightedTheta 0)) :=
    continuousAt_weightedTheta_zero.tendsto.mono_left nhdsWithin_le_nhds
  rw [weightedTheta_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact weightedTheta_eq hz

/-- There is a positive θ value arbitrarily close to zero. -/
theorem exists_shapeTheta_pos_below {c : ℝ} (hc : 0 < c) :
    ∃ z ∈ Ioo (0 : ℝ) c, 0 < shapeTheta z := by
  have hp := tendsto_mul_shapeTheta_zero.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1/6))
  have hc' : ∀ᶠ z : ℝ in 𝓝[>] 0, z < c :=
    (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  have hzp : ∀ᶠ z : ℝ in 𝓝[>] 0, z ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  obtain ⟨z, hzpos, hzp, hzc⟩ := (hzp.and (hp.and hc')).exists
  refine ⟨z, ⟨hzpos, hzc⟩, ?_⟩
  exact (mul_pos_iff_of_pos_left hzpos).mp hzp

/-- θ has one minimum: it decreases up to the unique root of p, then increases. -/
theorem shapeTheta_monotonicity {z₀ : ℝ} (hz₀ : z₀ ∈ Ioo (0 : ℝ) 1)
    (hroot : shapePolynomial z₀ = 0) :
    StrictAntiOn shapeTheta (Ioc (0 : ℝ) z₀) ∧
    StrictMonoOn shapeTheta (Icc z₀ 1) := by
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ioc 0 z₀)
    · intro z hz
      exact (hasDerivAt_shapeTheta hz.1).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ioc] at hz
      have hp : shapePolynomial z < 0 := by
        rw [← hroot]
        exact strictMonoOn_shapePolynomial ⟨le_of_lt hz.1, le_of_lt (hz.2.trans hz₀.2)⟩
          ⟨le_of_lt hz₀.1, le_of_lt hz₀.2⟩ hz.2
      rw [(hasDerivAt_shapeTheta hz.1).deriv]
      have hzp := hz.1
      exact div_neg_of_neg_of_pos hp (by positivity)
  · apply strictMonoOn_of_deriv_pos (convex_Icc z₀ 1)
    · intro z hz
      exact (hasDerivAt_shapeTheta (lt_of_lt_of_le hz₀.1 hz.1)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hzp : 0 < z := hz₀.1.trans hz.1
      have hp : 0 < shapePolynomial z := by
        rw [← hroot]
        exact strictMonoOn_shapePolynomial ⟨le_of_lt hz₀.1, le_of_lt hz₀.2⟩
          ⟨le_of_lt hzp, le_of_lt hz.2⟩ hz.1
      rw [(hasDerivAt_shapeTheta hzp).deriv]
      exact div_pos hp (by positivity)

/-- θ has exactly the single sign transition required for the spinodal. -/
theorem exists_shapeTheta_crossing :
    ∃ zsp ∈ Ioo (0 : ℝ) 1, shapeTheta zsp = 0 ∧
      (∀ z ∈ Ioo (0 : ℝ) zsp, 0 < shapeTheta z) ∧
      (∀ z ∈ Ioo zsp 1, shapeTheta z < 0) := by
  obtain ⟨z₀, ⟨hz₀, hroot⟩, _⟩ := existsUnique_shapePolynomial_zero
  obtain ⟨hleft, hright⟩ := shapeTheta_monotonicity hz₀ hroot
  have hneg : shapeTheta z₀ < 0 := by
    simpa using hright ⟨le_rfl, le_of_lt hz₀.2⟩ ⟨le_of_lt hz₀.2, le_rfl⟩ hz₀.2
  obtain ⟨a, ha, hap⟩ := exists_shapeTheta_pos_below hz₀.1
  have hc : ContinuousOn shapeTheta (Icc a z₀) := by
    intro z hz
    exact (hasDerivAt_shapeTheta (lt_of_lt_of_le ha.1 hz.1)).continuousAt.continuousWithinAt
  obtain ⟨zsp, hsp, he⟩ := intermediate_value_Icc' (le_of_lt ha.2) hc
    (show (0 : ℝ) ∈ Icc (shapeTheta z₀) (shapeTheta a) from ⟨le_of_lt hneg, le_of_lt hap⟩)
  have hspa : a < zsp := by
    by_contra hn
    have : zsp = a := le_antisymm (le_of_not_gt hn) hsp.1
    subst zsp
    linarith
  have hsp0 : zsp < z₀ := by
    by_contra hn
    have : zsp = z₀ := le_antisymm hsp.2 (le_of_not_gt hn)
    subst zsp
    linarith
  have hspp : 0 < zsp := ha.1.trans hspa
  refine ⟨zsp, ⟨hspp, hsp0.trans hz₀.2⟩, he, ?_, ?_⟩
  · intro z hz
    have h := hleft ⟨hz.1, le_of_lt (hz.2.trans hsp0)⟩ ⟨hspp, le_of_lt hsp0⟩ hz.2
    rwa [he] at h
  · intro z hz
    by_cases hzz : z ≤ z₀
    · have h := hleft ⟨hspp, le_of_lt hsp0⟩ ⟨hspp.trans hz.1, hzz⟩ hz.1
      rwa [he] at h
    · have h := hright ⟨le_of_lt (lt_of_not_ge hzz), le_of_lt hz.2⟩
        ⟨le_of_lt hz₀.2, le_rfl⟩ hz.2
      simpa using h

/-- A logarithmic form of b(z), used to differentiate without inverse logs. -/
theorem branchB_eq_exp_log (z : ℝ) :
    branchB z = Real.exp (2*z*Real.log z/(1-z)^2) := by
  simp only [branchB, branchLog_eq_neg_log]
  congr 1
  ring

theorem contDiffAt_branchB {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ContDiffAt ℝ 1 branchB z := by
  have he : branchB = fun x : ℝ => Real.exp (2*x*Real.log x/(1-x)^2) := funext branchB_eq_exp_log
  rw [he]
  apply ContDiffAt.exp
  apply ContDiffAt.div
  · exact (contDiffAt_const.mul contDiffAt_id).mul (Real.contDiffAt_log.mpr (ne_of_gt hz))
  · fun_prop
  · exact pow_ne_zero _ (ne_of_gt (sub_pos.mpr hz1))

theorem contDiffAt_branchRho {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ContDiffAt ℝ 1 branchRho z :=
  (contDiffAt_kappa hz).mul (contDiffAt_branchB hz hz1)

theorem contDiffOn_branchRho : ContDiffOn ℝ 1 branchRho (Ioo (0 : ℝ) 1) := by
  intro z hz
  exact (contDiffAt_branchRho hz.1 hz.2).contDiffWithinAt

theorem hasDerivAt_branchB {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasDerivAt branchB
      (branchB z * (2*(1+z)*Real.log z+2*(1-z))/(1-z)^3) z := by
  have hz0 := ne_of_gt hz
  have hn := ne_of_gt (sub_pos.mpr hz1)
  have hi := hasDerivAt_id z
  have hd := ((((hi.const_mul 2).mul (Real.hasDerivAt_log hz0)).div
    ((hi.const_sub 1).pow 2) (pow_ne_zero _ hn))).exp
  have he : branchB = fun x : ℝ => Real.exp (2*x*Real.log x/(1-x)^2) := funext branchB_eq_exp_log
  rw [he]
  convert hd using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

/-- The derivative of ρ has the sign of θ, as in `lem:unimodal`. -/
theorem hasDerivAt_branchRho {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasDerivAt branchRho
      (branchRho z * (2*(1+z)/(1-z)^3) * shapeTheta z) z := by
  have hk := hasDerivAt_kappa hz
  have hb := hasDerivAt_branchB hz hz1
  have hz0 := ne_of_gt hz
  have hn := ne_of_gt (sub_pos.mpr hz1)
  have hk0 := ne_of_gt (kappa_pos hz)
  have hn2 : z^2+3 ≠ 0 := by positivity
  have hn3 : 1+z ≠ 0 := by linarith
  have hc := kappa_cube (le_of_lt hz)
  have hkder : (z^2+1)/(4*kappa z^2) = kappa z*(z^2+1)/(z*(z^2+3)) := by
    field_simp
    nlinarith [congrArg (fun t : ℝ => 4*(z^2+1)*t) hc]
  convert hk.mul hb using 1
  rw [hkder]
  unfold branchRho shapeTheta
  field_simp
  ring

/-- A unique stationary point, with the derivative signs in `lem:unimodal`. -/
theorem exists_branchRho_unimodal :
    ∃ zsp ∈ Ioo (0 : ℝ) 1, deriv branchRho zsp = 0 ∧
      (∀ z ∈ Ioo (0 : ℝ) zsp, 0 < deriv branchRho z) ∧
      (∀ z ∈ Ioo zsp 1, deriv branchRho z < 0) := by
  obtain ⟨zsp, hzsp, he, hleft, hright⟩ := exists_shapeTheta_crossing
  refine ⟨zsp, hzsp, ?_, ?_, ?_⟩
  · rw [(hasDerivAt_branchRho hzsp.1 hzsp.2).deriv, he, mul_zero]
  · intro z hz
    have hz1 := hz.2.trans hzsp.2
    rw [(hasDerivAt_branchRho hz.1 hz1).deriv]
    have hr := (branchRho_mem_Ioo hz.1 hz1).1
    have hn : 0 < 1-z := sub_pos.mpr hz1
    have hzpos := hz.1
    exact mul_pos (mul_pos hr (by positivity)) (hleft z hz)
  · intro z hz
    have hzp := hzsp.1.trans hz.1
    rw [(hasDerivAt_branchRho hzp hz.2).deriv]
    have hr := (branchRho_mem_Ioo hzp hz.2).1
    have hn : 0 < 1-z := sub_pos.mpr hz.2
    exact mul_neg_of_pos_of_neg (mul_pos hr (by positivity)) (hright z hz)

/-- κ is continuous at zero as an actual real power. -/
theorem continuousAt_kappa_zero : ContinuousAt kappa 0 := by
  unfold kappa
  apply ContinuousAt.rpow_const
  · fun_prop
  · exact Or.inr (by norm_num)

@[simp] theorem kappa_zero : kappa 0 = 0 := by norm_num [kappa]

/-- The removable x log x singularity gives the left-endpoint limit of b. -/
theorem continuousAt_branchB_zero : ContinuousAt branchB 0 := by
  change ContinuousAt (fun z => branchB z) 0
  simp_rw [branchB_eq_exp_log, mul_assoc]
  apply Real.continuous_exp.continuousAt.comp
  apply ContinuousAt.div
  · exact continuousAt_const.mul Real.continuous_mul_log.continuousAt
  · fun_prop
  · norm_num

/-- The zero-endpoint limit in `lem:unimodal`. -/
theorem tendsto_branchRho_zero : Tendsto branchRho (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : ContinuousAt branchRho 0 := continuousAt_kappa_zero.mul continuousAt_branchB_zero
  have hz : branchRho 0 = 0 := by simp [branchRho]
  simpa only [hz] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- The logarithmic upper bound used at the endpoint one. -/
theorem branchExponent_le {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    2*z*Real.log z/(1-z)^2 ≤ -(2*z/(1-z)) := by
  have hn := ne_of_gt (sub_pos.mpr hz1)
  calc
    2*z*Real.log z/(1-z)^2 ≤ 2*z*(z-1)/(1-z)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hz) (by positivity)
    _ = -(2*z/(1-z)) := by field_simp; ring

/-- The exponent of b tends to -∞ as z approaches one from below. -/
theorem tendsto_branchExponent_one :
    Tendsto (fun z : ℝ => 2*z*Real.log z/(1-z)^2) (𝓝[<] 1) atBot := by
  have hi : Tendsto (fun z : ℝ => z) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hden : Tendsto (fun z : ℝ => 1-z) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hi.const_sub (1 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z < 1 at hz
      change 0 < 1-z
      exact sub_pos.mpr hz
  have hnum : Tendsto (fun z : ℝ => 2*z) (𝓝[<] 1) (𝓝 2) := by
    simpa using hi.const_mul 2
  have hquot : Tendsto (fun z : ℝ => 2*z/(1-z)) (𝓝[<] 1) atTop := by
    simpa only [div_eq_mul_inv] using hnum.pos_mul_atTop (by norm_num) hden.inv_tendsto_nhdsGT_zero
  have hbound : (fun z : ℝ => 2*z*Real.log z/(1-z)^2) ≤ᶠ[𝓝[<] 1]
      (fun z : ℝ => -(2*z/(1-z))) := by
    have hpos : ∀ᶠ z : ℝ in 𝓝[<] 1, 0 < z :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, self_mem_nhdsWithin] with z hz hz1
    exact branchExponent_le hz hz1
  exact tendsto_atBot_mono' _ hbound (tendsto_neg_atTop_atBot.comp hquot)

/-- The within-one endpoint limit of b. -/
theorem tendsto_branchB_one : Tendsto branchB (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp tendsto_branchExponent_one
  exact h.congr (fun z => (branchB_eq_exp_log z).symm)

/-- The one-endpoint limit in `lem:unimodal`. -/
theorem tendsto_branchRho_one : Tendsto branchRho (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hk : Tendsto kappa (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa only [kappa_one] using (contDiffAt_kappa (by norm_num : (0 : ℝ) < 1)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  simpa only [mul_zero] using hk.mul tendsto_branchB_one

/-- Complete `lem:unimodal`: C¹ regularity, the two zero endpoint limits,
and a single stationary point separating strictly positive/negative derivatives. -/
theorem branchRho_unimodal :
    ContDiffOn ℝ 1 branchRho (Ioo (0 : ℝ) 1) ∧
    Tendsto branchRho (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto branchRho (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
    ∃ zsp ∈ Ioo (0 : ℝ) 1, deriv branchRho zsp = 0 ∧
      (∀ z ∈ Ioo (0 : ℝ) zsp, 0 < deriv branchRho z) ∧
      (∀ z ∈ Ioo zsp 1, deriv branchRho z < 0) :=
  ⟨contDiffOn_branchRho, tendsto_branchRho_zero, tendsto_branchRho_one,
    exists_branchRho_unimodal⟩

end SparseLowerTail.Section04

import SparseLowerTail.Section07.SameBlockCap
import SparseLowerTail.Section07.SmallRowRigidity
import SparseLowerTail.Section06.RowsBipodal

/-! The structural conclusion in the small-target range. The two spectral sign
classes have identical rows internally, hence the actual minimizer is bipodal.
No bipodal ansatz is assumed. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04 Section06

/-- Small-target minimizers are actual bipodal graphons, with their partition
provided by the leading centered-kernel eigenfunction. -/
theorem smallTarget_isBipodal (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    ∃ c a d b : ℝ, IsBipodal U c a d b := by
  let P := positiveSignBlock (S.eigenfunction 0)
  have hP : MeasurableSet P := positiveSignBlock_measurable (S.eigenfunction_measurable 0)
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  let μ := graphonMultiplier U r
  have hμ : 18≤μ := by
    have hh := (smallTargetErrorData external hr hU S).mu_lower
    change 186/10≤μ at hh
    linarith
  have ha : Real.exp (-((27/100)*μ))∈Icc (0:ℝ) 1 :=
    ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by nlinarith)⟩
  have hcap := smallTarget_sameBlock_cap external hSampling hr hU S
  have hdom : ∀ᵐ p ∂squareMeasure,U p≤twoBlock P hP (Real.exp (-((27/100)*μ))) 1 ha (by norm_num) p := by
    filter_upwards [hcap,U.bounded] with p hc hb
    change U p≤blockValue P (Real.exp (-((27/100)*μ))) 1 p
    dsimp [blockValue]
    split_ifs with hx hy hy
    · exact hc (by simp [P,hx,hy])
    · exact hb.2
    · exact hb.2
    · exact hc (by simp [P,hx,hy])
  have hdomc : ∀ᵐ p ∂squareMeasure,U p≤twoBlock Pᶜ hP.compl (Real.exp (-((27/100)*μ))) 1 ha (by norm_num) p := by
    change ∀ᵐ p ∂squareMeasure,U p≤blockValue Pᶜ (Real.exp (-((27/100)*μ))) 1 p
    simpa only [blockValue_compl] using hdom
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have herr := smallTarget_error_bounds external hSampling hr hU S
  have hp : 0<unitMeasure.real P := by linarith [hblocks.2.1,herr.2.2.2.1]
  have hpc : 0<unitMeasure.real Pᶜ := by linarith [hblocks.2.2.2.1,herr.2.2.2.1]
  have hp0 : unitMeasure P≠0 := by
    intro hh
    have hz : unitMeasure.real P=0 := by simp [Measure.real,hh]
    linarith
  have hpc0 : unitMeasure Pᶜ≠0 := by
    intro hh
    have hz : unitMeasure.real Pᶜ=0 := by simp [Measure.real,hh]
    linarith
  refine ⟨unitMeasure.real P,?_⟩
  apply bipodal_of_row_class_eq hP hp0 hpc0
  have hrows := minimizer_row_functional hSampling hr01 hU
  have hlow := Measure.ae_ae_of_ae_prod (minimizer_lower_bound hr01 hU)
  have hcaps := Measure.ae_ae_of_ae_prod hcap
  filter_upwards [hrows,hlow,hcaps] with x hx hlx hcx
  filter_upwards [hrows,hlow,hcaps] with y hy hly hcy
  intro hsame
  have hbx : ∀ᵐ z ∂unitMeasure, Real.exp (-μ)≤U (x,z) ∧ U (x,z)≤1 := by
    filter_upwards [hlx,hx.2.1] with z hl hb
    exact ⟨hl,hb.2⟩
  have hby : ∀ᵐ z ∂unitMeasure, Real.exp (-μ)≤U (y,z) ∧ U (y,z)≤1 := by
    filter_upwards [hly,hy.2.1] with z hl hb
    exact ⟨hl,hb.2⟩
  by_cases hxin : x∈P
  · have hyin := hsame.mp hxin
    have hxc : ∀ᵐ z ∂unitMeasure,z∈P→U (x,z)≤Real.exp (-((27/100)*μ)) := by
      filter_upwards [hcx] with z hz
      intro hzin
      exact hz ⟨fun _ => hzin,fun _ => hxin⟩
    have hyc : ∀ᵐ z ∂unitMeasure,z∈P→U (y,z)≤Real.exp (-((27/100)*μ)) := by
      filter_upwards [hcy] with z hz
      intro hzin
      exact hz ⟨fun _ => hzin,fun _ => hyin⟩
    exact small_stationary_rows_eq hP hμ (Real.exp_pos _) hdom hx.1 hy.1 hbx hby hxc hyc hx.2.2.2 hy.2.2.2
  · have hyin : y∉P := fun hh => hxin (hsame.mpr hh)
    have hxc : ∀ᵐ z ∂unitMeasure,z∈Pᶜ→U (x,z)≤Real.exp (-((27/100)*μ)) := by
      filter_upwards [hcx] with z hz
      intro hzin
      exact hz ⟨fun hh => (hxin hh).elim,fun hh => (hzin hh).elim⟩
    have hyc : ∀ᵐ z ∂unitMeasure,z∈Pᶜ→U (y,z)≤Real.exp (-((27/100)*μ)) := by
      filter_upwards [hcy] with z hz
      intro hzin
      exact hz ⟨fun hh => (hyin hh).elim,fun hh => (hzin hh).elim⟩
    exact small_stationary_rows_eq hP.compl hμ (Real.exp_pos _) hdomc hx.1 hy.1 hbx hby hxc hyc hx.2.2.2 hy.2.2.2

end SparseLowerTail.Section07

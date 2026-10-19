import SparseLowerTail.Section06.BlockBalance
import SparseLowerTail.Section06.RowRigidity

/-! Sequential approximation stage of local rigidity: actual measurable
partitions converge to equal mass and give uniform graphon approximations. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section06
open Section02 Section04

/-- Steps 1--3 of `thm:rigidity` assembled for a cut-convergent sequence. -/
theorem exists_convergent_row_partitions (hSampling : UniformSampling)
    {P : Set ℝ} (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal))
    {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1) (hμ : 0<μ) (hEL : BalancedEL a b μ)
    {r : ℕ → ℝ} {U : ℕ → Graphon} (hr : ∀ n,r n∈Ioo (0:ℝ) 1)
    (hU : ∀ n,IsMinimizer (r n) (U n))
    (hcut : CutConverges U (twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩))
    (hmu : Tendsto (fun n => graphonMultiplier (U n) (r n)) atTop (𝓝 μ)) :
    ∃ (Q : ℕ → Set ℝ) (ζ : ℕ → ℝ),
      (∀ n,MeasurableSet (Q n)) ∧ (∀ n,0≤ζ n) ∧ Tendsto ζ atTop (𝓝 0) ∧
      Tendsto (fun n => unitMeasure.real (Q n)) atTop (𝓝 (1/2)) ∧
      ∀ n,∀ᵐ p ∂squareMeasure,|U n p-blockValue (Q n) a b p|≤ζ n := by
  let B := twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩
  let ν := fun n => graphonMultiplier (U n) (r n)
  let d := fun n => cutNorm (fun p => U n p-B p)
  let β := fun n => ν n*d n+|ν n-μ|
  have hν : ∀ n,0≤ν n := fun n => (minimizer_multiplier_pos (hr n) (hU n)).le
  have hd : ∀ n,0≤d n := fun n => cutNorm_nonneg ((graphon_integrable (U n)).sub (graphon_integrable B))
  have hβ : ∀ n,0≤β n := fun n => add_nonneg (mul_nonneg (hν n) (hd n)) (abs_nonneg _)
  have hdlim : Tendsto d atTop (𝓝 0) := hcut
  have hνlim : Tendsto ν atTop (𝓝 μ) := hmu
  have habslim : Tendsto (fun n => |ν n-μ|) atTop (𝓝 0) := by
    simpa using (hνlim.sub (tendsto_const_nhds (x:=μ))).abs
  have hβlim : Tendsto β atTop (𝓝 0) := by
    simpa [β] using (hνlim.mul hdlim).add habslim
  obtain ⟨c,hc,hrows⟩ := minimizer_rows_near_balanced hSampling hP hm ha hab hb hμ hEL
  let ε := fun n => Real.sqrt (2*β n/c)
  let ζ := fun n => 2*ν n*ε n+|ν n-μ|
  have hε : ∀ n,0≤ε n := fun n => Real.sqrt_nonneg _
  have hεsq : ∀ n,(ε n)^2=2*β n/c := fun n => Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) (hβ n)) hc.le)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x:=(2:ℝ))).mul hβlim).div_const c).sqrt
    simpa [ε] using h
  have hζlim : Tendsto ζ atTop (𝓝 0) := by
    simpa [ζ] using (((tendsto_const_nhds (x:=(2:ℝ))).mul hνlim).mul hεlim).add habslim
  have hex : ∀ n,∃ Q : Set ℝ,MeasurableSet Q ∧
      (∀ᵐ p ∂squareMeasure,|U n p-blockValue Q a b p|≤ζ n) ∧
      2*(b-a)*(unitMeasure.real Q-1/2)^2≤d n+ζ n := by
    intro n
    have hrow : ∀ᵐ x ∂unitMeasure,
        min (profileL2Sq (fun y => U n (x,y)) (blockProfile P a b))
          (profileL2Sq (fun y => U n (x,y)) (blockProfile P b a))≤(ε n)^2 := by
      filter_upwards [hrows (r n) (U n) (hr n) (hU n)] with x hx
      rw [hεsq]
      apply (le_div_iff₀ hc).mpr
      change c*min (profileL2Sq (fun y => U n (x,y)) (blockProfile P a b))
        (profileL2Sq (fun y => U n (x,y)) (blockProfile P b a))≤2*β n at hx
      nlinarith
    obtain ⟨Q,hQ,_,hu,hp⟩ := exists_uniform_row_partition (hr n) (hU n) hP hm ha hab hb hμ hEL (hε n) hrow
    exact ⟨Q,hQ,hu,hp⟩
  choose Q hQ hu hp using hex
  refine ⟨Q,ζ,hQ,fun n => add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hν n)) (hε n)) (abs_nonneg _),hζlim,?_,hu⟩
  have hpos : 0<2*(b-a) := mul_pos (by norm_num) (sub_pos.mpr hab)
  have hsq : Tendsto (fun n => (unitMeasure.real (Q n)-1/2)^2) atTop (𝓝 0) := by
    apply squeeze_zero (g:=fun n => (d n+ζ n)/(2*(b-a))) (fun n => sq_nonneg _)
      (fun n => (le_div_iff₀ hpos).mpr (by nlinarith [hp n]))
    simpa using (hdlim.add hζlim).div_const (2*(b-a))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have habs := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_zero,Real.norm_eq_abs] using habs

end SparseLowerTail.Section06

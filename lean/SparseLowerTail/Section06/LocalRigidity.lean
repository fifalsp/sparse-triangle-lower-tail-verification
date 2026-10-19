import SparseLowerTail.Section06.RigidityApproximation
import SparseLowerTail.Section06.RowsBipodal
import SparseLowerTail.Section05.MinimizerLimits

/-! The complete local rigidity theorem for unrestricted graphon minimizers. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section06
open Section02 Section04 Section05

/-- Local rigidity after choosing representatives converging in cut norm. -/
theorem eventually_bipodal_of_cutConverges (hSampling : UniformSampling)
    {P : Set ℝ} (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal))
    {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1) (hμ : 0<μ) (hEL : BalancedEL a b μ)
    {r : ℕ → ℝ} {U : ℕ → Graphon} (hr : ∀ n,r n∈Ioo (0:ℝ) 1)
    (hU : ∀ n,IsMinimizer (r n) (U n))
    (hcut : CutConverges U (twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩))
    (hmu : Tendsto (fun n => graphonMultiplier (U n) (r n)) atTop (𝓝 μ)) :
    ∀ᶠ n in atTop,∃ c aa dd bb : ℝ,IsBipodal (U n) c aa dd bb := by
  obtain ⟨Q,ζ,hQ,_,hζ,hp,hu⟩ := exists_convergent_row_partitions hSampling hP hm ha hab hb hμ hEL hr hU hcut hmu
  obtain ⟨δ,hδ,hradius⟩ := exists_uniform_bipodal_radius ha hab hb.le hμ hEL
  have hmuabs : Tendsto (fun n => |graphonMultiplier (U n) (r n)-μ|) atTop (𝓝 0) := by
    simpa using (hmu.sub (tendsto_const_nhds (x:=μ))).abs
  have hpabs : Tendsto (fun n => |unitMeasure.real (Q n)-1/2|) atTop (𝓝 0) := by
    simpa using (hp.sub (tendsto_const_nhds (x:=(1/2:ℝ)))).abs
  filter_upwards [hmuabs.eventually (gt_mem_nhds hδ),hpabs.eventually (gt_mem_nhds hδ),
    hζ.eventually (gt_mem_nhds hδ)] with n hmn hpn hzn
  have hELrows := (minimizer_row_functional hSampling (hr n) (hU n)).mono fun x hx => hx.2.2.2
  have hun : ∀ᵐ p ∂squareMeasure,|U n p-blockValue (Q n) a b p|≤δ :=
    (hu n).mono fun p hp => hp.trans hzn.le
  obtain ⟨aa,dd,bb,hh⟩ := hradius (Q n) (hQ n) (graphonMultiplier (U n) (r n)) (U n)
    (minimizer_multiplier_pos (hr n) (hU n)).le hmn hpn hun hELrows
  exact ⟨unitMeasure.real (Q n),aa,dd,bb,hh⟩

/-- Complete `thm:rigidity`, using the actual infimum-over-bijections cut distance.
The only classical input is inverse-transform sampling for the proved insertion
variation. No compactness, certificate, or unproved rigidity hypothesis is assumed. -/
theorem eventually_bipodal_of_cutDistance (hSampling : UniformSampling)
    {P : Set ℝ} (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal))
    {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1) (hμ : 0<μ) (hEL : BalancedEL a b μ)
    {r : ℕ → ℝ} {U : ℕ → Graphon} (hr : ∀ n,r n∈Ioo (0:ℝ) 1)
    (hU : ∀ n,IsMinimizer (r n) (U n))
    (hcut : Tendsto (fun n => cutDistance (U n)
      (twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩)) atTop (𝓝 0))
    (hmu : Tendsto (fun n => graphonMultiplier (U n) (r n)) atTop (𝓝 μ)) :
    ∀ᶠ n in atTop,∃ c aa dd bb : ℝ,IsBipodal (U n) c aa dd bb := by
  obtain ⟨φ,hφ⟩ := exists_relabel_cutConverges hcut
  have hmurelabel : Tendsto (fun n => graphonMultiplier (relabel (U n) (φ n).toRelabeling) (r n)) atTop (𝓝 μ) := by
    simpa only [graphonMultiplier,cost_relabel,edgeDensity_relabel] using hmu
  have h := eventually_bipodal_of_cutConverges hSampling hP hm ha hab hb hμ hEL hr
    (fun n => minimizer_relabel (hU n) (φ n).toRelabeling) hφ hmurelabel
  filter_upwards [h] with n hn
  obtain ⟨c,aa,dd,bb,hh⟩ := hn
  exact ⟨c,aa,dd,bb,(isBipodal_relabel_iff (U n) (φ n) c aa dd bb).mp hh⟩

end SparseLowerTail.Section06

import SparseLowerTail.Section04.Rescaling
import SparseLowerTail.Section04.BalancedPhase

/-!
The boundary lemma `lem:boundary`. Scaling the given minimizer and truncating
produces genuine competitors. Continuity is needed only for the explicit scaling
formula and the proved stationary branch, so no minimizer-existence or value
continuity theorem is required for this argument.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section08
open Section04

/-- Entropy of a scaled kernel, expressed without a positivity-dependent type. -/
def boundaryScaleCost (U : Graphon) (r s : ℝ) : ℝ :=
  (s/r)*cost U + ((s/r)*Real.log (s/r))*edgeDensity U + 1-s/r

@[simp] theorem boundaryScaleCost_self (U : Graphon) {r : ℝ} (hr : r ≠ 0) :
    boundaryScaleCost U r r = cost U := by simp [boundaryScaleCost, hr]

theorem hasDerivAt_boundaryScaleCost (U : Graphon) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (boundaryScaleCost U r) ((cost U+edgeDensity U-1)/r) r := by
  have hlin := (hasDerivAt_id r).div_const r
  have hlog := hlin.log (by simp [ne_of_gt hr])
  have h := (((hlin.mul_const (cost U)).add
    ((hlin.mul hlog).mul_const (edgeDensity U))).add_const 1).sub hlin
  convert h using 1
  simp [ne_of_gt hr]
  ring

/-- Scaling followed by truncation proves the variational lower bound. -/
theorem value_le_boundaryScaleCost {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {U : Graphon} (ht : triangle U = r^3) :
    value s ≤ boundaryScaleCost U r s := by
  let W := (NonnegativeKernel.ofGraphon U).scale (s/r) (div_pos hs hr).le
  have hW : W.triangle = s^3 := by
    rw [NonnegativeKernel.triangle_scale, NonnegativeKernel.triangle_ofGraphon, ht]
    field_simp
  have h := NonnegativeKernel.value_le_cost W hW.le
  rw [NonnegativeKernel.cost_scale _ _ (div_pos hs hr)] at h
  exact h

/-- The stationary branch itself is a feasible genuine graphon at its target. -/
theorem minimizer_cost_le_leftBranchCost {r : ℝ} (hr : r ∈ Ioo (0:ℝ) spinodalValue)
    {U : Graphon} (hU : IsMinimizer r U) : cost U ≤ branchCost (leftBranch r) := by
  have hz := leftBranch_mem_unit hr
  let B := branchGraphon (leftBranch r) hz.1 hz.2
  have hB := branchGraphon_isBalanced hz.1 hz.2
  have ht : triangle B = r^3 := by
    rw [hB.triangle_eq (hB.values_mem_Icc).1 (hB.values_mem_Icc).2,
      branch_triangle_eq_rho_cube hz.1, branchRho_leftBranch ⟨hr.1.le,hr.2.le⟩]
  have hc := hU.2 B ht.le
  rwa [branchGraphon_cost hz.1 hz.2] at hc

/-- Full manuscript `lem:boundary`. The interval value identity is the stated
hypothesis; all scaling, continuity and derivative inputs are proved. -/
theorem boundary {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ < r₁)
    (hr₁ : r₁ ≤ threshold)
    (hvalue : ∀ r ∈ Ioo r₀ r₁, value r = branchCost (leftBranch r))
    {U : Graphon} (hU : IsMinimizer r₀ U) :
    cost U = branchCost (leftBranch r₀) ∧
      (branchA (leftBranch r₀)+branchB (leftBranch r₀))/2 ≤ edgeDensity U := by
  have hrt : r₀ < threshold := hr₀₁.trans_le hr₁
  have hr : r₀ ∈ Ioo (0:ℝ) 1 := ⟨hr₀, hrt.trans threshold_mem_Ioo.2⟩
  have hspin : r₀ ∈ Ioo (0:ℝ) spinodalValue := ⟨hr₀, by
    rw [threshold_eq_transitionTarget] at hrt
    exact hrt.trans transitionTarget_spec.1.2⟩
  have ht := minimizer_triangle_eq hr hU
  let φ : ℝ → ℝ := fun s => boundaryScaleCost U r₀ s-branchCost (leftBranch s)
  have hφder : HasDerivAt φ
      ((cost U+edgeDensity U-1)/r₀+branchMu (leftBranch r₀)*r₀^2) r₀ := by
    convert (hasDerivAt_boundaryScaleCost U hr₀).sub (hasDerivAt_leftBranchCost hspin) using 1
    ring
  have hφnonneg : ∀ s ∈ Ioo r₀ r₁, 0 ≤ φ s := by
    intro s hs
    have hh := value_le_boundaryScaleCost hr₀ (hr₀.trans hs.1) ht
    rw [hvalue s hs] at hh
    exact sub_nonneg.mpr hh
  have hφ₀ : 0 ≤ φ r₀ := by
    apply ge_of_tendsto (show Tendsto φ (𝓝[>] r₀) (𝓝 (φ r₀)) from
      hφder.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr₀₁).filter_mono nhdsWithin_le_nhds] with s hs hs₁
    exact hφnonneg s ⟨hs,hs₁⟩
  have heq : cost U = branchCost (leftBranch r₀) := by
    have hlo : branchCost (leftBranch r₀) ≤ cost U := by
      simpa only [φ, boundaryScaleCost_self U (ne_of_gt hr₀), sub_nonneg] using hφ₀
    exact le_antisymm (minimizer_cost_le_leftBranchCost hspin hU) hlo
  have hφzero : φ r₀ = 0 := by simp [φ, ne_of_gt hr₀, heq]
  have hmin : IsLocalMinOn φ (Ici r₀) r₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr₀₁).filter_mono nhdsWithin_le_nhds] with s hs hs₁
    rw [hφzero]
    rcases eq_or_lt_of_le (show r₀ ≤ s from hs) with h | h
    · simpa [← h] using hφ₀
    · exact hφnonneg s ⟨h,hs₁⟩
  have hcone : (1:ℝ) ∈ posTangentConeAt (Ici r₀) r₀ := by
    apply one_mem_posTangentConeAt_iff_frequently.mpr
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact le_of_lt (show r₀ < s from hs)
  have hd := hmin.hasFDerivWithinAt_nonneg hφder.hasDerivWithinAt.hasFDerivWithinAt hcone
  have hd' : 0 ≤ (cost U+edgeDensity U-1)/r₀+branchMu (leftBranch r₀)*r₀^2 := by
    simpa using hd
  have hz := leftBranch_mem_unit hspin
  have hm := balancedEL_multiplier_cost (branch_balancedEL hz.1 hz.2)
  rw [branch_triangle_eq_rho_cube hz.1,
    branchRho_leftBranch ⟨hr₀.le,hspin.2.le⟩] at hm
  change branchMu (leftBranch r₀)*r₀^3 =
    1-branchCost (leftBranch r₀)-
      (branchA (leftBranch r₀)+branchB (leftBranch r₀))/2 at hm
  refine ⟨heq, ?_⟩
  have hmul := mul_nonneg hd' hr₀.le
  have hdiv : ((cost U+edgeDensity U-1)/r₀)*r₀ = cost U+edgeDensity U-1 :=
    div_mul_cancel₀ _ (ne_of_gt hr₀)
  rw [heq] at hdiv hmul
  nlinarith

end SparseLowerTail.Section08

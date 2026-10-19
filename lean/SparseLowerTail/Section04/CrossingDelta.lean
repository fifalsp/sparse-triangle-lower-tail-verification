import SparseLowerTail.Section04.BalancedDerivative
import SparseLowerTail.Section04.BranchInverse
import SparseLowerTail.Section04.CrossingShape

/-!
# Delta calculus along stationary inverse branches

Stable manuscript anchor: `thm:crossing`(a). This module proves the derivative
and strict increase of the scalar gap on any continuous noncritical inverse
branch. Identification of the manuscript's lower inverse branch is separate.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section04

/-- The stationary gap `g_r(σ(r))`, before choosing a global inverse branch. -/
def inverseDelta (σ : ℝ → ℝ) (r : ℝ) : ℝ := rayGap r (σ r)

/-- The envelope derivative in `thm:crossing`(a). Only stationarity at the point
and differentiability of the parametrization are needed for this cancellation. -/
theorem hasDerivAt_inverseDelta_of_differentiable {σ : ℝ → ℝ} {r σ' : ℝ}
    (hz : σ r ∈ Ioo (0 : ℝ) 1) (hσ : HasDerivAt σ σ' r)
    (hinv : branchRho (σ r) = r) :
    HasDerivAt (inverseDelta σ) (rayExcess (σ r) / r) r := by
  have hr : 0 < r := hinv ▸ (branchRho_mem_Ioo hz.1 hz.2).1
  have ha := (hasDerivAt_rayExcess hz.1).differentiableAt.hasDerivAt.comp r hσ
  have hc := (hasDerivAt_rayCost hz.1 hz.2).comp r hσ
  have hl := Real.hasDerivAt_log (ne_of_gt hr)
  have hd := (ha.mul hl).add hc
  rw [hinv] at hd
  convert hd using 1
  dsimp
  rw [div_eq_mul_inv]
  ring

/-- Local inverse formulation: inverse differentiability follows from the
classical inverse derivative rule, with `ρ' ≠ 0` explicitly required. -/
theorem hasDerivAt_inverseDelta_of_local_inverse {σ : ℝ → ℝ} {r : ℝ}
    (hz : σ r ∈ Ioo (0 : ℝ) 1) (hσ : ContinuousAt σ r)
    (hn : deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ᶠ t in 𝓝 r, branchRho (σ t) = t) :
    HasDerivAt (inverseDelta σ) (rayExcess (σ r) / r) r := by
  have hrho := ((contDiffAt_branchRho hz.1 hz.2).differentiableAt (by norm_num)).hasDerivAt
  exact hasDerivAt_inverseDelta_of_differentiable hz
    (hrho.of_local_left_inverse hσ hn hinv) hinv.self_of_nhds

/-- Pointwise derivative throughout an open inverse-branch domain. -/
theorem hasDerivAt_inverseDelta_on {J : Set ℝ} (hJ : IsOpen J)
    {σ : ℝ → ℝ} (hσ : ContinuousOn σ J) (hz : MapsTo σ J (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ J, deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ r ∈ J, branchRho (σ r) = r) {r : ℝ} (hr : r ∈ J) :
    HasDerivAt (inverseDelta σ) (rayExcess (σ r) / r) r := by
  apply hasDerivAt_inverseDelta_of_local_inverse (hz hr)
    (hσ.continuousAt (hJ.mem_nhds hr)) (hn r hr)
  filter_upwards [hJ.mem_nhds hr] with t ht
  exact hinv t ht

/-- Continuous differentiability in `thm:crossing`(a). -/
theorem contDiffOn_inverseDelta {J : Set ℝ} (hJ : IsOpen J)
    {σ : ℝ → ℝ} (hσ : ContinuousOn σ J) (hz : MapsTo σ J (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ J, deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ r ∈ J, branchRho (σ r) = r) :
    ContDiffOn ℝ 1 (inverseDelta σ) J := by
  have hd := fun r hr => hasDerivAt_inverseDelta_on hJ hσ hz hn hinv (r := r) hr
  have hA : ContinuousOn rayExcess (Ioo (0 : ℝ) 1) := by
    intro z hz
    exact (hasDerivAt_rayExcess hz.1).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun r => rayExcess (σ r) / r) J := by
    apply (hA.comp hσ hz).div continuousOn_id
    intro r hr
    have hp : 0 < r := (hinv r hr) ▸ (branchRho_mem_Ioo (hz hr).1 (hz hr).2).1
    exact ne_of_gt hp
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen hJ]
  refine ⟨fun r hr => (hd r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · rw [contDiffOn_zero]
    apply hc.congr
    intro r hr
    exact (hd r hr).deriv

/-- Positivity of the derivative in `thm:crossing`(a). -/
theorem deriv_inverseDelta_pos {J : Set ℝ} (hJ : IsOpen J)
    {σ : ℝ → ℝ} (hσ : ContinuousOn σ J) (hz : MapsTo σ J (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ J, deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ r ∈ J, branchRho (σ r) = r) {r : ℝ} (hr : r ∈ J) :
    0 < deriv (inverseDelta σ) r := by
  rw [(hasDerivAt_inverseDelta_on hJ hσ hz hn hinv hr).deriv]
  have hp : 0 < r := (hinv r hr) ▸ (branchRho_mem_Ioo (hz hr).1 (hz hr).2).1
  exact div_pos (rayExcess_pos (hz hr).1 (hz hr).2) hp

/-- Strict increase of delta follows on every convex open inverse-branch domain. -/
theorem strictMonoOn_inverseDelta {J : Set ℝ} (hJ : IsOpen J) (hJconv : Convex ℝ J)
    {σ : ℝ → ℝ} (hσ : ContinuousOn σ J) (hz : MapsTo σ J (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ J, deriv branchRho (σ r) ≠ 0)
    (hinv : ∀ r ∈ J, branchRho (σ r) = r) : StrictMonoOn (inverseDelta σ) J := by
  apply strictMonoOn_of_deriv_pos hJconv (contDiffOn_inverseDelta hJ hσ hz hn hinv).continuousOn
  intro r hr
  exact deriv_inverseDelta_pos hJ hσ hz hn hinv (interior_subset hr)

/-- Delta is the cost difference divided by the target, matching the manuscript. -/
theorem inverseDelta_cost_identity {σ : ℝ → ℝ} {r : ℝ}
    (hz : σ r ∈ Ioo (0 : ℝ) 1) (hinv : branchRho (σ r) = r) :
    branchCost (σ r) = entropy r + r * inverseDelta σ r := by
  obtain ⟨ha, hb⟩ := branch_eq_scaled_ray hz.1
  rw [hinv] at ha hb
  unfold branchCost
  rw [ha, hb]
  exact scaled_ray_cost hz.1 (hinv ▸ (branchRho_mem_Ioo hz.1 hz.2).1)

/-- D and delta have opposite signs on an inverse branch. -/
theorem inverseDelta_difference_identity {σ : ℝ → ℝ} {r : ℝ}
    (hz : σ r ∈ Ioo (0 : ℝ) 1) (hinv : branchRho (σ r) = r) :
    branchDifference (σ r) = -r * inverseDelta σ r := by
  rw [branchDifference_eq hz.1 hz.2, hinv]
  rfl

/-- The manuscript's actual delta function, using the proved increasing inverse. -/
def crossingDelta (r : ℝ) : ℝ := inverseDelta leftBranch r

private theorem leftBranch_mapsTo_unit :
    MapsTo leftBranch (Ioo (0 : ℝ) spinodalValue) (Ioo (0 : ℝ) 1) := by
  intro r hr
  have hz := (leftBranch_spec ⟨hr.1, hr.2.le⟩).1
  exact ⟨hz.1, hz.2.trans_lt spinodal_spec.1.2⟩

private theorem continuousOn_leftBranch_open :
    ContinuousOn leftBranch (Ioo (0 : ℝ) spinodalValue) :=
  continuousOn_leftBranch.mono Ioo_subset_Ioc_self

/-- The derivative identity for the actual delta, with no inverse-branch hypotheses. -/
theorem hasDerivAt_crossingDelta {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    HasDerivAt crossingDelta (rayExcess (leftBranch r) / r) r := by
  exact hasDerivAt_inverseDelta_on isOpen_Ioo continuousOn_leftBranch_open
    leftBranch_mapsTo_unit (fun _ hr => ne_of_gt (deriv_branchRho_leftBranch_pos hr))
    (fun _ hr => branchRho_leftBranch ⟨hr.1.le, hr.2.le⟩) hr

/-- The continuous differentiability assertion in `thm:crossing`(a), instantiated. -/
theorem contDiffOn_crossingDelta :
    ContDiffOn ℝ 1 crossingDelta (Ioo (0 : ℝ) spinodalValue) :=
  contDiffOn_inverseDelta isOpen_Ioo continuousOn_leftBranch_open leftBranch_mapsTo_unit
    (fun _ hr => ne_of_gt (deriv_branchRho_leftBranch_pos hr))
    (fun _ hr => branchRho_leftBranch ⟨hr.1.le, hr.2.le⟩)

/-- Strict increase in `thm:crossing`(a), instantiated on the true lower branch. -/
theorem strictMonoOn_crossingDelta :
    StrictMonoOn crossingDelta (Ioo (0 : ℝ) spinodalValue) :=
  strictMonoOn_inverseDelta isOpen_Ioo (convex_Ioo _ _) continuousOn_leftBranch_open
    leftBranch_mapsTo_unit (fun _ hr => ne_of_gt (deriv_branchRho_leftBranch_pos hr))
    (fun _ hr => branchRho_leftBranch ⟨hr.1.le, hr.2.le⟩)

/-- The derivative half of `lem:Bderivative`(b) for the actual left branch. -/
theorem hasDerivAt_leftBranchCost {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    HasDerivAt (fun t => branchCost (leftBranch t)) (-branchMu (leftBranch r) * r ^ 2) r :=
  hasDerivAt_branchCost_on_inverse isOpen_Ioo continuousOn_leftBranch_open
    leftBranch_mapsTo_unit (fun _ hr => ne_of_gt (deriv_branchRho_leftBranch_pos hr))
    (fun _ hr => branchRho_leftBranch ⟨hr.1.le, hr.2.le⟩) hr

/-- The C¹ half of `lem:Bderivative`(b) for the actual left branch. -/
theorem contDiffOn_leftBranchCost :
    ContDiffOn ℝ 1 (fun t => branchCost (leftBranch t)) (Ioo (0 : ℝ) spinodalValue) :=
  contDiffOn_branchCost_inverse isOpen_Ioo continuousOn_leftBranch_open
    leftBranch_mapsTo_unit (fun _ hr => ne_of_gt (deriv_branchRho_leftBranch_pos hr))
    (fun _ hr => branchRho_leftBranch ⟨hr.1.le, hr.2.le⟩)

/-- Continuity of the branch cost at the zero parameter, including both entropy endpoints. -/
theorem continuousAt_branchCost_zero : ContinuousAt branchCost 0 := by
  have ha : ContinuousAt branchA 0 := continuousAt_id.mul continuousAt_branchB_zero
  have hb := continuousAt_branchB_zero
  exact ((continuous_entropy.continuousAt.comp ha).add
    (continuous_entropy.continuousAt.comp hb)).div_const 2

@[simp] theorem branchCost_zero : branchCost 0 = 1 / 2 := by
  norm_num [branchCost, branchA, branchB, balancedCost]

/-- The actual lower inverse tends to zero with the target. -/
theorem tendsto_leftBranch_zero : Tendsto leftBranch (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc := (continuousOn_leftBranch_Icc 0
    ⟨le_rfl, spinodalValue_mem_Ioo.1.le⟩).tendsto
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ))
      (𝓝[Icc 0 spinodalValue] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    have hu : ∀ᶠ r : ℝ in 𝓝[>] 0, r < spinodalValue :=
      (eventually_lt_nhds spinodalValue_mem_Ioo.1).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hu] with r hr hru
    exact ⟨le_of_lt hr, hru.le⟩
  simpa only [leftBranch_zero, Function.comp_apply] using hc.comp hid

/-- The lower-endpoint limit in `thm:crossing`(a). This follows directly from
`F(B_z) → 1/2` and `h(r) → 1`, avoiding a comparison with a fixed auxiliary ray. -/
theorem tendsto_crossingDelta_zero : Tendsto crossingDelta (𝓝[>] (0 : ℝ)) atBot := by
  have hcost : Tendsto (fun r => branchCost (leftBranch r)) (𝓝[>] (0 : ℝ)) (𝓝 (1/2)) := by
    simpa only [branchCost_zero] using continuousAt_branchCost_zero.tendsto.comp tendsto_leftBranch_zero
  have he : Tendsto entropy (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using continuous_entropy.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi (0 : ℝ)))
  have hn : Tendsto (fun r => branchCost (leftBranch r) - entropy r)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(1/2))) := by
    convert hcost.sub he using 1
    norm_num
  have hi : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_id.inv_tendsto_nhdsGT_zero
  have hp := hn.neg_mul_atTop (by norm_num : -(1/2 : ℝ) < 0) hi
  apply hp.congr'
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0, r < spinodalValue :=
    (eventually_lt_nhds spinodalValue_mem_Ioo.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hu] with r hr hru
  change 0 < r at hr
  have hz := leftBranch_mapsTo_unit ⟨hr, hru⟩
  have hid := inverseDelta_cost_identity hz (branchRho_leftBranch ⟨le_of_lt hr, hru.le⟩)
  change (branchCost (leftBranch r) - entropy r) * r⁻¹ = inverseDelta leftBranch r
  rw [hid]
  field_simp [ne_of_gt hr]
  ring

/-- Delta remains continuous at the spinodal endpoint, where the inverse derivative
need not exist. Only continuity of the actual inverse is used here. -/
theorem continuousOn_crossingDelta :
    ContinuousOn crossingDelta (Ioc (0 : ℝ) spinodalValue) := by
  have hz : MapsTo leftBranch (Ioc (0 : ℝ) spinodalValue) (Ioo (0 : ℝ) 1) := by
    intro r hr
    have h := (leftBranch_spec hr).1
    exact ⟨h.1, h.2.trans_lt spinodal_spec.1.2⟩
  have hc : ContinuousOn branchCost (Ioo (0 : ℝ) 1) := by
    intro z hz
    exact (contDiffAt_branchCost hz.1 hz.2).continuousAt.continuousWithinAt
  have hq := ((hc.comp continuousOn_leftBranch hz).sub continuous_entropy.continuousOn).div
    continuousOn_id (fun r hr => ne_of_gt hr.1)
  apply hq.congr
  intro r hr
  have hid := inverseDelta_cost_identity (hz hr) (leftBranch_spec hr).2
  change inverseDelta leftBranch r = (branchCost (leftBranch r) - entropy r) / r
  apply (eq_div_iff (ne_of_gt hr.1)).mpr
  nlinarith [hid]

/-- Delta is strictly increasing up to and including the spinodal endpoint. -/
theorem strictMonoOn_crossingDelta_Ioc :
    StrictMonoOn crossingDelta (Ioc (0 : ℝ) spinodalValue) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 spinodalValue) continuousOn_crossingDelta
  intro r hr
  rw [interior_Ioc] at hr
  rw [(hasDerivAt_crossingDelta hr).deriv]
  exact div_pos (rayExcess_pos (leftBranch_mapsTo_unit hr).1 (leftBranch_mapsTo_unit hr).2) hr.1

/-- Delta is positive at the spinodal: there the ray gap strictly decreases to zero at z=1. -/
theorem crossingDelta_spinodal_pos : 0 < crossingDelta spinodalValue := by
  have hshape := rayGap_strictAnti_of_single_exception spinodalValue_mem_Ioo.1
    spinodal_spec.1 (fun z hz hne => branchRho_lt_spinodalValue hz hne)
  have h := hshape ⟨spinodal_spec.1.1, spinodal_spec.1.2.le⟩
    ⟨by norm_num, le_rfl⟩ spinodal_spec.1.2
  simpa [crossingDelta, inverseDelta] using h

/-- Existence and uniqueness of the transition in `thm:crossing`(a). -/
theorem existsUnique_crossingDelta_zero :
    ∃! r : ℝ, r ∈ Ioo (0 : ℝ) spinodalValue ∧ crossingDelta r = 0 := by
  have hneg : ∀ᶠ r : ℝ in 𝓝[>] 0, crossingDelta r < 0 :=
    tendsto_crossingDelta_zero.eventually (eventually_lt_atBot 0)
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0, r < spinodalValue :=
    (eventually_lt_nhds spinodalValue_mem_Ioo.1).filter_mono nhdsWithin_le_nhds
  have hex : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r < spinodalValue ∧ crossingDelta r < 0 := by
    filter_upwards [self_mem_nhdsWithin, hu, hneg] with r hr hru hrn
    exact ⟨hr, hru, hrn⟩
  obtain ⟨r₀, hr₀, hr₀u, hr₀n⟩ := hex.exists
  have hc : ContinuousOn crossingDelta (Icc r₀ spinodalValue) :=
    continuousOn_crossingDelta.mono (fun r hr => ⟨hr₀.trans_le hr.1, hr.2⟩)
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hr₀u.le hc
    (show (0 : ℝ) ∈ Icc (crossingDelta r₀) (crossingDelta spinodalValue) from
      ⟨hr₀n.le, crossingDelta_spinodal_pos.le⟩)
  have hri : r ∈ Ioo (0 : ℝ) spinodalValue := by
    refine ⟨hr₀.trans_le hr.1, lt_of_le_of_ne hr.2 ?_⟩
    intro h
    subst r
    linarith [crossingDelta_spinodal_pos]
  refine ⟨r, ⟨hri, he⟩, ?_⟩
  intro s hs
  exact strictMonoOn_crossingDelta.injOn hs.1 hri (hs.2.trans he.symm)

/-- The unique transition target; its definition uses the theorem above, not decimal data. -/
def transitionTarget : ℝ := Classical.choose existsUnique_crossingDelta_zero.exists

theorem transitionTarget_spec : transitionTarget ∈ Ioo (0 : ℝ) spinodalValue ∧
    crossingDelta transitionTarget = 0 :=
  Classical.choose_spec existsUnique_crossingDelta_zero.exists

theorem crossingDelta_neg_iff {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    crossingDelta r < 0 ↔ r < transitionTarget := by
  have ht : transitionTarget ∈ Ioc (0 : ℝ) spinodalValue :=
    ⟨transitionTarget_spec.1.1, transitionTarget_spec.1.2.le⟩
  simpa only [transitionTarget_spec.2] using strictMonoOn_crossingDelta_Ioc.lt_iff_lt hr ht

theorem crossingDelta_zero_iff {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    crossingDelta r = 0 ↔ r = transitionTarget := by
  constructor
  · intro he
    apply strictMonoOn_crossingDelta_Ioc.injOn hr
      ⟨transitionTarget_spec.1.1, transitionTarget_spec.1.2.le⟩
    rw [he, transitionTarget_spec.2]
  · rintro rfl
    exact transitionTarget_spec.2

theorem crossingDelta_pos_iff {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    0 < crossingDelta r ↔ transitionTarget < r := by
  have ht : transitionTarget ∈ Ioc (0 : ℝ) spinodalValue :=
    ⟨transitionTarget_spec.1.1, transitionTarget_spec.1.2.le⟩
  simpa only [transitionTarget_spec.2] using strictMonoOn_crossingDelta_Ioc.lt_iff_lt ht hr

end SparseLowerTail.Section04

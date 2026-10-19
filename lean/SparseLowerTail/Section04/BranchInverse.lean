import SparseLowerTail.Section04.Unimodal
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! The actual inverse branches following manuscript `lem:unimodal`.
The spinodal is chosen from the theorem already proved, rather than supplied
as an external hypothesis. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section04

/-- The unique spinodal parameter guaranteed by `lem:unimodal`. -/
def spinodal : ℝ := Classical.choose exists_branchRho_unimodal

theorem spinodal_spec : spinodal ∈ Ioo (0 : ℝ) 1 ∧ deriv branchRho spinodal = 0 ∧
    (∀ z ∈ Ioo (0 : ℝ) spinodal, 0 < deriv branchRho z) ∧
    (∀ z ∈ Ioo spinodal 1, deriv branchRho z < 0) :=
  Classical.choose_spec exists_branchRho_unimodal

def spinodalValue : ℝ := branchRho spinodal

theorem spinodalValue_mem_Ioo : spinodalValue ∈ Ioo (0 : ℝ) 1 :=
  branchRho_mem_Ioo spinodal_spec.1.1 spinodal_spec.1.2

@[simp] theorem branchRho_zero : branchRho 0 = 0 := by simp [branchRho]

theorem continuousOn_branchRho_left : ContinuousOn branchRho (Icc 0 spinodal) := by
  intro z hz
  rcases eq_or_lt_of_le hz.1 with he | hp
  · subst z
    exact (continuousAt_kappa_zero.mul continuousAt_branchB_zero).continuousWithinAt
  · exact (contDiffAt_branchRho hp (lt_of_le_of_lt hz.2 spinodal_spec.1.2)).continuousAt.continuousWithinAt

theorem strictMonoOn_branchRho_left : StrictMonoOn branchRho (Icc 0 spinodal) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 spinodal) continuousOn_branchRho_left
  intro z hz
  rw [interior_Icc] at hz
  exact spinodal_spec.2.2.1 z hz

theorem branchRho_left_mapsTo : MapsTo branchRho (Icc 0 spinodal) (Icc 0 spinodalValue) := by
  intro z hz
  constructor
  · simpa using strictMonoOn_branchRho_left.monotoneOn ⟨le_rfl, le_of_lt spinodal_spec.1.1⟩ hz hz.1
  · exact strictMonoOn_branchRho_left.monotoneOn hz ⟨le_of_lt spinodal_spec.1.1, le_rfl⟩ hz.2

theorem branchRho_left_surjOn : SurjOn branchRho (Icc 0 spinodal) (Icc 0 spinodalValue) := by
  intro r hr
  apply intermediate_value_Icc (le_of_lt spinodal_spec.1.1) continuousOn_branchRho_left
  simpa only [branchRho_zero] using hr

/-- The increasing half of the branch as a genuine order isomorphism. -/
def leftBranchIso : Icc (0 : ℝ) spinodal ≃o Icc (0 : ℝ) spinodalValue where
  toEquiv := Equiv.ofBijective (fun z => ⟨branchRho z, branchRho_left_mapsTo z.property⟩)
    ⟨fun x y h => Subtype.ext (strictMonoOn_branchRho_left.injOn x.property y.property (congrArg Subtype.val h)),
      fun r => by
        obtain ⟨z, hz, he⟩ := branchRho_left_surjOn r.property
        exact ⟨⟨z, hz⟩, Subtype.ext he⟩⟩
  map_rel_iff' := strictMonoOn_branchRho_left.le_iff_le (Subtype.property _) (Subtype.property _)

/-- The increasing inverse branch z₁(r), extended by zero outside its natural domain. -/
def leftBranch (r : ℝ) : ℝ :=
  if hr : r ∈ Icc (0 : ℝ) spinodalValue then (leftBranchIso.symm ⟨r, hr⟩ : ℝ) else 0

theorem leftBranch_eq {r : ℝ} (hr : r ∈ Icc (0 : ℝ) spinodalValue) :
    leftBranch r = (leftBranchIso.symm ⟨r, hr⟩ : ℝ) := dif_pos hr

theorem leftBranch_mem_Icc {r : ℝ} (hr : r ∈ Icc (0 : ℝ) spinodalValue) :
    leftBranch r ∈ Icc (0 : ℝ) spinodal := by
  rw [leftBranch_eq hr]
  exact (leftBranchIso.symm ⟨r, hr⟩).property

theorem branchRho_leftBranch {r : ℝ} (hr : r ∈ Icc (0 : ℝ) spinodalValue) :
    branchRho (leftBranch r) = r := by
  rw [leftBranch_eq hr]
  exact congrArg Subtype.val (leftBranchIso.apply_symm_apply ⟨r, hr⟩)

theorem leftBranch_branchRho {z : ℝ} (hz : z ∈ Icc (0 : ℝ) spinodal) :
    leftBranch (branchRho z) = z := by
  apply strictMonoOn_branchRho_left.injOn (leftBranch_mem_Icc (branchRho_left_mapsTo hz)) hz
  exact branchRho_leftBranch (branchRho_left_mapsTo hz)

@[simp] theorem leftBranch_zero : leftBranch 0 = 0 := by
  simpa using leftBranch_branchRho ⟨le_rfl, le_of_lt spinodal_spec.1.1⟩

@[simp] theorem leftBranch_spinodalValue : leftBranch spinodalValue = spinodal :=
  leftBranch_branchRho ⟨le_of_lt spinodal_spec.1.1, le_rfl⟩

theorem strictMonoOn_leftBranch : StrictMonoOn leftBranch (Icc (0 : ℝ) spinodalValue) := by
  intro r hr s hs hrs
  rw [leftBranch_eq hr, leftBranch_eq hs]
  exact leftBranchIso.symm.strictMono hrs

theorem leftBranch_spec {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    leftBranch r ∈ Ioc (0 : ℝ) spinodal ∧ branchRho (leftBranch r) = r := by
  have hr' : r ∈ Icc (0 : ℝ) spinodalValue := ⟨le_of_lt hr.1, hr.2⟩
  refine ⟨⟨?_, (leftBranch_mem_Icc hr').2⟩, branchRho_leftBranch hr'⟩
  have hp := strictMonoOn_leftBranch ⟨le_rfl, le_of_lt spinodalValue_mem_Ioo.1⟩ hr' hr.1
  simpa using hp

theorem leftBranch_lt_spinodal {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    leftBranch r < spinodal := by
  have hp := strictMonoOn_leftBranch ⟨le_of_lt hr.1, le_of_lt hr.2⟩
    ⟨le_of_lt spinodalValue_mem_Ioo.1, le_rfl⟩ hr.2
  simpa using hp

theorem deriv_branchRho_leftBranch_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    0 < deriv branchRho (leftBranch r) :=
  spinodal_spec.2.2.1 _ ⟨(leftBranch_spec ⟨hr.1, le_of_lt hr.2⟩).1.1, leftBranch_lt_spinodal hr⟩

theorem continuousOn_leftBranch_Icc : ContinuousOn leftBranch (Icc (0 : ℝ) spinodalValue) := by
  rw [continuousOn_iff_continuous_restrict]
  have h := continuous_subtype_val.comp leftBranchIso.symm.continuous
  convert h using 1
  ext r
  exact leftBranch_eq r.property

theorem continuousOn_leftBranch : ContinuousOn leftBranch (Ioc (0 : ℝ) spinodalValue) :=
  continuousOn_leftBranch_Icc.mono Ioc_subset_Icc_self

theorem strictAntiOn_branchRho_right : StrictAntiOn branchRho (Ico spinodal 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico spinodal 1)
  · intro z hz
    exact (contDiffAt_branchRho (lt_of_lt_of_le spinodal_spec.1.1 hz.1) hz.2).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ico] at hz
    exact spinodal_spec.2.2.2 z hz

theorem branchRho_right_mapsTo : MapsTo branchRho (Ico spinodal 1) (Ioc 0 spinodalValue) := by
  intro z hz
  exact ⟨(branchRho_mem_Ioo (lt_of_lt_of_le spinodal_spec.1.1 hz.1) hz.2).1,
    strictAntiOn_branchRho_right.antitoneOn ⟨le_rfl, spinodal_spec.1.2⟩ hz hz.1⟩

theorem branchRho_right_surjOn : SurjOn branchRho (Ico spinodal 1) (Ioc 0 spinodalValue) := by
  intro r hr
  have hv : ∀ᶠ z : ℝ in 𝓝[<] 1, branchRho z < r :=
    tendsto_branchRho_one.eventually (eventually_lt_nhds hr.1)
  have hz : ∀ᶠ z : ℝ in 𝓝[<] 1, spinodal < z :=
    (eventually_gt_nhds spinodal_spec.1.2).filter_mono nhdsWithin_le_nhds
  have hz1 : ∀ᶠ z : ℝ in 𝓝[<] 1, z < 1 := self_mem_nhdsWithin
  obtain ⟨b, hbv, hbs, hb1⟩ := (hv.and (hz.and hz1)).exists
  have hc : ContinuousOn branchRho (Icc spinodal b) := by
    intro z hz
    exact (contDiffAt_branchRho (lt_of_lt_of_le spinodal_spec.1.1 hz.1)
      (lt_of_le_of_lt hz.2 hb1)).continuousAt.continuousWithinAt
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc' (le_of_lt hbs) hc ⟨le_of_lt hbv, hr.2⟩
  exact ⟨z, ⟨hz.1, lt_of_le_of_lt hz.2 hb1⟩, he⟩

/-- The decreasing half of the branch, with reversed order on the value interval. -/
def rightBranchIso : Ico spinodal (1 : ℝ) ≃o (Ioc (0 : ℝ) spinodalValue)ᵒᵈ where
  toEquiv := Equiv.ofBijective (fun z => ⟨branchRho z, branchRho_right_mapsTo z.property⟩)
    ⟨fun x y h => Subtype.ext (strictAntiOn_branchRho_right.injOn x.property y.property (congrArg Subtype.val h)),
      fun r => by
        obtain ⟨z, hz, he⟩ := branchRho_right_surjOn r.property
        exact ⟨⟨z, hz⟩, Subtype.ext he⟩⟩
  map_rel_iff' := strictAntiOn_branchRho_right.le_iff_ge (Subtype.property _) (Subtype.property _)

/-- The decreasing inverse z₂(r), with its natural endpoint r=r_sp included. -/
def rightBranch (r : ℝ) : ℝ :=
  if hr : r ∈ Ioc (0 : ℝ) spinodalValue then (rightBranchIso.symm ⟨r, hr⟩ : ℝ) else 1

theorem rightBranch_eq {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    rightBranch r = (rightBranchIso.symm ⟨r, hr⟩ : ℝ) := dif_pos hr

theorem rightBranch_mem_Ico {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    rightBranch r ∈ Ico spinodal (1 : ℝ) := by
  rw [rightBranch_eq hr]
  exact (rightBranchIso.symm ⟨r, hr⟩).property

theorem branchRho_rightBranch {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    branchRho (rightBranch r) = r := by
  rw [rightBranch_eq hr]
  exact congrArg Subtype.val (rightBranchIso.apply_symm_apply ⟨r, hr⟩)

theorem rightBranch_branchRho {z : ℝ} (hz : z ∈ Ico spinodal (1 : ℝ)) :
    rightBranch (branchRho z) = z := by
  apply strictAntiOn_branchRho_right.injOn (rightBranch_mem_Ico (branchRho_right_mapsTo hz)) hz
  exact branchRho_rightBranch (branchRho_right_mapsTo hz)

@[simp] theorem rightBranch_spinodalValue : rightBranch spinodalValue = spinodal :=
  rightBranch_branchRho ⟨le_rfl, spinodal_spec.1.2⟩

theorem strictAntiOn_rightBranch : StrictAntiOn rightBranch (Ioc (0 : ℝ) spinodalValue) := by
  intro r hr s hs hrs
  rw [rightBranch_eq hr, rightBranch_eq hs]
  exact rightBranchIso.symm.strictMono hrs

theorem spinodal_lt_rightBranch {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    spinodal < rightBranch r := by
  have hp := strictAntiOn_rightBranch ⟨hr.1, le_of_lt hr.2⟩
    ⟨spinodalValue_mem_Ioo.1, le_rfl⟩ hr.2
  simpa using hp

theorem rightBranch_spec {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) spinodalValue) :
    rightBranch r ∈ Ico spinodal (1 : ℝ) ∧ branchRho (rightBranch r) = r :=
  ⟨rightBranch_mem_Ico hr, branchRho_rightBranch hr⟩

theorem deriv_branchRho_rightBranch_neg {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    deriv branchRho (rightBranch r) < 0 :=
  spinodal_spec.2.2.2 _ ⟨spinodal_lt_rightBranch hr, (rightBranch_mem_Ico ⟨hr.1, le_of_lt hr.2⟩).2⟩

theorem continuousOn_rightBranch : ContinuousOn rightBranch (Ioc (0 : ℝ) spinodalValue) := by
  rw [continuousOn_iff_continuous_restrict]
  have h := continuous_subtype_val.comp rightBranchIso.symm.continuous
  convert h using 1
  ext r
  exact rightBranch_eq r.property

/-- The spinodal gives the strict maximum of ρ on the open unit interval. -/
theorem branchRho_lt_spinodalValue {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (hne : z ≠ spinodal) :
    branchRho z < spinodalValue := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact strictMonoOn_branchRho_left ⟨le_of_lt hz.1, le_of_lt hlt⟩
      ⟨le_of_lt spinodal_spec.1.1, le_rfl⟩ hlt
  · exact strictAntiOn_branchRho_right ⟨le_rfl, spinodal_spec.1.2⟩ ⟨le_of_lt hgt, hz.2⟩ hgt

theorem branchRho_le_spinodalValue {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    branchRho z ≤ spinodalValue := by
  by_cases he : z = spinodal
  · subst z
    rfl
  · exact le_of_lt (branchRho_lt_spinodalValue hz he)

/-- All three strict signs relative to a sub-spinodal target, for `thm:crossing`. -/
theorem branchRho_level_signs {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    (∀ z ∈ Ioo (0 : ℝ) (leftBranch r), branchRho z < r) ∧
    (∀ z ∈ Ioo (leftBranch r) (rightBranch r), r < branchRho z) ∧
    (∀ z ∈ Ioo (rightBranch r) 1, branchRho z < r) := by
  have hl := leftBranch_spec ⟨hr.1, le_of_lt hr.2⟩
  have hu := rightBranch_spec ⟨hr.1, le_of_lt hr.2⟩
  have hls := leftBranch_lt_spinodal hr
  have hus := spinodal_lt_rightBranch hr
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [← hl.2]
    exact strictMonoOn_branchRho_left ⟨le_of_lt hz.1, le_of_lt (hz.2.trans hls)⟩
      ⟨le_of_lt hl.1.1, le_of_lt hls⟩ hz.2
  · intro z hz
    by_cases hzs : z ≤ spinodal
    · rw [← hl.2]
      exact strictMonoOn_branchRho_left ⟨le_of_lt hl.1.1, le_of_lt hls⟩
        ⟨le_of_lt (hl.1.1.trans hz.1), hzs⟩ hz.1
    · rw [← hu.2]
      exact strictAntiOn_branchRho_right ⟨le_of_lt (lt_of_not_ge hzs), hz.2.trans hu.1.2⟩ hu.1 hz.2
  · intro z hz
    rw [← hu.2]
    exact strictAntiOn_branchRho_right hu.1 ⟨le_of_lt (hus.trans hz.1), hz.2⟩ hz.1

/-- Exactly two solutions below the spinodal, as asserted after `lem:unimodal`. -/
theorem branchRho_eq_iff_branches {r z : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    branchRho z = r ↔ z = leftBranch r ∨ z = rightBranch r := by
  constructor
  · intro he
    by_cases hzs : z ≤ spinodal
    · left
      apply strictMonoOn_branchRho_left.injOn ⟨le_of_lt hz.1, hzs⟩
        (leftBranch_mem_Icc ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
      exact he.trans (branchRho_leftBranch ⟨le_of_lt hr.1, le_of_lt hr.2⟩).symm
    · right
      apply strictAntiOn_branchRho_right.injOn ⟨le_of_lt (lt_of_not_ge hzs), hz.2⟩
        (rightBranch_mem_Ico ⟨hr.1, le_of_lt hr.2⟩)
      exact he.trans (branchRho_rightBranch ⟨hr.1, le_of_lt hr.2⟩).symm
  · rintro (rfl | rfl)
    · exact branchRho_leftBranch ⟨le_of_lt hr.1, le_of_lt hr.2⟩
    · exact branchRho_rightBranch ⟨hr.1, le_of_lt hr.2⟩

theorem leftBranch_mapsTo : MapsTo leftBranch (Ioc (0 : ℝ) spinodalValue) (Ioo (0 : ℝ) 1) := by
  intro r hr
  have h := (leftBranch_spec hr).1
  exact ⟨h.1, lt_of_le_of_lt h.2 spinodal_spec.1.2⟩

theorem rightBranch_mapsTo : MapsTo rightBranch (Ioc (0 : ℝ) spinodalValue) (Ioo (0 : ℝ) 1) := by
  intro r hr
  have h := rightBranch_mem_Ico hr
  exact ⟨lt_of_lt_of_le spinodal_spec.1.1 h.1, h.2⟩

/-- Classical inverse differentiation, instantiated with the constructed left branch. -/
theorem hasDerivAt_leftBranch {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    HasDerivAt leftBranch (deriv branchRho (leftBranch r))⁻¹ r := by
  have hz := leftBranch_mapsTo ⟨hr.1, le_of_lt hr.2⟩
  have hc := (continuousOn_leftBranch.mono Ioo_subset_Ioc_self).continuousAt (isOpen_Ioo.mem_nhds hr)
  apply (((contDiffAt_branchRho hz.1 hz.2).differentiableAt (by norm_num)).hasDerivAt).of_local_left_inverse hc
    (ne_of_gt (deriv_branchRho_leftBranch_pos hr))
  filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
  exact branchRho_leftBranch ⟨le_of_lt ht.1, le_of_lt ht.2⟩

theorem hasDerivAt_rightBranch {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) spinodalValue) :
    HasDerivAt rightBranch (deriv branchRho (rightBranch r))⁻¹ r := by
  have hz := rightBranch_mapsTo ⟨hr.1, le_of_lt hr.2⟩
  have hc := (continuousOn_rightBranch.mono Ioo_subset_Ioc_self).continuousAt (isOpen_Ioo.mem_nhds hr)
  apply (((contDiffAt_branchRho hz.1 hz.2).differentiableAt (by norm_num)).hasDerivAt).of_local_left_inverse hc
    (ne_of_lt (deriv_branchRho_rightBranch_neg hr))
  filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
  exact branchRho_rightBranch ⟨ht.1, le_of_lt ht.2⟩

private theorem contDiffOn_inverse_from_derivative {σ : ℝ → ℝ}
    (hc : ContinuousOn σ (Ioo (0 : ℝ) spinodalValue))
    (hm : MapsTo σ (Ioo (0 : ℝ) spinodalValue) (Ioo (0 : ℝ) 1))
    (hn : ∀ r ∈ Ioo (0 : ℝ) spinodalValue, deriv branchRho (σ r) ≠ 0)
    (hd : ∀ r ∈ Ioo (0 : ℝ) spinodalValue,
      HasDerivAt σ (deriv branchRho (σ r))⁻¹ r) :
    ContDiffOn ℝ 1 σ (Ioo (0 : ℝ) spinodalValue) := by
  have hdc := (contDiffOn_branchRho.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).comp hc hm
  have hdinv := hdc.inv₀ hn
  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun r hr => (hd r hr).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · rw [contDiffOn_zero]
    exact hdinv.congr (fun r hr => (hd r hr).deriv)

theorem contDiffOn_leftBranch : ContDiffOn ℝ 1 leftBranch (Ioo (0 : ℝ) spinodalValue) :=
  contDiffOn_inverse_from_derivative (continuousOn_leftBranch.mono Ioo_subset_Ioc_self)
    (leftBranch_mapsTo.mono_left Ioo_subset_Ioc_self)
    (fun _ hr => ne_of_gt (deriv_branchRho_leftBranch_pos hr)) (fun _ hr => hasDerivAt_leftBranch hr)

theorem contDiffOn_rightBranch : ContDiffOn ℝ 1 rightBranch (Ioo (0 : ℝ) spinodalValue) :=
  contDiffOn_inverse_from_derivative (continuousOn_rightBranch.mono Ioo_subset_Ioc_self)
    (rightBranch_mapsTo.mono_left Ioo_subset_Ioc_self)
    (fun _ hr => ne_of_lt (deriv_branchRho_rightBranch_neg hr)) (fun _ hr => hasDerivAt_rightBranch hr)

end SparseLowerTail.Section04

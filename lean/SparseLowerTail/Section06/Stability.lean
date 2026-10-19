import SparseLowerTail.Section06.LocalRigidity
import SparseLowerTail.Section04.BipodalMinimizers
import SparseLowerTail.Section02.RelabelBalanced

/-! Stability of the actual graphon minimizer classification under target limits. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section06
open Section02 Section04 Section05

/-- Compactness in the actual infimum cut distance, deduced from the two narrow
classical measure-space inputs already used by the development. -/
theorem exists_cutDistance_subsequence (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (U : ℕ→Graphon) :
    ∃ W : Graphon,∃ σ : ℕ→ℕ,StrictMono σ ∧
      Tendsto (fun n => cutDistance (U (σ n)) W) atTop (𝓝 0) := by
  obtain ⟨W,σ,φ,hσ,hcut⟩ := hcompact U
  refine ⟨W,σ,hσ,?_⟩
  apply squeeze_zero (fun n => cutDistance_nonneg _ _) _ hcut
  intro n
  have h := cutDistance_triangle (U (σ n)) (relabel (U (σ n)) (φ n)) W
  rw [cutDistance_relabel_zero hpull,zero_add] at h
  have hb := cutDistance_le_relabel (relabel (U (σ n)) (φ n)) W BijectiveRelabeling.identity
  exact h.trans hb

/-- Branch data at every target up to the crossing. -/
theorem branch_data_at {r : ℝ} (hr : r∈Ioc (0:ℝ) threshold) :
    0<branchA (leftBranch r) ∧ branchA (leftBranch r)<branchB (leftBranch r) ∧
    branchB (leftBranch r)<1 ∧ 0<branchMu (leftBranch r) ∧
    BalancedEL (branchA (leftBranch r)) (branchB (leftBranch r)) (branchMu (leftBranch r)) := by
  have hrs : r∈Ioo (0:ℝ) spinodalValue := ⟨hr.1,by
    rw [threshold_eq_transitionTarget] at hr
    exact hr.2.trans_lt transitionTarget_spec.1.2⟩
  exact branch_spec (leftBranch_mem_unit hrs).1 (leftBranch_mem_unit hrs).2

/-- The graphon multiplier of the balanced branch is its scalar multiplier. -/
theorem balanced_branch_multiplier {r : ℝ} (hr : r∈Ioc (0:ℝ) threshold) {W : Graphon}
    (hW : IsBalanced W (branchA (leftBranch r)) (branchB (leftBranch r))) :
    graphonMultiplier W r=branchMu (leftBranch r) := by
  have hs := branch_data_at hr
  obtain ⟨ha,hb⟩ := hW.values_mem_Icc
  have hrs : r∈Ioo (0:ℝ) spinodalValue := ⟨hr.1,by
    rw [threshold_eq_transitionTarget] at hr
    exact hr.2.trans_lt transitionTarget_spec.1.2⟩
  have hz := leftBranch_mem_unit hrs
  have htri : balancedTriangle (branchA (leftBranch r)) (branchB (leftBranch r))=r^3 := by
    rw [(branch_eq_scaled_ray hz.1).1,(branch_eq_scaled_ray hz.1).2,
      scaled_ray_triangle hz.1,branchRho_leftBranch ⟨hr.1.le,hrs.2.le⟩]
  have hm := balancedEL_multiplier_cost hs.2.2.2.2
  rw [htri] at hm
  unfold graphonMultiplier
  rw [hW.cost_eq ha hb,hW.edgeDensity_eq]
  exact (div_eq_iff (pow_ne_zero 3 hr.1.ne')).mpr hm.symm

/-- The substantive stability implication: a branch-shaped cut limit forces
all sufficiently late minimizers to have the unique branch parameters. -/
theorem eventually_balanced_of_branch_limit (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcount : ClassicalTriangleCounting)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) threshold) {rn : ℕ→ℝ}
    (hrn : ∀ n,rn n∈Ioo (0:ℝ) threshold) (hrt : Tendsto rn atTop (𝓝 r))
    {U : ℕ→Graphon} {W : Graphon} (hU : ∀ n,IsMinimizer (rn n) (U n))
    (hcut : Tendsto (fun n => cutDistance (U n) W) atTop (𝓝 0))
    (hW : IsBalanced W (branchA (leftBranch r)) (branchB (leftBranch r))) :
    ∀ᶠ n in atTop,IsBalanced (U n) (branchA (leftBranch (rn n))) (branchB (leftBranch (rn n))) := by
  have hr1 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt threshold_mem_Ioo.2⟩
  have hrn1 : ∀ n,rn n∈Ioo (0:ℝ) 1 := fun n => ⟨(hrn n).1,(hrn n).2.trans threshold_mem_Ioo.2⟩
  have hmu := (minimizer_limits_cutDistance hdyadic hcount hr1 hrn1 hrt hU hcut).2.2.2
  rw [balanced_branch_multiplier hr hW] at hmu
  obtain ⟨ha,hab,hb,hμ,hEL⟩ := branch_data_at hr
  obtain ⟨P,hP,hm,he⟩ := hW.exists_twoBlock ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩
  have hc : Tendsto (fun n => cutDistance (U n)
      (twoBlock P hP _ _ ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => cutDistance_nonneg _ _) _ hcut
    intro n
    have hh := cutDistance_triangle (U n) W (twoBlock P hP _ _ ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩)
    simpa only [cutDistance_eq_zero_of_ae he,add_zero] using hh
  have hh := eventually_bipodal_of_cutDistance hSampling hP hm ha hab hb hμ hEL hrn1 hU hc hmu
  filter_upwards [hh] with n hn
  obtain ⟨c,a,d,b,hbip⟩ := hn
  exact (bipodal_minimizer_classification hSampling (hrn n) (hU n) hbip).1

/-- The classification property used in the continuation argument. -/
def BranchClassification (r : ℝ) : Prop :=
  ∀ U : Graphon,IsMinimizer r U ↔
    IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r))

/-- Once every minimizer is on the branch, attainment supplies the converse too. -/
theorem branchClassification_of_minimizers (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) threshold)
    (h : ∀ U : Graphon,IsMinimizer r U →
      IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r))) :
    BranchClassification r := by
  obtain ⟨W,hW⟩ := exists_minimizer hdyadic hcompact hcount
    ⟨hr.1.le,(hr.2.trans threshold_mem_Ioo.2).le⟩
  have hBW := h W hW
  obtain ⟨ha,hb⟩ := hBW.values_mem_Icc
  intro U
  refine ⟨h U,fun hBU => ?_⟩
  apply isMinimizer_iff.mpr
  constructor
  · change triangle U≤r^3
    rw [hBU.triangle_eq ha hb,← hBW.triangle_eq ha hb]
    exact hW.1
  · rw [hBU.cost_eq ha hb,← hBW.cost_eq ha hb]
    exact (isMinimizer_iff.mp hW).2

/-- `prop:stability` for a fixed target sequence: if every subsequential cut
limit of every choice of minimizers is the limiting balanced branch, the exact
classification holds at all sufficiently late targets. -/
theorem eventually_branchClassification_of_subsequence_limits (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    {r₀ : ℝ} (hr₀ : r₀∈Ioc (0:ℝ) threshold) {rn : ℕ→ℝ}
    (hrn : ∀ n,rn n∈Ioo (0:ℝ) threshold) (hrt : Tendsto rn atTop (𝓝 r₀))
    (hlimits : ∀ (U : ℕ→Graphon), (∀ n,IsMinimizer (rn n) (U n)) →
      ∀ (W : Graphon) (σ : ℕ→ℕ),StrictMono σ →
      Tendsto (fun n => cutDistance (U (σ n)) W) atTop (𝓝 0) →
        IsBalanced W (branchA (leftBranch r₀)) (branchB (leftBranch r₀))) :
    ∀ᶠ n in atTop,BranchClassification (rn n) := by
  classical
  by_contra hbad
  have hchoices : ∀ n,∃ U : Graphon,IsMinimizer (rn n) U ∧
      (¬BranchClassification (rn n) →
        ¬IsBalanced U (branchA (leftBranch (rn n))) (branchB (leftBranch (rn n)))) := by
    intro n
    by_cases hn : BranchClassification (rn n)
    · obtain ⟨U,hU⟩ := exists_minimizer hdyadic hcompact hcount
        ⟨(hrn n).1.le,((hrn n).2.trans threshold_mem_Ioo.2).le⟩
      exact ⟨U,hU,fun hnot => False.elim (hnot hn)⟩
    · have hnb : ¬∀ U : Graphon,IsMinimizer (rn n) U →
          IsBalanced U (branchA (leftBranch (rn n))) (branchB (leftBranch (rn n))) :=
        fun hh => hn (branchClassification_of_minimizers hdyadic hcompact hcount (hrn n) hh)
      push_neg at hnb
      obtain ⟨U,hU,hnot⟩ := hnb
      exact ⟨U,hU,fun _ => hnot⟩
  choose U hU hbadU using hchoices
  have hfreq : ∃ᶠ n in atTop,¬BranchClassification (rn n) := by
    simpa only [Filter.Frequently,not_not] using hbad
  obtain ⟨σ,hσ,hσbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨W,τ,hτ,hcut⟩ := exists_cutDistance_subsequence hcompact hpull (fun n => U (σ n))
  have hW := hlimits U hU W (σ ∘ τ) (hσ.comp hτ) hcut
  have he := eventually_balanced_of_branch_limit hSampling hdyadic hcount hr₀
    (fun n => hrn (σ (τ n))) (hrt.comp (hσ.comp hτ).tendsto_atTop)
    (fun n => hU (σ (τ n))) hcut hW
  obtain ⟨n,hn⟩ := he.exists
  exact hbadU (σ (τ n)) (hσbad (τ n)) hn

/-- Compactness plus local rigidity upgrades branch-shaped limits to a full
neighborhood of target values. Every premise refers to actual graphons. -/
theorem branchClassification_near_of_limits (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    {r₀ : ℝ} (hr₀ : r₀∈Ioc (0:ℝ) threshold)
    (hlimits : ∀ (rn : ℕ→ℝ), (∀ n,rn n∈Ioo (0:ℝ) threshold) →
      Tendsto rn atTop (𝓝 r₀) → ∀ (U : ℕ→Graphon), (∀ n,IsMinimizer (rn n) (U n)) →
      ∀ W : Graphon,Tendsto (fun n => cutDistance (U n) W) atTop (𝓝 0) →
        IsBalanced W (branchA (leftBranch r₀)) (branchB (leftBranch r₀))) :
    ∃ δ : ℝ,0<δ ∧ ∀ r∈Ioo (0:ℝ) threshold,|r-r₀|<δ → BranchClassification r := by
  by_contra hbad
  have hseq : ∀ n : ℕ,∃ r : ℝ,∃ U : Graphon,
      r∈Ioo (0:ℝ) threshold ∧ |r-r₀|<1/((n:ℝ)+1) ∧ IsMinimizer r U ∧
      ¬IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) := by
    intro n
    have he : 0<1/((n:ℝ)+1) := by positivity
    have hf : ¬∀ r∈Ioo (0:ℝ) threshold,|r-r₀|<1/((n:ℝ)+1) → BranchClassification r :=
      fun hh => hbad ⟨_,he,hh⟩
    push_neg at hf
    obtain ⟨r,hr,hclose,hnot⟩ := hf
    have hn : ¬∀ U : Graphon,IsMinimizer r U →
        IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) :=
      fun hh => hnot (branchClassification_of_minimizers hdyadic hcompact hcount hr hh)
    push_neg at hn
    obtain ⟨U,hU,hbadU⟩ := hn
    exact ⟨r,U,hr,hclose,hU,hbadU⟩
  choose rn U hrn hclose hU hbadU using hseq
  have hrt : Tendsto rn atTop (𝓝 r₀) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    exact squeeze_zero (fun n => abs_nonneg _) (fun n => (hclose n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨W,σ,hσ,hcut⟩ := exists_cutDistance_subsequence hcompact hpull U
  have hrt' := hrt.comp hσ.tendsto_atTop
  have hW := hlimits (fun n => rn (σ n)) (fun n => hrn (σ n)) hrt'
    (fun n => U (σ n)) (fun n => hU (σ n)) W hcut
  have hh := eventually_balanced_of_branch_limit hSampling hdyadic hcount hr₀
    (fun n => hrn (σ n)) hrt' (fun n => hU (σ n)) hcut hW
  obtain ⟨n,hn⟩ := hh.exists
  exact hbadU (σ n) hn

/-- `cor:open`: exact classification of unrestricted minimizers is open below
the crossing, with an actual interval contained in the subcritical regime. -/
theorem branchClassification_open (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    {r₀ : ℝ} (hr₀ : r₀∈Ioo (0:ℝ) threshold) (h₀ : BranchClassification r₀) :
    ∃ δ : ℝ,0<δ ∧ Ioo (r₀-δ) (r₀+δ)⊆Ioo (0:ℝ) threshold ∧
      ∀ r∈Ioo (r₀-δ) (r₀+δ),BranchClassification r := by
  obtain ⟨ε,hε,hnear⟩ := branchClassification_near_of_limits hSampling hdyadic hcompact hpull hcount
    ⟨hr₀.1,hr₀.2.le⟩ (by
      intro rn hrn hrt U hU W hcut
      have hr1 : r₀∈Ioo (0:ℝ) 1 := ⟨hr₀.1,hr₀.2.trans threshold_mem_Ioo.2⟩
      have hrn1 : ∀ n,rn n∈Ioo (0:ℝ) 1 := fun n => ⟨(hrn n).1,(hrn n).2.trans threshold_mem_Ioo.2⟩
      exact (h₀ W).mp (minimizer_limits_cutDistance hdyadic hcount hr1 hrn1 hrt hU hcut).1)
  let δ := min ε (min (r₀/2) ((threshold-r₀)/2))
  have hδ : 0<δ := lt_min hε (lt_min (by linarith [hr₀.1]) (by linarith [hr₀.2]))
  have hdε : δ≤ε := min_le_left _ _
  have hdr : δ≤r₀/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdt : δ≤(threshold-r₀)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Ioo (r₀-δ) (r₀+δ)⊆Ioo (0:ℝ) threshold := by
    intro r hr
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  refine ⟨δ,hδ,hsub,?_⟩
  intro r hr
  apply hnear r (hsub hr)
  exact (abs_lt.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩).trans_le hdε

/-- `cor:seed`: classification holds on a genuine left neighborhood of the
threshold. CriticalClassification remains the explicit internal obligation. -/
theorem branchClassification_seed (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hcrit : CriticalClassification) :
    ∃ δ : ℝ,0<δ ∧ 0<threshold-δ ∧
      ∀ r∈Ioo (threshold-δ) threshold,BranchClassification r := by
  obtain ⟨ε,hε,hnear⟩ := branchClassification_near_of_limits hSampling hdyadic hcompact hpull hcount
    ⟨threshold_mem_Ioo.1,le_rfl⟩ (by
      intro rn hrn hrt U hU W hcut
      have hh := balanced_left_limit_cutDistance hdyadic hcount hcrit hrn hrt hU
        (σ:=id) strictMono_id hcut
      simpa only [criticalA,criticalB,transitionParameter,threshold_eq_transitionTarget] using hh)
  let δ := min ε (threshold/2)
  have hδ : 0<δ := lt_min hε (by linarith [threshold_mem_Ioo.1])
  have hdε : δ≤ε := min_le_left _ _
  have hdt : δ≤threshold/2 := min_le_right _ _
  refine ⟨δ,hδ,by linarith [threshold_mem_Ioo.1],?_⟩
  intro r hr
  apply hnear r ⟨by linarith [hr.1,threshold_mem_Ioo.1],hr.2⟩
  apply lt_of_lt_of_le _ hdε
  rw [abs_of_neg (sub_neg.mpr hr.2)]
  linarith [hr.1]

/-- The good-target region is an open subset of the real line. -/
theorem branchClassification_region_open (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting) :
    IsOpen {r : ℝ | r∈Ioo (0:ℝ) threshold ∧ BranchClassification r} := by
  apply isOpen_iff_mem_nhds.mpr
  intro r hr
  obtain ⟨δ,hδ,hsub,hgood⟩ := branchClassification_open hSampling hdyadic hcompact hpull hcount hr.1 hr.2
  apply mem_of_superset (Ioo_mem_nhds (by linarith : r-δ<r) (by linarith : r<r+δ))
  intro s hs
  exact ⟨hsub hs,hgood s hs⟩

/-- The measurable-partition classification has precisely the manuscript's
measure-preserving-relabeling meaning, using only the classical CDF transform. -/
theorem branchClassification_relabel_iff (hCDF : ClassicalCDFTransport) {r : ℝ}
    (ha : branchA (leftBranch r)∈Icc (0:ℝ) 1)
    (hb : branchB (leftBranch r)∈Icc (0:ℝ) 1) :
    BranchClassification r ↔ ∀ U : Graphon,IsMinimizer r U ↔
      IsBalancedRelabeling U (branchA (leftBranch r)) (branchB (leftBranch r)) ha hb := by
  constructor
  · intro h U
    exact (h U).trans (isBalanced_iff_relabel hCDF ha hb)
  · intro h U
    exact (h U).trans (isBalanced_iff_relabel hCDF ha hb).symm

end SparseLowerTail.Section06

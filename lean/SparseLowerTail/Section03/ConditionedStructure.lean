import SparseLowerTail.Section03.ConditionedStructureFinite
import SparseLowerTail.Section03.ReductionParameters
import SparseLowerTail.Section03.ReductionLargeN

/-! The conditioned graph approaches an actual graphon minimizer throughout the sparse regime. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02

/-- The conditional probability of having no minimizer within ε, in the genuine relabeling formulation. -/
def triangleConditionalFarMass (n : ℕ) (p r ε : ℝ) : ℝ :=
  if hn : 0<n then finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p (r^3))
    (triangleFarEvent n hn p r ε) else 0

theorem triangleConditionalFarMass_nonneg (n : ℕ) {p : ℝ} (hp : p∈Icc (0:ℝ) 1) (r ε : ℝ) :
    0≤triangleConditionalFarMass n p r ε := by
  unfold triangleConditionalFarMass
  split_ifs
  · exact Finset.sum_nonneg (fun z _ => hypergraphLowerLaw_nonneg _ 3 hp _ z)
  · exact le_rfl

/-- Increasing the allowed cut error only decreases the probability of failure. -/
theorem triangleConditionalFarMass_antitone (n : ℕ) {p r ε ε' : ℝ} (hp : p∈Icc (0:ℝ) 1) (he : ε≤ε') :
    triangleConditionalFarMass n p r ε'≤triangleConditionalFarMass n p r ε := by
  classical
  by_cases hn : 0<n
  · unfold triangleConditionalFarMass
    rw [dif_pos hn,dif_pos hn]
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun z _ _ => hypergraphLowerLaw_nonneg _ 3 hp _ z)
    intro z hz
    simp only [triangleFarEvent,Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    intro hclose
    obtain ⟨U,hU,φ,hφ⟩ := hclose
    exact hz ⟨U,hU,φ,hφ.trans_le he⟩
  · simp [triangleConditionalFarMass,hn]

/-- Every fixed probability tolerance eventually bounds the failure probability by half that tolerance. -/
theorem triangle_conditioned_structure_eventually
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    (hHarris : ∀ (ν : Type) [Fintype ν] [DecidableEq ν], ClassicalHarrisPositiveAssociation ν)
    {η ε θ : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hε : ε∈Ioo (0:ℝ) 1) (hθ : θ∈Ioo (0:ℝ) 1)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    ∀ᶠ j in atTop, triangleConditionalFarMass (n j) (p j) (η^(1/3:ℝ)) ε≤θ/2 := by
  let r := η^(1/3:ℝ)
  have hr : r∈Ioo (0:ℝ) 1 := ⟨Real.rpow_pos_of_pos hη.1 _,Real.rpow_lt_one hη.1.le hη.2 (by norm_num)⟩
  have hrcube : r^3=η := by
    simpa only [r,one_div] using Real.rpow_inv_natCast_pow hη.1.le (by norm_num : (3:ℕ)≠0)
  obtain ⟨δ,hδ,hfinite⟩ := triangle_far_probability_estimate hdyadic hcompact hpull hcount r hε
  obtain ⟨P⟩ := exists_reduction_parameters hr hε hδ hθ
  obtain ⟨L,hL,hdec⟩ := triangle_decorrelation hSelection hCS P.alpha_mem P.beta_mem
  have hcast : Tendsto (fun j => (n j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hinv : Tendsto (fun j => 1/(n j:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcast
  have hinvsmall : ∀ᶠ j in atTop, 1/(n j:ℝ)≤min (P.ω/8) (δ/2) :=
    (hinv.eventually_lt_const (lt_min (div_pos P.omega_pos (by norm_num)) (div_pos hδ (by norm_num)))).mono (fun _ h => h.le)
  have hrate := triangleLowerTailRate_tendsto hdyadic hcompact hcount hlower hupper hη n p hn hp hpzero hsparse
  have hratebound : ∀ᶠ j in atTop, triangleLowerTailRate (n j) (p j) η/triangleRateScale (n j) (p j)≤value r+P.ζ :=
    (hrate.eventually_lt_const (lt_add_of_pos_right _ P.zeta_pos)).mono (fun _ h => h.le)
  have hsmall : ∀ᶠ j in atTop, p j≤1/2 :=
    (hpzero.eventually_lt_const (by norm_num : (0:ℝ)<1/2)).mono (fun _ h => h.le)
  have hpnonneg : ∀ j, 0≤p j := fun j => (hp j).1.le
  have hnp := sparse_edge_scale_tendsto_atTop n p hn hpnonneg hsparse
  have hvolume := sparse_volume_tendsto_atTop n p hn hpnonneg hsparse
  have hpref := eventually_cut_prefactor_bound n p hn hnp hε.1
  have hlogexp := eventually_reduction_log_exp_bounds n p hvolume P.omega_pos P.alpha_mem.1 hθ.1
  filter_upwards [eventually_sparse_threshold n p (L:=L) hn hsparse,hcast.eventually_ge_atTop L,
    hinvsmall,hratebound,hsmall,hpref,hlogexp] with j hj hjL hjinv hjrate hjp hjpref hjlogexp
  have hn3 : 3≤n j := by omega
  have hnpos : 0<n j := by omega
  have hpL : L*(n j:ℝ)^(-(1/(2:ℝ)))≤p j := by rw [sparse_half_power_identity]; exact hj.2
  obtain ⟨W,hW,hdecor⟩ := hdec (n j) hjL (p j) hpL hjp η hη
  have hbaseline := conditional_value_baseline_bounds (n j) hr.1 P.s_mem.1.le P.s_mem.2.le P.alpha_mem.1.le
    P.scale_loss (hjinv.trans (min_le_left _ _)) P.alpha_omega
  have hcost : P.γ+2*P.α+1/(n j:ℝ)≤δ := by
    have hi := hjinv.trans (min_le_right _ _)
    linarith [P.gamma_alpha]
  have hs : P.s^3=η+P.ζ := by rw [P.s_cube,hrcube]
  have hprob := hfinite (n j) hn3 (p j) η P.α P.γ P.ζ P.s P.β P.ω
    (hp j) hjp hη.1.le hrcube P.alpha_mem.1.le P.alpha_eps P.gamma_pos P.zeta_pos P.zeta_delta
    hcost hs hbaseline.2.2 hbaseline.1 hbaseline.2.1 P.zeta_omega P.beta_omega hjrate hjpref hjlogexp.1
    (hHarris (GraphEdgeCoordinate (n j))) W (hHarris (↑Wᶜ)) hW hdecor
  change triangleConditionalFarMass (n j) (p j) r ε≤θ/2
  rw [triangleConditionalFarMass,dif_pos hnpos,hrcube]
  exact hprob.trans (by linarith [P.beta_theta,P.cost_theta,P.cut_theta,hjlogexp.2])

/-- Full conditioned-structure convergence, in the strong form with a genuine minimizer and bijection. -/
theorem triangle_conditioned_structure_tendsto_small
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    (hHarris : ∀ (ν : Type) [Fintype ν] [DecidableEq ν], ClassicalHarrisPositiveAssociation ν)
    {η ε : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hε : ε∈Ioo (0:ℝ) 1)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleConditionalFarMass (n j) (p j) (η^(1/3:ℝ)) ε) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    apply Eventually.of_forall
    intro j
    apply hb.trans_le
    unfold triangleConditionalFarMass
    split_ifs
    · exact Finset.sum_nonneg (fun z _ => hypergraphLowerLaw_nonneg _ 3 ⟨(hp j).1.le,(hp j).2.le⟩ _ z)
    · exact le_rfl
  · intro a ha
    let θ := min a (1/2)
    have hθ : θ∈Ioo (0:ℝ) 1 := ⟨lt_min ha (by norm_num),lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have hh := triangle_conditioned_structure_eventually hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
      hη hε hθ n p hn hp hpzero hsparse
    filter_upwards [hh] with j hj
    exact hj.trans_lt (by have ht : θ≤a := min_le_left _ _; linarith)

/-- The full conditioned-structure statement for every ε>0, along every sparse sequence. -/
theorem triangle_conditioned_structure_tendsto
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    (hHarris : ∀ (ν : Type) [Fintype ν] [DecidableEq ν], ClassicalHarrisPositiveAssociation ν)
    {η ε : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hε : 0<ε)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleConditionalFarMass (n j) (p j) (η^(1/3:ℝ)) ε) atTop (𝓝 0) := by
  let ε₀ := min ε (1/2)
  have hε₀ : ε₀∈Ioo (0:ℝ) 1 := ⟨lt_min hε (by norm_num),lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hh := triangle_conditioned_structure_tendsto_small hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
    hη hε₀ n p hn hp hpzero hsparse
  exact squeeze_zero (fun j => triangleConditionalFarMass_nonneg (n j) ⟨(hp j).1.le,(hp j).2.le⟩ _ ε)
    (fun j => triangleConditionalFarMass_antitone (n j) ⟨(hp j).1.le,(hp j).2.le⟩ (min_le_left _ _)) hh

/-- The actual successful event: an actual minimizer and an actual measure-preserving bijection exist. -/
def triangleCloseEvent (n : ℕ) (hn : 0<n) (p r ε : ℝ) : Finset (GraphEdgeCoordinate n → Bool) := by
  classical
  exact Finset.univ.filter (TriangleClose n hn p r ε)

def triangleConditionalCloseMass (n : ℕ) (p r ε : ℝ) : ℝ :=
  if hn : 0<n then finiteEventMass (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p (r^3))
    (triangleCloseEvent n hn p r ε) else 1

/-- The success and failure masses are complementary under the normalized actual conditional law. -/
theorem triangleConditionalCloseMass_eq (n : ℕ) {p : ℝ} (hp : p∈Ioo (0:ℝ) 1) (r ε : ℝ) (hr : 0≤r^3) :
    triangleConditionalCloseMass n p r ε=1-triangleConditionalFarMass n p r ε := by
  classical
  by_cases hn : 0<n
  · unfold triangleConditionalCloseMass triangleConditionalFarMass
    rw [dif_pos hn,dif_pos hn]
    have hc : (triangleFarEvent n hn p r ε)ᶜ=triangleCloseEvent n hn p r ε := by
      ext z
      simp [triangleFarEvent,triangleCloseEvent]
    have hh := Finset.sum_add_sum_compl (triangleFarEvent n hn p r ε)
      (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p (r^3))
    rw [hypergraphLowerLaw_sum _ 3 (by norm_num) (fun _ hA => coordinateTriangleHypergraph_uniform hA) hp hr,hc] at hh
    change finiteEventMass _ (triangleFarEvent n hn p r ε)+finiteEventMass _ (triangleCloseEvent n hn p r ε)=1 at hh
    linarith
  · simp [triangleConditionalCloseMass,triangleConditionalFarMass,hn]

/-- Manuscript thm:reduction(b): the actual conditional probability of proximity to a minimizer tends to one. -/
theorem triangle_conditioned_structure_success_tendsto
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    (hHarris : ∀ (ν : Type) [Fintype ν] [DecidableEq ν], ClassicalHarrisPositiveAssociation ν)
    {η ε : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hε : 0<ε)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleConditionalCloseMass (n j) (p j) (η^(1/3:ℝ)) ε) atTop (𝓝 1) := by
  have hh := triangle_conditioned_structure_tendsto hdyadic hcompact hpull hcount hlower hupper hSelection hCS hHarris
    hη hε n p hn hp hpzero hsparse
  have he : ∀ j, triangleConditionalCloseMass (n j) (p j) (η^(1/3:ℝ)) ε=
      1-triangleConditionalFarMass (n j) (p j) (η^(1/3:ℝ)) ε := fun j =>
    triangleConditionalCloseMass_eq (n j) (hp j) _ ε (pow_nonneg (Real.rpow_pos_of_pos hη.1 _).le 3)
  simp_rw [he]
  simpa only [sub_zero] using (tendsto_const_nhds.sub hh)

/-- Both parts of the manuscript's reduction theorem, with only the named external/classical hypotheses. -/
theorem triangle_reduction
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    (hHarris : ∀ (ν : Type) [Fintype ν] [DecidableEq ν], ClassicalHarrisPositiveAssociation ν)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/
      (triangleRateScale (n j) (p j)*value (η^(1/3:ℝ)))) atTop (𝓝 1) ∧
    ∀ ε : ℝ, 0<ε → Tendsto (fun j => triangleConditionalCloseMass (n j) (p j) (η^(1/3:ℝ)) ε) atTop (𝓝 1) :=
  ⟨triangleLowerTailRate_ratio_tendsto_one hdyadic hcompact hcount hlower hupper hη n p hn hp hpzero hsparse,
    fun _ hε => triangle_conditioned_structure_success_tendsto hdyadic hcompact hpull hcount hlower hupper
      hSelection hCS hHarris hη hε n p hn hp hpzero hsparse⟩

end SparseLowerTail.Section03

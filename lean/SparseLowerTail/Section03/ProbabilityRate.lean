import SparseLowerTail.Section03.ConditionedStructure
import SparseLowerTail.MainReplayAssembly

/-! The probability-rate corollary of the main variational classification. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02 Section04

/-- The replica-symmetric variational value is attained precisely above the threshold. -/
theorem value_eq_entropy_iff_threshold_le (hmain : MainTheorem) {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) :
    value r=entropy r ↔ threshold≤r := by
  have hle := value_le_entropy ⟨hr.1.le,hr.2.le⟩
  have hstrict := hmain.strict_improvement r hr
  constructor
  · intro he
    by_contra hh
    have hi := hstrict.mpr (lt_of_not_ge hh)
    linarith
  · intro hh
    apply le_antisymm hle
    by_contra he
    have hi := hstrict.mp (lt_of_not_ge he)
    linarith

/-- Cubing the threshold gives exactly the triangle-density transition. -/
theorem threshold_le_cubeRoot_iff {η : ℝ} (hη : η∈Ioo (0:ℝ) 1) :
    threshold≤η^(1/3:ℝ) ↔ threshold^3≤η := by
  have hr : 0≤η^(1/3:ℝ) := (Real.rpow_pos_of_pos hη.1 _).le
  have hc : (η^(1/3:ℝ))^3=η := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hη.1.le (by norm_num : (3:ℕ)≠0)
  simpa only [hc] using (pow_le_pow_iff_left₀ threshold_mem_Ioo.1.le hr (by norm_num : (3:ℕ)≠0)).symm

/-- The complete probability-rate corollary, conditional only on the main classification
and the same generic external/classical inputs as the already-proved reduction. -/
theorem triangle_probability_rate (hmain : MainTheorem)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hcount : ClassicalTriangleCounting) (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1) (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/
      (triangleRateScale (n j) (p j)*balancedValue (η^(1/3:ℝ)))) atTop (𝓝 1) ∧
    (Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/
      (triangleRateScale (n j) (p j)*entropy (η^(1/3:ℝ)))) atTop (𝓝 1) ↔ threshold^3≤η) := by
  let r := η^(1/3:ℝ)
  have hr : r∈Ioo (0:ℝ) 1 := ⟨Real.rpow_pos_of_pos hη.1 _,Real.rpow_lt_one hη.1.le hη.2 (by norm_num)⟩
  have hrate := triangleLowerTailRate_ratio_tendsto_one hdyadic hcompact hcount hlower hupper hη n p hn hp hpzero hsparse
  have hvalue := hmain.value_reduction r hr
  refine ⟨?_,?_⟩
  · change value (η^(1/3:ℝ))=balancedValue (η^(1/3:ℝ)) at hvalue
    simpa only [hvalue] using hrate
  · have hbase := triangleLowerTailRate_tendsto hdyadic hcompact hcount hlower hupper hη n p hn hp hpzero hsparse
    have hv := value_pos_bounds hdyadic hcompact hcount hr
    have hepos : 0<entropy r := hv.1.trans_le hv.2.1
    have hh : Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/
        (triangleRateScale (n j) (p j)*entropy r)) atTop (𝓝 (value r/entropy r)) := by
      have hlim := hbase.div_const (entropy r)
      simpa only [div_div] using hlim
    have heq : value r/entropy r=1 ↔ threshold^3≤η := by
      rw [div_eq_one_iff_eq (ne_of_gt hepos),value_eq_entropy_iff_threshold_le hmain hr]
      exact threshold_le_cubeRoot_iff hη
    constructor
    · intro ht
      exact heq.mp (tendsto_nhds_unique hh ht)
    · intro ht
      rwa [heq.mpr ht] at hh


/-- The rate corollary assembled directly from the outstanding finite certificate replays. -/
theorem triangle_probability_rate_of_remaining_replays
    (external : Section07.KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : Section07.PositiveKernelSpectralTheorem)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hnJobs : Section05.RemainingNonapexJobResults) (haJobs : Section05.ApexJobResults)
    (hABB : Certificate.FamilyABBLocal)
    (hExterior : Certificate.FamilyABBLocal → Section08.CompactFamilyCertificate)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1) (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/
      (triangleRateScale (n j) (p j)*balancedValue (η^(1/3:ℝ)))) atTop (𝓝 1) ∧
    (Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/
      (triangleRateScale (n j) (p j)*entropy (η^(1/3:ℝ)))) atTop (𝓝 1) ↔ threshold^3≤η) :=
  triangle_probability_rate (mainTheorem_of_remaining_replays external hSampling hSpectral
    hdyadic hcompact hpull hcount hnJobs haJobs hABB hExterior)
    hdyadic hcompact hcount hlower hupper hη n p hn hp hpzero hsparse

end SparseLowerTail.Section03

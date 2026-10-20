import SparseLowerTail.Section03.RateSandwich

/-! The triangle lower-tail rate, deduced from the discrete variational limit and generic KS23 bounds. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02

/-- The actual normalized triangle log probability converges throughout the sparse regime. -/
theorem triangleLowerTailRate_tendsto (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/triangleRateScale (n j) (p j))
      atTop (𝓝 (value (η^(1/3:ℝ)))) := by
  let ε : ℕ → ℝ := fun k => (1-η)/((k:ℝ)+2)
  have hε : ∀ k, ε k∈Ioo (0:ℝ) (1-η) := by
    intro k
    have hk : (0:ℝ)≤k := Nat.cast_nonneg k
    have hd : (0:ℝ)<(k:ℝ)+2 := by linarith
    constructor
    · exact div_pos (by linarith [hη.2]) hd
    · apply (div_lt_iff₀ hd).mpr
      nlinarith [hη.2]
  have hεzero : Tendsto ε atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  obtain ⟨hF,hG⟩ := targetValue_perturbations_tendsto hη
  have hF' := hF.comp hεzero
  have hG' := hG.comp hεzero
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨k,hk⟩ := (hF'.eventually_const_lt hb).exists
    obtain ⟨f,g,hf,hg,hsand⟩ := triangleRate_sandwich hdyadic hcompact hcount hlower hupper
      hη (hε k) n p hn hp hpzero hsparse
    filter_upwards [hsand,hf.eventually_const_lt hk] with j hj hbj
    exact hbj.trans_le hj.1
  · intro a ha
    obtain ⟨k,hk⟩ := (hG'.eventually_lt_const ha).exists
    obtain ⟨f,g,hf,hg,hsand⟩ := triangleRate_sandwich hdyadic hcompact hcount hlower hupper
      hη (hε k) n p hn hp hpzero hsparse
    filter_upwards [hsand,hg.eventually_lt_const hk] with j hj hja
    exact hj.2.trans_lt hja

/-- The manuscript's multiplicative lower-tail asymptotic, including positivity of its leading value. -/
theorem triangleLowerTailRate_ratio_tendsto_one (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    {η : ℝ} (hη : η∈Ioo (0:ℝ) 1)
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    Tendsto (fun j => triangleLowerTailRate (n j) (p j) η/
      (triangleRateScale (n j) (p j)*value (η^(1/3:ℝ)))) atTop (𝓝 1) := by
  have hr : η^(1/3:ℝ)∈Ioo (0:ℝ) 1 := ⟨Real.rpow_pos_of_pos hη.1 _,
    Real.rpow_lt_one hη.1.le hη.2 (by norm_num)⟩
  have hv : value (η^(1/3:ℝ))≠0 := ne_of_gt (value_pos_bounds hdyadic hcompact hcount hr).1
  simpa only [div_div,div_self hv] using
    (triangleLowerTailRate_tendsto hdyadic hcompact hcount hlower hupper hη n p hn hp hpzero hsparse).div_const
      (value (η^(1/3:ℝ)))

end SparseLowerTail.Section03

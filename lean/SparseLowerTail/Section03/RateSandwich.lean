import SparseLowerTail.Section03.TriangleRateComparison

/-! Vanishing-error rate sandwiches, with the actual finite triangle probabilities. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section03
open Section02

/-- The normalized log probability is trapped between convergent sequences for each fixed perturbation. -/
theorem triangleRate_sandwich (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    (hlower : KS23HypergraphLowerBound) (hupper : KS23HypergraphUpperBound)
    {η ε : ℝ} (hη : η∈Ioo (0:ℝ) 1) (hε : ε∈Ioo (0:ℝ) (1-η))
    (n : ℕ → ℕ) (p : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hp : ∀ j, p j∈Ioo (0:ℝ) 1) (hpzero : Tendsto p atTop (𝓝 0))
    (hsparse : Tendsto (fun j => Real.sqrt (n j:ℝ)*p j) atTop atTop) :
    ∃ f g : ℕ → ℝ,
      Tendsto f atTop (𝓝 ((1-ε)*value ((η+ε)^(1/3:ℝ)))) ∧
      Tendsto g atTop (𝓝 ((1+ε)*value (((1-ε)*η)^(1/3:ℝ)))) ∧
      ∀ᶠ j in atTop,
        f j≤triangleLowerTailRate (n j) (p j) η/triangleRateScale (n j) (p j) ∧
        triangleLowerTailRate (n j) (p j) η/triangleRateScale (n j) (p j)≤g j := by
  obtain ⟨L,hL,C₁,hC₁,C₂,hC₂,hKS⟩ := triangle_KS_comparison hlower hupper ⟨hε.1,by linarith [hε.2,hη.1]⟩
  have hscale := triangleRateScale_tendsto_atTop n p hn (fun j => (hp j).1.le) hsparse
  have hlowtarget : η+ε∈Ioo (0:ℝ) 1 := ⟨by linarith [hη.1,hε.1],by linarith [hε.2]⟩
  have huptarget : (1-ε)*η∈Ioo (0:ℝ) 1 := by
    have hε1 : ε<1 := by linarith [hε.2,hη.1]
    constructor
    · exact mul_pos (by linarith) hη.1
    · nlinarith [mul_pos hε.1 hη.1, hη.2]
  let f : ℕ → ℝ := fun j => (1-ε)*(finiteTrianglePhi (n j) (p j) (η+ε)/triangleRateScale (n j) (p j))-
    C₁/triangleRateScale (n j) (p j)
  let g : ℕ → ℝ := fun j => (1+ε)*(finiteTrianglePhi (n j) (p j) ((1-ε)*η)/triangleRateScale (n j) (p j))+
    C₂/triangleRateScale (n j) (p j)
  have hf : Tendsto f atTop (𝓝 ((1-ε)*value ((η+ε)^(1/3:ℝ)))) := by
    simpa only [sub_zero] using
      ((finiteTrianglePhi_tendsto hdyadic hcompact hcount hlowtarget n p hn hp hpzero).const_mul (1-ε)).sub
        (hscale.const_div_atTop C₁)
  have hg : Tendsto g atTop (𝓝 ((1+ε)*value (((1-ε)*η)^(1/3:ℝ)))) := by
    simpa only [add_zero] using
      ((finiteTrianglePhi_tendsto hdyadic hcompact hcount huptarget n p hn hp hpzero).const_mul (1+ε)).add
        (hscale.const_div_atTop C₂)
  refine ⟨f,g,hf,hg,?_⟩
  have hsmall : ∀ᶠ j in atTop, p j≤1/2 :=
    ((hpzero.eventually_lt_const (by norm_num : (0:ℝ)<1/2))).mono (fun _ h => h.le)
  filter_upwards [eventually_sparse_threshold n p hn hsparse,hsmall] with j hj hjp
  have hnpos : 0 < n j := lt_of_lt_of_le (by norm_num : 0 < 4) hj.1
  have hnreal : (0:ℝ) < n j := Nat.cast_pos.mpr hnpos
  have hs : 0<triangleRateScale (n j) (p j) :=
    div_pos (mul_pos (sq_pos_of_pos hnreal) (hp j).1) (by norm_num)
  obtain ⟨hlo,hhi⟩ := hKS (n j) hj.1 (p j) η (hp j) hjp hj.2 hη.1.le
  constructor
  · have hh := div_le_div_of_nonneg_right hlo hs.le
    convert hh using 1; dsimp [f]; ring
  · have hh := div_le_div_of_nonneg_right hhi hs.le
    convert hh using 1; dsimp [g]; ring

/-- The graphon target value is continuous at every interior lower-tail parameter. -/
theorem targetValue_continuousAt {η : ℝ} (hη : η∈Ioo (0:ℝ) 1) :
    ContinuousAt (fun u : ℝ => value (u^(1/3:ℝ))) η := by
  have hr : η^(1/3:ℝ)∈Ioo (0:ℝ) 1 := ⟨Real.rpow_pos_of_pos hη.1 _,
    Real.rpow_lt_one hη.1.le hη.2 (by norm_num)⟩
  have hroot : ContinuousAt (fun u : ℝ => u^(1/3:ℝ)) η :=
    (Real.continuous_rpow_const (by norm_num : (0:ℝ)≤1/3)).continuousAt
  have hvalue : ContinuousAt value (η^(1/3:ℝ)) :=
    continuousOn_value.continuousAt (isOpen_Ioo.mem_nhds hr)
  exact hvalue.comp (f := fun u : ℝ => u^(1/3:ℝ)) hroot

/-- The two limiting KS perturbation bounds meet at the unrestricted graphon value. -/
theorem targetValue_perturbations_tendsto {η : ℝ} (hη : η∈Ioo (0:ℝ) 1) :
    Tendsto (fun ε : ℝ => (1-ε)*value ((η+ε)^(1/3:ℝ))) (𝓝 0) (𝓝 (value (η^(1/3:ℝ)))) ∧
    Tendsto (fun ε : ℝ => (1+ε)*value (((1-ε)*η)^(1/3:ℝ))) (𝓝 0) (𝓝 (value (η^(1/3:ℝ)))) := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
  have h1 : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
  have hηc : Tendsto (fun _ : ℝ => η) (𝓝 0) (𝓝 η) := tendsto_const_nhds
  have hplus : Tendsto (fun ε : ℝ => η+ε) (𝓝 0) (𝓝 η) := by simpa only [add_zero] using hηc.add hid
  have hminus : Tendsto (fun ε : ℝ => (1-ε)*η) (𝓝 0) (𝓝 η) := by
    simpa only [sub_zero,one_mul] using (h1.sub hid).mul_const η
  constructor
  · simpa only [sub_zero,one_mul] using
      (h1.sub hid).mul ((targetValue_continuousAt hη).tendsto.comp hplus)
  · simpa only [add_zero,one_mul] using
      (h1.add hid).mul ((targetValue_continuousAt hη).tendsto.comp hminus)

end SparseLowerTail.Section03

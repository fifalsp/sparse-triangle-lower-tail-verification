import SparseLowerTail.Section07.PenalizedDigitsCore

/-! Exact numerical bounds used in the current proof of lem:tie. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07.EndpointProof
open Section04 Numerics
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem milli_log_lower : Bounds (-Real.log (1/1000 : ℝ)) (172693881974553426301349359101327/25000000000000000000000000000000 : ℝ) (690775527898213705205397436405311/100000000000000000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-3/125 : ℝ)) (by norm_num) 90
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (128/125 : ℝ)=10*Real.log 2+Real.log (1/1000 : ℝ) := by
    rw [show (128/125 : ℝ)=(2:ℝ)^10*(1/1000 : ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_40.1
  have h2u := log_two_bounds_40.2
  constructor <;> linarith

theorem milli_log {z : ℝ} (hz : z ∈ Icc (1/1000 : ℝ) (1/1000 : ℝ)) : Bounds (branchLog z) (172693881974553426301349359101327/25000000000000000000000000000000 : ℝ) (690775527898213705205397436405311/100000000000000000000000000000000 : ℝ) := by
  have hz0 : 0<z := lt_of_lt_of_le (by norm_num : 0<(1/1000 : ℝ)) hz.1
  have hlo := Real.log_le_log (by norm_num : 0<(1/1000 : ℝ)) hz.1
  have hhi := Real.log_le_log hz0 hz.2
  have hl := milli_log_lower.1
  have hu := milli_log_lower.2
  rw [branchLog_eq_neg_log]
  constructor <;> linarith

theorem milli_exponent {z : ℝ} (hz : z ∈ Icc (1/1000 : ℝ) (1/1000 : ℝ)) : Bounds (2*z*branchLog z/(1-z)^2) (3460795770235769829916991247530353/250000000000000000000000000000000000 : ℝ) (13843183080943079319667964990121473/1000000000000000000000000000000000000 : ℝ) := by
  have hZ : Bounds z (1/1000 : ℝ) (1/1000 : ℝ) := hz
  have hL := milli_log hz
  let v1 : ℝ := (2 : ℝ)*z
  have h1 : Bounds v1 (1/500 : ℝ) (1/500 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hZ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v2 : ℝ := v1*(branchLog z)
  have h2 : Bounds v2 (172693881974553426301349359101327/12500000000000000000000000000000000 : ℝ) (690775527898213705205397436405311/50000000000000000000000000000000000 : ℝ) := by
    exact h1.mul_corners hL (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v3 : ℝ := (1 : ℝ)-z
  have h3 : Bounds v3 (999/1000 : ℝ) (999/1000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  let v4 : ℝ := v3*v3
  have h4 : Bounds v4 (998001/1000000 : ℝ) (998001/1000000 : ℝ) := by
    exact h3.mul_corners h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v5 : ℝ := v2/v4
  have h5 : Bounds v5 (3460795770235769829916991247530353/250000000000000000000000000000000000 : ℝ) (13843183080943079319667964990121473/1000000000000000000000000000000000000 : ℝ) := by
    exact (h2.div_pos h4 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have he : 2*z*branchLog z/(1-z)^2=v5 := by
    dsimp only [v1,v2,v3,v4,v5,branchMu,branchA,branchRho,balancedTriangle]
    ring
  rw [he]
  exact h5

theorem milli_exp_lower : Bounds (Real.exp (-13843183080943079319667964990121473/1000000000000000000000000000000000000 : ℝ)) (49312609658355411468184020798399/50000000000000000000000000000000 : ℝ) (98625219316710822936368041596801/100000000000000000000000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-13843183080943079319667964990121473/1000000000000000000000000000000000000 : ℝ)) (by norm_num) (n := 20) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem milli_exp_upper : Bounds (Real.exp (-3460795770235769829916991247530353/250000000000000000000000000000000000 : ℝ)) (49312609658355411468184020798399/50000000000000000000000000000000 : ℝ) (98625219316710822936368041596801/100000000000000000000000000000000 : ℝ) := by
  have h := Real.exp_bound (x := (-3460795770235769829916991247530353/250000000000000000000000000000000000 : ℝ)) (by norm_num) (n := 20) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

theorem milli_B {z : ℝ} (hz : z ∈ Icc (1/1000 : ℝ) (1/1000 : ℝ)) : Bounds (branchB z) (49312609658355411468184020798399/50000000000000000000000000000000 : ℝ) (98625219316710822936368041596801/100000000000000000000000000000000 : ℝ) := by
  have hE := milli_exponent hz
  have hlo := Real.exp_le_exp.mpr (neg_le_neg hE.2)
  have hhi := Real.exp_le_exp.mpr (neg_le_neg hE.1)
  have he : branchB z=Real.exp (-(2*z*branchLog z/(1-z)^2)) := by unfold branchB;congr 1;ring
  rw [← he] at hlo hhi
  have hl := milli_exp_lower.1
  have hu := milli_exp_upper.2
  constructor <;> linarith

theorem milli_K {z : ℝ} (hz : z ∈ Icc (1/1000 : ℝ) (1/1000 : ℝ)) : Bounds (kappa z) (2271400993418006647209702992013/25000000000000000000000000000000 : ℝ) (1817120794734405317767762393611/20000000000000000000000000000000 : ℝ) := by
  have hlo := kappa_mono_nonneg (by norm_num : 0≤(1/1000 : ℝ)) hz.1
  have hhi := kappa_mono_nonneg (le_trans (by norm_num : 0≤(1/1000 : ℝ)) hz.1) hz.2
  have hl : (2271400993418006647209702992013/25000000000000000000000000000000 : ℝ)≤kappa (1/1000 : ℝ) := by
    apply (show Odd (3:ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [kappa_cube (by norm_num : 0≤(1/1000 : ℝ))]
    norm_num
  have hu : kappa (1/1000 : ℝ)≤(1817120794734405317767762393611/20000000000000000000000000000000 : ℝ) := by
    apply (show Odd (3:ℕ) by decide).strictMono_pow.le_iff_le.mp
    rw [kappa_cube (by norm_num : 0≤(1/1000 : ℝ))]
    norm_num
  exact ⟨hl.trans hlo,hhi.trans hu⟩

theorem milli_data {z : ℝ} (hz : z ∈ Icc (1/1000 : ℝ) (1/1000 : ℝ)) :
    Bounds (branchMu z) (14231805463289424911732385140986047137/1000000000000000000000000000000000000 : ℝ) (14231805463289424911732385140986974789/1000000000000000000000000000000000000 : ℝ) ∧
    Bounds (branchRho z) (44803484226409148393682694247865353/500000000000000000000000000000000000 : ℝ) (4480348422640914839368269424788151/50000000000000000000000000000000000 : ℝ) ∧
    Bounds ((branchA z+branchB z)/2) (49361922268013766879652204819197399/100000000000000000000000000000000000 : ℝ) (98723844536027533759304409638397801/200000000000000000000000000000000000 : ℝ) ∧
    Bounds (balancedTriangle (branchA z) (branchB z)) (359745490307810379124330745689401/500000000000000000000000000000000000 : ℝ) (719490980615620758248661491378869/1000000000000000000000000000000000000 : ℝ) ∧
    Bounds (balancedPenalty (branchMu z/3) (branchA z) (branchB z)) (499554340207387093054187001013420051/1000000000000000000000000000000000000 : ℝ) (124888585051846773263546750253359037/250000000000000000000000000000000000 : ℝ) := by
  have hZ : Bounds z (1/1000 : ℝ) (1/1000 : ℝ) := hz
  have hL := milli_log hz
  have hB := milli_B hz
  have hK := milli_K hz
  let v1 : ℝ := z*(branchB z)
  have h1 : Bounds v1 (49312609658355411468184020798399/50000000000000000000000000000000000 : ℝ) (98625219316710822936368041596801/100000000000000000000000000000000000 : ℝ) := by
    exact hZ.mul_corners hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v2 : ℝ := (2 : ℝ)*(branchLog z)
  have h2 : Bounds v2 (172693881974553426301349359101327/12500000000000000000000000000000 : ℝ) (690775527898213705205397436405311/50000000000000000000000000000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hL (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v3 : ℝ := (1 : ℝ)-z
  have h3 : Bounds v3 (999/1000 : ℝ) (999/1000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub hZ).weaken (by norm_num) (by norm_num)
  let v4 : ℝ := v3*v3
  have h4 : Bounds v4 (998001/1000000 : ℝ) (998001/1000000 : ℝ) := by
    exact h3.mul_corners h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v5 : ℝ := (branchB z)*(branchB z)
  have h5 : Bounds v5 (972693388526930964384478769920209407/1000000000000000000000000000000000000 : ℝ) (972693388526930964384478769920268583/1000000000000000000000000000000000000 : ℝ) := by
    exact hB.mul_corners hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v6 : ℝ := v4*v5
  have h6 : Bounds v6 (242687243610816407346668549214784727/250000000000000000000000000000000000 : ℝ) (970748974443265629386674196859197967/1000000000000000000000000000000000000 : ℝ) := by
    exact h4.mul_corners h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v7 : ℝ := v2/v6
  have h7 : Bounds v7 (14231805463289424911732385140986047137/1000000000000000000000000000000000000 : ℝ) (14231805463289424911732385140986974789/1000000000000000000000000000000000000 : ℝ) := by
    exact (h2.div_pos h6 (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v8 : ℝ := (kappa z)*(branchB z)
  have h8 : Bounds v8 (44803484226409148393682694247865353/500000000000000000000000000000000000 : ℝ) (4480348422640914839368269424788151/50000000000000000000000000000000000 : ℝ) := by
    exact hK.mul_corners hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v9 : ℝ := v1+(branchB z)
  have h9 : Bounds v9 (49361922268013766879652204819197399/50000000000000000000000000000000000 : ℝ) (98723844536027533759304409638397801/100000000000000000000000000000000000 : ℝ) := by
    exact (h1.add hB).weaken (by norm_num) (by norm_num)
  let v10 : ℝ := v9/(2 : ℝ)
  have h10 : Bounds v10 (49361922268013766879652204819197399/100000000000000000000000000000000000 : ℝ) (98723844536027533759304409638397801/200000000000000000000000000000000000 : ℝ) := by
    exact (h9.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v11 : ℝ := v1*v1
  have h11 : Bounds v11 (759916709786664815925374039/781250000000000000000000000000000 : ℝ) (972693388526930964384478769921/1000000000000000000000000000000000000 : ℝ) := by
    exact h1.mul_corners h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v12 : ℝ := v11*v1
  have h12 : Bounds v12 (95932098771383177305429097/100000000000000000000000000000000000 : ℝ) (959320987713831773054290971/1000000000000000000000000000000000000 : ℝ) := by
    exact h11.mul_corners h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v13 : ℝ := (3 : ℝ)*v1
  have h13 : Bounds v13 (147937828975066234404552062395197/50000000000000000000000000000000000 : ℝ) (295875657950132468809104124790403/100000000000000000000000000000000000 : ℝ) := by
    exact (Bounds.refl (3 : ℝ)).mul_corners h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v14 : ℝ := (branchB z)*(branchB z)
  have h14 : Bounds v14 (972693388526930964384478769920209407/1000000000000000000000000000000000000 : ℝ) (972693388526930964384478769920268583/1000000000000000000000000000000000000 : ℝ) := by
    exact hB.mul_corners hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v15 : ℝ := v13*v14
  have h15 : Bounds v15 (1438981481570747659581436455612119/500000000000000000000000000000000000 : ℝ) (1438981481570747659581436455612251/500000000000000000000000000000000000 : ℝ) := by
    exact h13.mul_corners h14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v16 : ℝ := v12+v15
  have h16 : Bounds v16 (359745490307810379124330745689401/125000000000000000000000000000000000 : ℝ) (2877963922462483032994645965515473/1000000000000000000000000000000000000 : ℝ) := by
    exact (h12.add h15).weaken (by norm_num) (by norm_num)
  let v17 : ℝ := v16/(4 : ℝ)
  have h17 : Bounds v17 (359745490307810379124330745689401/500000000000000000000000000000000000 : ℝ) (719490980615620758248661491378869/1000000000000000000000000000000000000 : ℝ) := by
    exact (h16.div_pos (Bounds.refl (4 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v18 : ℝ := (1 : ℝ)-v10
  have h18 : Bounds v18 (101276155463972466240695590361602199/200000000000000000000000000000000000 : ℝ) (50638077731986233120347795180802601/100000000000000000000000000000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub h10).weaken (by norm_num) (by norm_num)
  let v19 : ℝ := (2 : ℝ)*v7
  have h19 : Bounds v19 (14231805463289424911732385140986047137/500000000000000000000000000000000000 : ℝ) (14231805463289424911732385140986974789/500000000000000000000000000000000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v20 : ℝ := v19*v17
  have h20 : Bounds v20 (20479311337425714447872852383769587/1000000000000000000000000000000000000 : ℝ) (2047931133742571444787285238377283/100000000000000000000000000000000000 : ℝ) := by
    exact h19.mul_corners h17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v21 : ℝ := v20/(3 : ℝ)
  have h21 : Bounds v21 (3413218556237619074645475397294931/500000000000000000000000000000000000 : ℝ) (213326159764851192165342212330967/31250000000000000000000000000000000 : ℝ) := by
    exact (h20.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v22 : ℝ := v18-v21
  have h22 : Bounds v22 (499554340207387093054187001013420051/1000000000000000000000000000000000000 : ℝ) (124888585051846773263546750253359037/250000000000000000000000000000000000 : ℝ) := by
    exact (h18.sub h21).weaken (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_,?_⟩
  · have he : branchMu z=v7 := by
      dsimp only [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,branchMu,branchA,branchRho,balancedTriangle]
      ring
    rw [he]
    exact h7
  · have he : branchRho z=v8 := by
      dsimp only [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,branchMu,branchA,branchRho,balancedTriangle]
    rw [he]
    exact h8
  · have he : (branchA z+branchB z)/2=v10 := by
      dsimp only [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,branchMu,branchA,branchRho,balancedTriangle]
    rw [he]
    exact h10
  · have he : balancedTriangle (branchA z) (branchB z)=v17 := by
      dsimp only [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,branchMu,branchA,branchRho,balancedTriangle]
      ring
    rw [he]
    exact h17
  · have he : balancedPenalty (branchMu z/3) (branchA z) (branchB z)=v22 := by
      rw [branchPenalty_stationary ⟨lt_of_lt_of_le (by norm_num : 0<(1/1000 : ℝ)) hz.1,lt_of_le_of_lt hz.2 (by norm_num : (1/1000 : ℝ)<1)⟩]
      dsimp only [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,branchMu,branchA,branchRho,balancedTriangle]
      ring
    rw [he]
    exact h22

theorem trial_log : Bounds (-Real.log (3/10 : ℝ)) (60198640216296799631137310888091/50000000000000000000000000000000 : ℝ) (24079456086518719852454924355237/20000000000000000000000000000000 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/5 : ℝ)) (by norm_num) 60
  norm_num [Finset.sum_range_succ] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  have he : Real.log (6/5 : ℝ)=2*Real.log 2+Real.log (3/10 : ℝ) := by
    rw [show (6/5 : ℝ)=(2:ℝ)^2*(3/10 : ℝ) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
    norm_num
  rw [he] at hl hu
  have h2l := log_two_bounds_40.1
  have h2u := log_two_bounds_40.2
  constructor <;> linarith

theorem trial_penalty_lt : constantPenalty (branchMu (1/1000 : ℝ)/3) (3/10 : ℝ)<(468/1000:ℝ) := by
  have hM := (milli_data (z := (1/1000 : ℝ)) ⟨le_rfl,le_rfl⟩).1
  let v1 : ℝ := (1 : ℝ)-(3/10 : ℝ)
  have h1 : Bounds v1 (7/10 : ℝ) (7/10 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (3/10 : ℝ))).weaken (by norm_num) (by norm_num)
  let v2 : ℝ := (3/10 : ℝ)*(-Real.log (3/10 : ℝ))
  have h2 : Bounds v2 (180595920648890398893411932664273/500000000000000000000000000000000 : ℝ) (72238368259556159557364773065711/200000000000000000000000000000000 : ℝ) := by
    exact (Bounds.refl (3/10 : ℝ)).mul_corners trial_log (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v3 : ℝ := v1-v2
  have h3 : Bounds v3 (67761631740443840442635226934289/200000000000000000000000000000000 : ℝ) (169404079351109601106588067335727/500000000000000000000000000000000 : ℝ) := by
    exact (h1.sub h2).weaken (by norm_num) (by norm_num)
  let v4 : ℝ := (3/10 : ℝ)*(3/10 : ℝ)
  have h4 : Bounds v4 (9/100 : ℝ) (9/100 : ℝ) := by
    exact (Bounds.refl (3/10 : ℝ)).mul_corners (Bounds.refl (3/10 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v5 : ℝ := v4*(3/10 : ℝ)
  have h5 : Bounds v5 (27/1000 : ℝ) (27/1000 : ℝ) := by
    exact h4.mul_corners (Bounds.refl (3/10 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v6 : ℝ := (branchMu (1/1000 : ℝ))*v5
  have h6 : Bounds v6 (48032343438601809077096799850827909/125000000000000000000000000000000000 : ℝ) (150101073245630653365927499533847/390625000000000000000000000000000 : ℝ) := by
    exact hM.mul_corners h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v7 : ℝ := v6/(3 : ℝ)
  have h7 : Bounds v7 (16010781146200603025698933283609303/125000000000000000000000000000000000 : ℝ) (64043124584802412102795733134441387/500000000000000000000000000000000000 : ℝ) := by
    exact (h6.div_pos (Bounds.refl (3 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v8 : ℝ := v3+v7
  have h8 : Bounds v8 (7295225122997250412793243764692491/15625000000000000000000000000000000 : ℝ) (233447203935912013209383800470168387/500000000000000000000000000000000000 : ℝ) := by
    exact (h3.add h7).weaken (by norm_num) (by norm_num)
  have he : constantPenalty (branchMu (1/1000 : ℝ)/3) (3/10 : ℝ)=v8 := by
    dsimp only [v1,v2,v3,v4,v5,v6,v7,v8]
    unfold constantPenalty entropy
    ring
  rw [he]
  exact lt_of_le_of_lt h8.2 (by norm_num)

theorem milli_branch_penalty_gt : (496/1000:ℝ)<balancedPenalty (branchMu (1/1000)/3) (branchA (1/1000)) (branchB (1/1000)) := by
  have h := (milli_data (z := (1/1000:ℝ)) ⟨le_rfl,le_rfl⟩).2.2.2.2
  exact lt_of_lt_of_le (by norm_num) h.1

theorem milli_constant_minimum_lt : constantMinimum (branchMu (1/1000)/3)<(468/1000:ℝ) := by
  have hγ : 0<branchMu (1/1000)/3 := div_pos (branchMu_pos (by norm_num) (by norm_num)) (by norm_num)
  exact (constantPenalty_min hγ (by norm_num : (3/10:ℝ) ∈ Icc (0:ℝ) 1)).trans_lt trial_penalty_lt

theorem milli_gap_gt : (28/1000:ℝ)<penalizedGap (1/1000) := by
  rw [penalizedGap_eq (by norm_num : (0:ℝ)<1/1000)]
  have hl := milli_branch_penalty_gt
  have hu := milli_constant_minimum_lt
  change constantPenalty (branchMu (1/1000)/3) (constantRoot (branchMu (1/1000)/3))<468/1000 at hu
  linarith

end SparseLowerTail.Section07.EndpointProof

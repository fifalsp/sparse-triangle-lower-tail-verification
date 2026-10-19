import SparseLowerTail.Section07.SmallErrorBounds

/-! The ten-term error table from lem:smallparams(b), with actual error
expressions. Generated rational arithmetic is checked by the Lean kernel. -/
noncomputable section
namespace SparseLowerTail.Section07.SmallErrorData
open Numerics
theorem weighted_mean_upper (d : SmallErrorData) :
    d.mu*rowMeanError d.eta d.ev d.bound d.tail d.diagonal<(549/10000 : ℝ) := by
  let v1 : ℝ := (2 : ℝ)*(d.bound^2)
  have h1 : Bounds v1 (2 : ℝ) (40103/20000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners d.bound_sq_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v2 : ℝ := v1-(1 : ℝ)
  have h2 : Bounds v2 (1 : ℝ) (20103/20000 : ℝ) := by
    exact (h1.sub (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  let v3 : ℝ := (d.mu*d.eta)*v2
  have h3 : Bounds v3 (0 : ℝ) (462369/40000000 : ℝ) := by
    exact d.mu_eta_bounds.mul_corners h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v4 : ℝ := (3 : ℝ)*d.bound
  have h4 : Bounds v4 (3 : ℝ) (30039/10000 : ℝ) := by
    exact (Bounds.refl (3 : ℝ)).mul_corners d.bound_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v5 : ℝ := v4*(d.ev*d.mu*(d.bound-1))
  have h5 : Bounds v5 (0 : ℝ) (23099991/625000000 : ℝ) := by
    exact h4.mul_corners d.scaled_bound_defect_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (0 : ℝ) (242596053/5000000000 : ℝ) := by
    exact (h3.add h5).weaken (by norm_num) (by norm_num)
  let v7 : ℝ := (d.bound^2)*(d.mu*Real.sqrt (d.tail*d.diagonal)*Real.sqrt (2-2/d.bound))
  have h7 : Bounds v7 (0 : ℝ) (31606177/5000000000 : ℝ) := by
    exact d.bound_sq_bounds.mul_corners d.weighted_sqrt_mean_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v8 : ℝ := v6+v7
  have h8 : Bounds v8 (0 : ℝ) (27420223/500000000 : ℝ) := by
    exact (h6.add h7).weaken (by norm_num) (by norm_num)
  have he : d.mu*rowMeanError d.eta d.ev d.bound d.tail d.diagonal=v8 := by
    dsimp only [v1,v2,v3,v4,v5,v6,v7,v8]
    unfold rowMeanError
    ring
  rw [he]
  exact lt_of_le_of_lt h8.2 (by norm_num)

theorem weighted_codegree_upper (d : SmallErrorData) :
    d.mu*rowCodegreeError d.eta d.m d.ev d.bound d.tail d.diagonal<(699/10000 : ℝ) := by
  let v1 : ℝ := (d.mu*d.eta)*d.m
  have h1 : Bounds v1 (0 : ℝ) (23/4000 : ℝ) := by
    exact d.mu_eta_bounds.mul_corners d.mean_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v2 : ℝ := v1/(2 : ℝ)
  have h2 : Bounds v2 (0 : ℝ) (23/8000 : ℝ) := by
    exact (h1.div_pos (Bounds.refl (2 : ℝ)) (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  let v3 : ℝ := (2 : ℝ)*d.ev
  have h3 : Bounds v3 (4989/5000 : ℝ) (1 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners d.eigenvalue_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v4 : ℝ := v3*(d.bound^2)
  have h4 : Bounds v4 (4989/5000 : ℝ) (40103/40000 : ℝ) := by
    exact h3.mul_corners d.bound_sq_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v5 : ℝ := v4*(d.mu*d.eta)
  have h5 : Bounds v5 (0 : ℝ) (922369/80000000 : ℝ) := by
    exact h4.mul_corners d.mu_eta_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : Bounds v6 (0 : ℝ) (1152369/80000000 : ℝ) := by
    exact (h2.add h5).weaken (by norm_num) (by norm_num)
  let v7 : ℝ := v6+(d.mu*Real.sqrt (d.diagonal*d.tail*d.eta*d.m/2))
  have h7 : Bounds v7 (0 : ℝ) (1274209/80000000 : ℝ) := by
    exact (h6.add d.weighted_sqrt_codegree_bounds).weaken (by norm_num) (by norm_num)
  let v8 : ℝ := (4 : ℝ)*(d.bound^2)
  have h8 : Bounds v8 (4 : ℝ) (40103/10000 : ℝ) := by
    exact (Bounds.refl (4 : ℝ)).mul_corners d.bound_sq_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v9 : ℝ := d.m+d.eta
  have h9 : Bounds v9 (312/625 : ℝ) (2503/5000 : ℝ) := by
    exact (d.mean_bounds.add d.eta_bounds).weaken (by norm_num) (by norm_num)
  let v10 : ℝ := v8*v9
  have h10 : Bounds v10 (1248/625 : ℝ) (100377809/50000000 : ℝ) := by
    exact h8.mul_corners h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v11 : ℝ := v10*(d.mu*d.eta)
  have h11 : Bounds v11 (0 : ℝ) (230868961/10000000000 : ℝ) := by
    exact h10.mul_corners d.mu_eta_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v12 : ℝ := v7+v11
  have h12 : Bounds v12 (0 : ℝ) (195072543/5000000000 : ℝ) := by
    exact (h7.add h11).weaken (by norm_num) (by norm_num)
  let v13 : ℝ := (2 : ℝ)*(d.bound^2)
  have h13 : Bounds v13 (2 : ℝ) (40103/20000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners d.bound_sq_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v14 : ℝ := v13*(d.mu*d.tail)
  have h14 : Bounds v14 (0 : ℝ) (8060703/2500000000 : ℝ) := by
    exact h13.mul_corners d.mu_tail_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v15 : ℝ := v14*(Real.sqrt (d.eta*d.m/2))
  have h15 : Bounds v15 (0 : ℝ) (15799/400000000 : ℝ) := by
    exact h14.mul_corners d.sqrt_eta_mean_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v16 : ℝ := v12+v15
  have h16 : Bounds v16 (0 : ℝ) (390540061/10000000000 : ℝ) := by
    exact (h12.add h15).weaken (by norm_num) (by norm_num)
  let v17 : ℝ := (5 : ℝ)*d.ev
  have h17 : Bounds v17 (4989/2000 : ℝ) (5/2 : ℝ) := by
    exact (Bounds.refl (5 : ℝ)).mul_corners d.eigenvalue_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v18 : ℝ := v17*d.bound
  have h18 : Bounds v18 (4989/2000 : ℝ) (10013/4000 : ℝ) := by
    exact h17.mul_corners d.bound_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v19 : ℝ := v18*(d.ev*d.mu*(d.bound-1))
  have h19 : Bounds v19 (0 : ℝ) (7699997/250000000 : ℝ) := by
    exact h18.mul_corners d.scaled_bound_defect_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v20 : ℝ := v16+v19
  have h20 : Bounds v20 (0 : ℝ) (698539941/10000000000 : ℝ) := by
    exact (h16.add h19).weaken (by norm_num) (by norm_num)
  let v21 : ℝ := (2 : ℝ)*(d.bound^2)
  have h21 : Bounds v21 (2 : ℝ) (40103/20000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners d.bound_sq_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v22 : ℝ := v21*(d.mu*d.tail)
  have h22 : Bounds v22 (0 : ℝ) (8060703/2500000000 : ℝ) := by
    exact h21.mul_corners d.mu_tail_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v23 : ℝ := v22*(Real.sqrt (d.tail*d.diagonal))
  have h23 : Bounds v23 (0 : ℝ) (212803/10000000000 : ℝ) := by
    exact h22.mul_corners d.sqrt_tail_diagonal_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v24 : ℝ := v20+v23
  have h24 : Bounds v24 (0 : ℝ) (87344093/1250000000 : ℝ) := by
    exact (h20.add h23).weaken (by norm_num) (by norm_num)
  have he : d.mu*rowCodegreeError d.eta d.m d.ev d.bound d.tail d.diagonal=v24 := by
    dsimp only [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24]
    unfold rowCodegreeError
    ring
  rw [he]
  exact lt_of_le_of_lt h24.2 (by norm_num)

theorem weighted_base_upper (d : SmallErrorData) :
    d.mu*rowBaseError d.m d.eta d.ev d.bound<(1633/100000 : ℝ) := by
  let v1 : ℝ := d.m+d.eta
  have h1 : Bounds v1 (312/625 : ℝ) (2503/5000 : ℝ) := by
    exact (d.mean_bounds.add d.eta_bounds).weaken (by norm_num) (by norm_num)
  let v2 : ℝ := (d.mu*(1/2-d.m))*v1
  have h2 : Bounds v2 (0 : ℝ) (77593/10000000 : ℝ) := by
    exact d.mean_defect_bounds.mul_corners h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v3 : ℝ := d.ev*d.bound
  have h3 : Bounds v3 (4989/10000 : ℝ) (10013/20000 : ℝ) := by
    exact d.eigenvalue_bounds.mul_corners d.bound_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v4 : ℝ := (d.mu*(1/2-d.m))+(d.mu*d.tail)
  have h4 : Bounds v4 (0 : ℝ) (4277/250000 : ℝ) := by
    exact (d.mean_defect_bounds.add d.mu_tail_bounds).weaken (by norm_num) (by norm_num)
  let v5 : ℝ := v3*v4
  have h5 : Bounds v5 (0 : ℝ) (42825601/5000000000 : ℝ) := by
    exact h3.mul_corners h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v6 : ℝ := v2+v5
  have h6 : Bounds v6 (0 : ℝ) (81622101/5000000000 : ℝ) := by
    exact (h2.add h5).weaken (by norm_num) (by norm_num)
  have he : d.mu*rowBaseError d.m d.eta d.ev d.bound=v6 := by
    dsimp only [v1,v2,v3,v4,v5,v6]
    unfold rowBaseError
    rw [abs_of_nonpos (by linarith [d.mean_upper]),abs_of_nonpos (by linarith [d.eigenvalue_upper,d.mean_upper])]
    dsimp [tail]
    ring
  rw [he]
  exact lt_of_le_of_lt h6.2 (by norm_num)

end SparseLowerTail.Section07.SmallErrorData

import SparseLowerTail.Section07.RowErrors
import SparseLowerTail.Numerics.IntervalArithmetic

/-! Scalar error bounds in lem:smallparams(b). All quantitative assumptions
are explicit; the graphon wrapper supplies them from smallparams(a) and the
proved spectral inequalities. -/
noncomputable section
namespace SparseLowerTail.Section07
open Numerics

structure SmallErrorData where
  m : ℝ
  mu : ℝ
  t : ℝ
  ev : ℝ
  mean_lower : 4992/10000≤m
  mean_upper : m≤1/2
  mu_lower : 186/10≤mu
  triangle_nonneg : 0≤t
  triangle_upper : t≤63/1000000
  mut_upper : mu*t≤12/10000
  mu2t_upper : mu^2*t≤23/1000
  mean_defect : mu*(1/2-m)≤155/10000
  eigenvalue_pos : 0<ev
  eigenvalue_upper : ev≤m
  spectral_first : m^3-t≤m*ev^2
  spectral_second : 3*m*ev*(m-ev)≤t

namespace SmallErrorData

def eta (d : SmallErrorData) : ℝ := d.mu*d.t/2
def tail (d : SmallErrorData) : ℝ := d.m-d.ev
def diagonal (d : SmallErrorData) : ℝ := d.m+d.mu*d.t
def bound (d : SmallErrorData) : ℝ := Real.sqrt (d.diagonal/d.ev)

theorem mu_pos (d : SmallErrorData) : 0<d.mu := lt_of_lt_of_le (by norm_num) d.mu_lower
theorem mean_pos (d : SmallErrorData) : 0<d.m := lt_of_lt_of_le (by norm_num) d.mean_lower
theorem eta_nonneg (d : SmallErrorData) : 0≤d.eta := by
  unfold eta; exact div_nonneg (mul_nonneg d.mu_pos.le d.triangle_nonneg) (by norm_num)
theorem tail_nonneg (d : SmallErrorData) : 0≤d.tail := sub_nonneg.mpr d.eigenvalue_upper

theorem eigenvalue_lower (d : SmallErrorData) : 4989/10000<d.ev := by
  by_contra hn
  have hev : d.ev≤4989/10000 := le_of_not_gt hn
  have hev2 : d.ev^2≤(4989/10000:ℝ)^2 := by nlinarith [d.eigenvalue_pos]
  have hm2 : (4992/10000:ℝ)^2≤d.m^2 := by nlinarith [d.mean_lower]
  have hdiff : (4992/10000:ℝ)^2-(4989/10000:ℝ)^2≤d.m^2-d.ev^2 := by linarith
  have hh := mul_le_mul d.mean_lower hdiff (by norm_num : (0:ℝ)≤(4992/10000)^2-(4989/10000)^2) d.mean_pos.le
  nlinarith [d.spectral_first,d.triangle_upper]

theorem tail_upper (d : SmallErrorData) : d.tail≤(134/100)*d.t := by
  have hprod := mul_le_mul d.mean_lower d.eigenvalue_lower.le (by norm_num : (0:ℝ)≤4989/10000) d.mean_pos.le
  have hfactor : 1≤(134/100:ℝ)*(3*d.m*d.ev) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hfactor d.tail_nonneg
  have hs := mul_le_mul_of_nonneg_left d.spectral_second (by norm_num : (0:ℝ)≤134/100)
  dsimp [tail] at *
  nlinarith

theorem diagonal_pos (d : SmallErrorData) : 0<d.diagonal := by
  dsimp [diagonal]
  linarith [d.mean_pos,mul_nonneg d.mu_pos.le d.triangle_nonneg]

theorem bound_sq (d : SmallErrorData) : d.bound^2=d.diagonal/d.ev :=
  Real.sq_sqrt (div_nonneg d.diagonal_pos.le d.eigenvalue_pos.le)

theorem bound_sq_mul (d : SmallErrorData) : d.bound^2*d.ev=d.diagonal := by
  rw [d.bound_sq,div_mul_cancel₀ _ d.eigenvalue_pos.ne']

theorem bound_one_le (d : SmallErrorData) : 1≤d.bound := by
  have hpos : 0≤d.bound := Real.sqrt_nonneg _
  have hsq := d.bound_sq_mul
  have hmut : 0≤d.mu*d.t := mul_nonneg d.mu_pos.le d.triangle_nonneg
  dsimp [diagonal] at hsq
  by_contra hn
  have hm : d.bound<1 := lt_of_not_ge hn
  have hs : d.bound^2<1 := by nlinarith
  have he := mul_lt_mul_of_pos_right hs d.eigenvalue_pos
  nlinarith [d.eigenvalue_upper]

theorem bound_sq_upper (d : SmallErrorData) : d.bound^2<1002575/1000000 := by
  have htail : d.tail≤(134/100:ℝ)*(63/1000000) :=
    d.tail_upper.trans (mul_le_mul_of_nonneg_left d.triangle_upper (by norm_num))
  have hsq := d.bound_sq_mul
  have herr : (d.bound^2-1)*d.ev=d.mu*d.t+d.tail := by
    dsimp [diagonal,tail] at *
    nlinarith [hsq]
  have hmax : d.mu*d.t+d.tail≤(12/10000:ℝ)+(134/100)*(63/1000000) := by
    linarith [d.mut_upper]
  have he : 0<(2575/1000000:ℝ)*d.ev-((12/10000:ℝ)+(134/100)*(63/1000000)) := by
    nlinarith [d.eigenvalue_lower]
  have hh : (d.bound^2-1)*d.ev<(2575/1000000:ℝ)*d.ev := by linarith
  have hb := (mul_lt_mul_iff_left₀ d.eigenvalue_pos).mp hh
  linarith

theorem bound_upper (d : SmallErrorData) : d.bound<10013/10000 := by
  nlinarith [d.bound_sq_upper,d.bound_one_le]

theorem eta_upper (d : SmallErrorData) : d.eta≤6/10000 := by
  dsimp [eta]; linarith [d.mut_upper]

theorem diagonal_upper (d : SmallErrorData) : d.diagonal≤5012/10000 := by
  dsimp [diagonal]; linarith [d.mean_upper,d.mut_upper]

theorem mu_eta_upper (d : SmallErrorData) : d.mu*d.eta≤115/10000 := by
  dsimp [eta]; nlinarith [d.mu2t_upper]

theorem mu_tail_upper (d : SmallErrorData) : d.mu*d.tail≤1608/1000000 := by
  have hh := mul_le_mul_of_nonneg_left d.tail_upper d.mu_pos.le
  nlinarith [d.mut_upper]

/-- Preserve the leading eigenvalue factor; cancelling it too early weakens the bounds. -/
theorem scaled_bound_defect (d : SmallErrorData) :
    d.ev*d.mu*(d.bound-1)≤12304/1000000 := by
  have hh := mul_nonneg d.eigenvalue_pos.le d.mu_pos.le
  have hs : 2*(d.bound-1)≤d.bound^2-1 := by nlinarith [sq_nonneg (d.bound-1)]
  have hmul := mul_le_mul_of_nonneg_left hs hh
  have he : d.ev*d.mu*(d.bound^2-1)=d.mu^2*d.t+d.mu*d.tail := by
    have hsq := d.bound_sq_mul
    have hsq' := congrArg (fun x : ℝ => d.mu*x) hsq
    dsimp [diagonal,tail] at *
    nlinarith [hsq']
  rw [he] at hmul
  nlinarith [d.mu2t_upper,d.mu_tail_upper]


theorem mean_bounds (d : SmallErrorData) : Bounds d.m (4992/10000) (1/2) :=
  ⟨d.mean_lower,d.mean_upper⟩
theorem eigenvalue_bounds (d : SmallErrorData) : Bounds d.ev (4989/10000) (1/2) :=
  ⟨d.eigenvalue_lower.le,d.eigenvalue_upper.trans d.mean_upper⟩
theorem bound_bounds (d : SmallErrorData) : Bounds d.bound 1 (10013/10000) :=
  ⟨d.bound_one_le,d.bound_upper.le⟩
theorem bound_sq_bounds (d : SmallErrorData) : Bounds (d.bound^2) 1 (1002575/1000000) :=
  ⟨by nlinarith [d.bound_one_le],d.bound_sq_upper.le⟩
theorem eta_bounds (d : SmallErrorData) : Bounds d.eta 0 (6/10000) :=
  ⟨d.eta_nonneg,d.eta_upper⟩
theorem diagonal_bounds (d : SmallErrorData) : Bounds d.diagonal 0 (5012/10000) :=
  ⟨d.diagonal_pos.le,d.diagonal_upper⟩
theorem tail_bounds (d : SmallErrorData) : Bounds d.tail 0 (8442/100000000) :=
  ⟨d.tail_nonneg,by nlinarith [d.tail_upper,d.triangle_upper]⟩
theorem mu_eta_bounds (d : SmallErrorData) : Bounds (d.mu*d.eta) 0 (115/10000) :=
  ⟨mul_nonneg d.mu_pos.le d.eta_nonneg,d.mu_eta_upper⟩
theorem mu_tail_bounds (d : SmallErrorData) : Bounds (d.mu*d.tail) 0 (1608/1000000) :=
  ⟨mul_nonneg d.mu_pos.le d.tail_nonneg,d.mu_tail_upper⟩
theorem scaled_bound_defect_bounds (d : SmallErrorData) :
    Bounds (d.ev*d.mu*(d.bound-1)) 0 (12304/1000000) :=
  ⟨mul_nonneg (mul_nonneg d.eigenvalue_pos.le d.mu_pos.le) (sub_nonneg.mpr d.bound_one_le),
   d.scaled_bound_defect⟩
theorem mean_defect_bounds (d : SmallErrorData) : Bounds (d.mu*(1/2-d.m)) 0 (155/10000) :=
  ⟨mul_nonneg d.mu_pos.le (sub_nonneg.mpr d.mean_upper),d.mean_defect⟩

private theorem sqrt_bounds_of_upper {x u : ℝ} (hx : 0≤x) (hu : 0≤u) (h : x≤u^2) :
    Bounds (Real.sqrt x) 0 u := by
  refine ⟨Real.sqrt_nonneg _,?_⟩
  nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg x]

theorem sqrt_eta_mean_bounds (d : SmallErrorData) :
    Bounds (Real.sqrt (d.eta*d.m/2)) 0 (1225/100000) := by
  apply sqrt_bounds_of_upper (div_nonneg (mul_nonneg d.eta_nonneg d.mean_pos.le) (by norm_num) : 0≤d.eta*d.m/2) (by norm_num)
  have h := d.eta_bounds.mul_nonneg d.mean_bounds (by norm_num) (by norm_num)
  nlinarith [h.2]

theorem sqrt_tail_diagonal_bounds (d : SmallErrorData) :
    Bounds (Real.sqrt (d.tail*d.diagonal)) 0 (66/10000) := by
  apply sqrt_bounds_of_upper (mul_nonneg d.tail_nonneg d.diagonal_pos.le) (by norm_num)
  have h := d.tail_bounds.mul_nonneg d.diagonal_bounds (by norm_num) (by norm_num)
  nlinarith [h.2]

/-- The weighted third codegree error, without an upper bound on the multiplier. -/
theorem weighted_sqrt_codegree_bounds (d : SmallErrorData) :
    Bounds (d.mu*Real.sqrt (d.diagonal*d.tail*d.eta*d.m/2)) 0 (1523/1000000) := by
  have hx : 0≤d.diagonal*d.tail*d.eta*d.m/2 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg d.diagonal_pos.le d.tail_nonneg)
      d.eta_nonneg) d.mean_pos.le) (by norm_num)
  have h := (((d.diagonal_bounds.mul_nonneg d.mu_tail_bounds (by norm_num) (by norm_num)).mul_nonneg
    d.mu_eta_bounds (by norm_num) (by norm_num)).mul_nonneg d.mean_bounds (by norm_num) (by norm_num)).2
  have hs := Real.sq_sqrt hx
  have he : (d.mu*Real.sqrt (d.diagonal*d.tail*d.eta*d.m/2))^2=
      d.diagonal*(d.mu*d.tail)*(d.mu*d.eta)*d.m/2 := by rw [mul_pow,hs]; ring
  have hpos : 0≤d.mu*Real.sqrt (d.diagonal*d.tail*d.eta*d.m/2) :=
    mul_nonneg d.mu_pos.le (Real.sqrt_nonneg _)
  refine ⟨hpos,?_⟩
  nlinarith [he]

theorem mu_bound_defect_bounds (d : SmallErrorData) :
    Bounds (d.mu*(d.bound-1)) 0 ((12304/1000000)/(4989/10000)) := by
  have hpos : 0≤d.mu*(d.bound-1) := mul_nonneg d.mu_pos.le (sub_nonneg.mpr d.bound_one_le)
  have hh := mul_le_mul_of_nonneg_right d.eigenvalue_lower.le hpos
  refine ⟨hpos,?_⟩
  norm_num
  nlinarith [d.scaled_bound_defect]

/-- Weighted product of square roots in the third row-mean error. -/
theorem weighted_sqrt_mean_bounds (d : SmallErrorData) :
    Bounds (d.mu*Real.sqrt (d.tail*d.diagonal)*Real.sqrt (2-2/d.bound)) 0 (6305/1000000) := by
  have hM : 0<d.bound := lt_of_lt_of_le zero_lt_one d.bound_one_le
  have hdiv : 2/d.bound≤2 := (div_le_iff₀ hM).mpr (by nlinarith [d.bound_one_le])
  have harg : 0≤2-2/d.bound := by linarith
  have hargle : 2-2/d.bound≤2*(d.bound-1) := by
    have hcancel : (2/d.bound)*d.bound=2 := div_mul_cancel₀ _ hM.ne'
    have hs := sq_nonneg (d.bound-1)
    apply (mul_le_mul_iff_left₀ hM).mp
    nlinarith
  have hbase : 0≤d.mu^2*d.tail*d.diagonal :=
    mul_nonneg (mul_nonneg (sq_nonneg _) d.tail_nonneg) d.diagonal_pos.le
  have hterm := mul_le_mul_of_nonneg_left hargle hbase
  have hnum := (((d.mu_tail_bounds.mul_nonneg d.diagonal_bounds (by norm_num) (by norm_num)).mul_nonneg
    d.mu_bound_defect_bounds (by norm_num) (by norm_num))).2
  have he : (d.mu*Real.sqrt (d.tail*d.diagonal)*Real.sqrt (2-2/d.bound))^2=
      d.mu^2*d.tail*d.diagonal*(2-2/d.bound) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg d.tail_nonneg d.diagonal_pos.le),Real.sq_sqrt harg]
    ring
  have hpos : 0≤d.mu*Real.sqrt (d.tail*d.diagonal)*Real.sqrt (2-2/d.bound) :=
    mul_nonneg (mul_nonneg d.mu_pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨hpos,?_⟩
  nlinarith [he]

end SmallErrorData
end SparseLowerTail.Section07

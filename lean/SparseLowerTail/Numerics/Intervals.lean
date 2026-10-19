import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Real interval arithmetic whose every bound is proved in Lean's kernel.
No floating-point evaluator or imported certificate status is trusted. -/
noncomputable section
namespace SparseLowerTail.Numerics

/-- A closed enclosure, with rational endpoints usually supplied by generated proofs. -/
def Bounds (x lo hi : ℝ) : Prop := lo ≤ x ∧ x ≤ hi

theorem Bounds.refl (x : ℝ) : Bounds x x x := ⟨le_rfl, le_rfl⟩
theorem Bounds.weaken {x l u l' u' : ℝ} (h : Bounds x l u) (hl : l' ≤ l) (hu : u ≤ u') :
    Bounds x l' u' := ⟨hl.trans h.1, h.2.trans hu⟩
theorem Bounds.add {x l u y v w : ℝ} (hx : Bounds x l u) (hy : Bounds y v w) :
    Bounds (x+y) (l+v) (u+w) := ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩
theorem Bounds.neg {x l u : ℝ} (hx : Bounds x l u) : Bounds (-x) (-u) (-l) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
theorem Bounds.sub {x l u y v w : ℝ} (hx : Bounds x l u) (hy : Bounds y v w) :
    Bounds (x-y) (l-w) (u-v) := ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩
theorem Bounds.mul_nonneg {x l u y v w : ℝ} (hx : Bounds x l u) (hy : Bounds y v w)
    (hl : 0 ≤ l) (hv : 0 ≤ v) : Bounds (x*y) (l*v) (u*w) :=
  ⟨mul_le_mul hx.1 hy.1 hv (hl.trans hx.1),
    mul_le_mul hx.2 hy.2 (hv.trans hy.1) (hl.trans (hx.1.trans hx.2))⟩
theorem Bounds.inv_pos {x l u : ℝ} (hx : Bounds x l u) (hl : 0 < l) :
    Bounds x⁻¹ u⁻¹ l⁻¹ := by
  have hx0 := hl.trans_le hx.1
  exact ⟨inv_anti₀ hx0 hx.2, inv_anti₀ hl hx.1⟩
theorem Bounds.div_pos {x l u y v w : ℝ} (hx : Bounds x l u) (hy : Bounds y v w)
    (hl : 0 ≤ l) (hv : 0 < v) : Bounds (x/y) (l/w) (u/v) := by
  exact hx.mul_nonneg (hy.inv_pos hv) hl (le_of_lt (_root_.inv_pos.mpr (hv.trans_le (hy.1.trans hy.2))))

theorem Bounds.pow {x l u : ℝ} (hx : Bounds x l u) (hl : 0 ≤ l) (n : ℕ) :
    Bounds (x^n) (l^n) (u^n) :=
  ⟨pow_le_pow_left₀ hl hx.1 n, pow_le_pow_left₀ (hl.trans hx.1) hx.2 n⟩

theorem log_two_bounds_22 : Bounds (Real.log 2)
    (6931471805599453094172/10^22) (6931471805599453094173/10^22) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/2 : ℝ)) (by norm_num) 80
  norm_num [Finset.sum_range_succ] at h
  rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  constructor <;> linarith

end SparseLowerTail.Numerics

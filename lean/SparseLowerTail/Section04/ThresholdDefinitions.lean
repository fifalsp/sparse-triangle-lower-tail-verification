import SparseLowerTail.Section04.Crossing
import SparseLowerTail.Numerics.Intervals

/-! Kernel-checked numerical constants for manuscript `lem:digits`.
Generated rational arithmetic is checked with `norm_num`; transcendental
bounds use proved Taylor remainders, never external floating-point assertions. -/
noncomputable section
open SparseLowerTail.Numerics
namespace SparseLowerTail.Section04

def digitZLower : ℝ := 2005543105488 / 10^14
def digitZUpper : ℝ := 2005543105489 / 10^14

/-- D/b after eliminating exp and the entropy products. All factors except the
final subtraction are positive near the crossing, making interval bounds sharp. -/
def normalizedDifference (z : ℝ) : ℝ :=
  ((1+z)/2-kappa z) * (1+2*z*branchLog z/(1-z)^2) + z*branchLog z/2 -
    kappa z * (-Real.log ((z^3+3*z)/4))/3

theorem branchDifference_normalized {z : ℝ} (hz : 0 < z) :
    branchDifference z = branchB z * normalizedDifference z := by
  have hk := kappa_pos hz
  have hb := branchB_pos z
  have hlk : Real.log (kappa z) = Real.log ((z^3+3*z)/4)/3 := by
    rw [← kappa_cube (le_of_lt hz), Real.log_pow]
    norm_num
  unfold branchDifference balancedCost entropy branchRho branchA normalizedDifference
  rw [Real.log_mul (ne_of_gt hk) (ne_of_gt hb),
    Real.log_mul (ne_of_gt hz) (ne_of_gt hb), log_branchB, hlk]
  rw [show Real.log z = -branchLog z by simp]
  ring

end SparseLowerTail.Section04

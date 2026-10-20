import SparseLowerTail.Section07.PenalizedValue
import SparseLowerTail.Numerics.PreciseLogTwo
import SparseLowerTail.Numerics.IntervalArithmetic

/-! Analytic identities and sign-to-root enclosure for the coexistence digits. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04 Numerics

theorem constantRoot_bounds_of_signs {γ l u : ℝ} (hγ : 0<γ) (hl : 0<l)
    (hlo : constantEquation γ l≤0) (hhi : 0≤constantEquation γ u) (hu : 0<u) :
    Bounds (constantRoot γ) l u := by
  have hr := constantRoot_spec hγ
  have hm := constantEquation_strictMono hγ.le
  constructor
  · by_contra hn
    have hh := hm hr.1.1 hl (lt_of_not_ge hn)
    rw [hr.2] at hh
    linarith
  · by_contra hn
    have hh := hm hu hr.1.1 (lt_of_not_ge hn)
    rw [hr.2] at hh
    linarith

theorem constantMinimum_stationary {γ : ℝ} (hγ : 0<γ) :
    constantMinimum γ=1-constantRoot γ-2*γ*(constantRoot γ)^3 := by
  have h := (constantRoot_spec hγ).2
  unfold constantEquation at h
  unfold constantMinimum constantPenalty entropy
  nlinarith [congrArg (fun t : ℝ => constantRoot γ*t) h]

theorem branchPenalty_stationary {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    balancedPenalty (branchMu z/3) (branchA z) (branchB z)=
      1-(branchA z+branchB z)/2-
        2*branchMu z*balancedTriangle (branchA z) (branchB z)/3 := by
  have h := balancedEL_multiplier_cost (branch_balancedEL hz.1 hz.2)
  unfold balancedPenalty
  linear_combination h

theorem penalizedGap_stationary {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    penalizedGap z=constantRoot (branchMu z/3)-(branchA z+branchB z)/2-
      2*branchMu z/3*(balancedTriangle (branchA z) (branchB z)-
        (constantRoot (branchMu z/3))^3) := by
  rw [penalizedGap_eq hz.1,branchPenalty_stationary hz]
  have hγ : 0<branchMu z/3 := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)
  have hc := constantMinimum_stationary hγ
  change constantPenalty (branchMu z/3) (constantRoot (branchMu z/3))=_ at hc
  rw [hc]
  ring

theorem kappa_mono_nonneg {x y : ℝ} (hx : 0≤x) (hxy : x≤y) : kappa x≤kappa y := by
  apply (show Odd (3:ℕ) by decide).strictMono_pow.le_iff_le.mp
  rw [kappa_cube hx,kappa_cube (hx.trans hxy)]
  nlinarith [pow_le_pow_left₀ hx hxy 3]

end SparseLowerTail.Section07

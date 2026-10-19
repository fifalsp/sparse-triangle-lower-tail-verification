import SparseLowerTail.CertificateAlgebra
import SparseLowerTail.Section04.Branch
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Analytic bridge for the certificate tangencies

Stable manuscript anchors: `s8:subs`, `eq:certcoef`, `eq:certpsi`,
`lem:certcoef` (tangency part). Coefficient signs and global certificate
nonnegativity are separate obligations. All results using the rational
coefficient identities explicitly assume `gamma ≠ 0`.
-/
noncomputable section
namespace SparseLowerTail.Certificate
open Section04

/-- The five coefficients in the original, unscaled certificate. -/
def c1 (z : ℝ) := branchB z ^ 2 * d1 z (branchLog z)
def c2 (z : ℝ) := branchB z ^ 2 * d2 z (branchLog z)
def c3 (z : ℝ) := branchB z ^ 3 * d3 z (branchLog z)
def c4 (z : ℝ) := branchB z ^ 2 * d4 z (branchLog z)
def c0 (z : ℝ) := -c1 z * ((branchA z + branchB z)/2) +
  c2 z * branchMu z * balancedTriangle (branchA z) (branchB z) -
  balancedTriangle (branchA z) (branchB z)/3

/-- The unscaled one-variable term S from `eq:certpsi`. -/
def potential (z u : ℝ) := c0 z + c1 z*u + c2 z*u*Real.log u +
  c3 z*Real.log u + c4 z*u*(Real.log u)^2

/-- The original certificate, written with a sum of logarithms. On positive
arguments this agrees with the paper's logarithm of the product. -/
def psi (z x y w : ℝ) := potential z x + potential z y + potential z w +
  branchMu z*c3 z*(x*y+y*w+w*x) +
  x*y*w*(1+branchMu z*c4 z*(Real.log x+Real.log y+Real.log w))

theorem psi_eq_product_log {z x y w : ℝ} (hx : 0 < x) (hy : 0 < y) (hw : 0 < w) :
    psi z x y w = potential z x + potential z y + potential z w +
      branchMu z*c3 z*(x*y+y*w+w*x) +
      x*y*w*(1+branchMu z*c4 z*Real.log (x*y*w)) := by
  rw [Real.log_mul (mul_ne_zero hx.ne' hy.ne') hw.ne', Real.log_mul hx.ne' hy.ne']
  rfl

/-- `s8:subs`, the multiplier substitution. -/
theorem branchMu_scaled (z : ℝ) :
    branchMu z * branchB z ^ 2 = multiplier z (branchLog z) := by
  unfold branchMu multiplier
  have hb : branchB z ≠ 0 := (branchB_pos z).ne'
  field_simp

/-- `s8:subs`, the off-diagonal logarithm. -/
theorem branch_logB (z : ℝ) : Real.log (branchB z) = logB z (branchLog z) := by
  rw [log_branchB]
  unfold logB
  ring

/-- `s8:subs`, the diagonal logarithm. -/
theorem branch_logA {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    Real.log (branchA z) = logA z (branchLog z) := by
  rw [(branch_balancedEL hz hz1).1]
  unfold branchA branchMu logA
  have hb : branchB z ≠ 0 := (branchB_pos z).ne'
  field_simp
  ring

/-- Constant term scaling used when dividing the certificate by b³. -/
theorem c0_scaled (z : ℝ) : c0 z = branchB z^3*d0 z (branchLog z) := by
  unfold c0 c1 c2
  rw [branch_triangle]
  unfold branchA d0 mean density
  have hm := branchMu_scaled z
  rw [← hm]
  ring

/-- S scaling, with its actual logarithm retained. -/
theorem potential_scaled (z u : ℝ) :
    potential z (branchB z*u) = branchB z^3*s z (branchLog z) u
      (Real.log (branchB z*u)) := by
  unfold potential
  rw [c0_scaled]
  unfold c1 c2 c3 c4 s
  ring

/-- The normalized three-variable function, retaining actual logarithms. -/
def normalizedPsi (z u v w : ℝ) :=
  s z (branchLog z) u (Real.log (branchB z*u)) +
  s z (branchLog z) v (Real.log (branchB z*v)) +
  s z (branchLog z) w (Real.log (branchB z*w)) +
  multiplier z (branchLog z)*d3 z (branchLog z)*(u*v+v*w+w*u) +
  u*v*w*(1+multiplier z (branchLog z)*d4 z (branchLog z)*
    (Real.log (branchB z*u)+Real.log (branchB z*v)+Real.log (branchB z*w)))

theorem psi_scaled (z u v w : ℝ) :
    psi z (branchB z*u) (branchB z*v) (branchB z*w) =
      branchB z^3*normalizedPsi z u v w := by
  unfold psi
  rw [potential_scaled, potential_scaled, potential_scaled]
  unfold normalizedPsi c3 c4
  have hm := branchMu_scaled z
  calc
    _ = branchB z^3 * (s z (branchLog z) u (Real.log (branchB z*u)) +
      s z (branchLog z) v (Real.log (branchB z*v)) +
      s z (branchLog z) w (Real.log (branchB z*w)) +
      (branchMu z*branchB z^2)*d3 z (branchLog z)*(u*v+v*w+w*u) +
      u*v*w*(1+(branchMu z*branchB z^2)*d4 z (branchLog z)*
        (Real.log (branchB z*u)+Real.log (branchB z*v)+Real.log (branchB z*w)))) := by ring
    _ = _ := by rw [hm]

/-- `lem:certcoef`, actual value tangency at (a,a,a). -/
theorem psi_aaa {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    psi z (branchA z) (branchA z) (branchA z) = 0 := by
  have hz0 : 1-z ≠ 0 := (sub_pos.mpr hz1).ne'
  have hp : z+1 ≠ 0 := by positivity
  have h := value_aaa z (branchLog z) hz0 hp hg
  have hlog : Real.log (branchB z*z) = logA z (branchLog z) := by
    simpa [branchA, mul_comm] using branch_logA hz hz1
  rw [show branchA z = branchB z*z by unfold branchA; ring, psi_scaled]
  unfold normalizedPsi
  rw [hlog]
  convert congrArg (fun v : ℝ => branchB z^3*v) h using 1 <;> ring

/-- `lem:certcoef`, actual value tangency at (a,b,b). -/
theorem psi_abb {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    psi z (branchA z) (branchB z) (branchB z) = 0 := by
  have hz0 : 1-z ≠ 0 := (sub_pos.mpr hz1).ne'
  have hp : z+1 ≠ 0 := by positivity
  have h := value_abb z (branchLog z) hz0 hp hg
  have hlog : Real.log (branchB z*z) = logA z (branchLog z) := by
    simpa [branchA, mul_comm] using branch_logA hz hz1
  have hscale := psi_scaled z z 1 1
  simp only [mul_one] at hscale
  rw [show branchA z = branchB z*z by unfold branchA; ring, hscale]
  unfold normalizedPsi
  simp only [mul_one, hlog, branch_logB]
  convert congrArg (fun v : ℝ => branchB z^3*v) h using 1 <;> ring

/-- The actual derivative of the one-variable potential. -/
def potentialDerivative (z u : ℝ) := c1 z + c2 z*(1+Real.log u) + c3 z/u +
  c4 z*((Real.log u)^2+2*Real.log u)

theorem hasDerivAt_potential (z : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (potential z) (potentialDerivative z u) u := by
  have hid := hasDerivAt_id u
  have hl := Real.hasDerivAt_log hu
  have hd := ((((hasDerivAt_const u (c0 z)).add (hid.const_mul (c1 z))).add
    ((hid.const_mul (c2 z)).mul hl)).add (hl.const_mul (c3 z))).add
    ((hid.const_mul (c4 z)).mul (hl.pow 2))
  convert hd using 1
  dsimp [potential, potentialDerivative]
  field_simp
  ring

/-- The first partial derivative, kept as an explicit formula for audits. -/
def psiDerivativeX (z x y w : ℝ) := potentialDerivative z x +
  branchMu z*c3 z*(y+w) +
  y*w*(1+branchMu z*c4 z*(1+Real.log x+Real.log y+Real.log w))

theorem hasDerivAt_psi_first (z y w : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u => psi z u y w) (psiDerivativeX z x y w) x := by
  have hid := hasDerivAt_id x
  have hl := Real.hasDerivAt_log hx
  have hp := (((hasDerivAt_potential z hx).add_const (potential z y)).add_const
    (potential z w)).add
    ((((hid.mul_const y).add_const (y*w)).add (hid.const_mul w)).const_mul
      (branchMu z*c3 z))
  have hq := ((hid.mul_const y).mul_const w).mul
    (((hl.add_const (Real.log y)).add_const (Real.log w)).const_mul
      (branchMu z*c4 z) |>.const_add 1)
  convert hp.add hq using 1
  dsimp [psi, psiDerivativeX]
  field_simp
  ring

theorem potentialDerivative_scaled (z : ℝ) {u : ℝ} (hu : u ≠ 0) :
    potentialDerivative z (branchB z*u) = branchB z^2*
      sd z (branchLog z) u (Real.log (branchB z*u)) := by
  unfold potentialDerivative c1 c2 c3 c4 sd
  have hb : branchB z ≠ 0 := (branchB_pos z).ne'
  field_simp

theorem psiDerivativeX_scaled (z v w : ℝ) {u : ℝ} (hu : u ≠ 0) :
    psiDerivativeX z (branchB z*u) (branchB z*v) (branchB z*w) =
      branchB z^2*(sd z (branchLog z) u (Real.log (branchB z*u)) +
        multiplier z (branchLog z)*d3 z (branchLog z)*(v+w) +
        v*w*(1+multiplier z (branchLog z)*d4 z (branchLog z)*
          (1+Real.log (branchB z*u)+Real.log (branchB z*v)+Real.log (branchB z*w)))) := by
  unfold psiDerivativeX
  rw [potentialDerivative_scaled z hu]
  unfold c3 c4
  rw [← branchMu_scaled]
  ring

/-- The actual first partial derivative vanishes at the all-a pattern. -/
theorem psiDerivativeX_aaa {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    psiDerivativeX z (branchA z) (branchA z) (branchA z) = 0 := by
  have hp : z+1 ≠ 0 := by positivity
  have h := gradient_aaa z (branchLog z) hz.ne' (sub_pos.mpr hz1).ne' hp
    (branchLog_pos hz hz1).ne' hg
  have hlog : Real.log (branchB z*z) = logA z (branchLog z) := by
    simpa [branchA, mul_comm] using branch_logA hz hz1
  rw [show branchA z = branchB z*z by unfold branchA; ring,
    psiDerivativeX_scaled z z z hz.ne', hlog]
  convert congrArg (fun v : ℝ => branchB z^2*v) h using 1 <;> ring

/-- The first-coordinate partial derivative vanishes at (a,b,b). -/
theorem psiDerivativeX_abb {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    psiDerivativeX z (branchA z) (branchB z) (branchB z) = 0 := by
  have hp : z+1 ≠ 0 := by positivity
  have h := gradient_abb_a z (branchLog z) hz.ne' (sub_pos.mpr hz1).ne' hp
    (branchLog_pos hz hz1).ne' hg
  have hlog : Real.log (branchB z*z) = logA z (branchLog z) := by
    simpa [branchA, mul_comm] using branch_logA hz hz1
  have hscale := psiDerivativeX_scaled z 1 1 hz.ne'
  simp only [mul_one] at hscale
  rw [show branchA z = branchB z*z by unfold branchA; ring, hscale, hlog, branch_logB]
  convert congrArg (fun v : ℝ => branchB z^2*v) h using 1 <;> ring

/-- The b-coordinate partial derivative, represented by symmetry as (b,a,b). -/
theorem psiDerivativeX_bab {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    psiDerivativeX z (branchB z) (branchA z) (branchB z) = 0 := by
  have hp : z+1 ≠ 0 := by positivity
  have h := gradient_abb_b z (branchLog z) (sub_pos.mpr hz1).ne' hp
    (branchLog_pos hz hz1).ne' hg
  have hlog : Real.log (branchB z*z) = logA z (branchLog z) := by
    simpa [branchA, mul_comm] using branch_logA hz hz1
  have hscale := psiDerivativeX_scaled z z 1 (by norm_num : (1 : ℝ) ≠ 0)
  simp only [mul_one] at hscale
  rw [show branchA z = branchB z*z by unfold branchA; ring, hscale, hlog, branch_logB]
  convert congrArg (fun v : ℝ => branchB z^2*v) h using 1 <;> ring

/-- The derivative theorem, not merely a formal gradient expression. -/
theorem hasDerivAt_psi_aaa_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    HasDerivAt (fun x => psi z x (branchA z) (branchA z)) 0 (branchA z) := by
  simpa only [psiDerivativeX_aaa hz hz1 hg] using
    hasDerivAt_psi_first z (branchA z) (branchA z) (branchA_pos hz).ne'

theorem hasDerivAt_psi_abb_a_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    HasDerivAt (fun x => psi z x (branchB z) (branchB z)) 0 (branchA z) := by
  simpa only [psiDerivativeX_abb hz hz1 hg] using
    hasDerivAt_psi_first z (branchB z) (branchB z) (branchA_pos hz).ne'

theorem hasDerivAt_psi_bab_b_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    HasDerivAt (fun x => psi z x (branchA z) (branchB z)) 0 (branchB z) := by
  simpa only [psiDerivativeX_bab hz hz1 hg] using
    hasDerivAt_psi_first z (branchA z) (branchB z) (branchB_pos z).ne'

theorem psi_swap_xy (z x y w : ℝ) : psi z x y w = psi z y x w := by
  unfold psi
  ring

theorem psi_swap_xw (z x y w : ℝ) : psi z x y w = psi z w y x := by
  unfold psi
  ring

theorem psiDerivativeX_swap_yw (z x y w : ℝ) :
    psiDerivativeX z x y w = psiDerivativeX z x w y := by
  unfold psiDerivativeX
  ring

theorem hasDerivAt_psi_second (z x w : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun u => psi z x u w) (psiDerivativeX z y x w) y := by
  convert hasDerivAt_psi_first z x w hy using 1
  funext u
  exact psi_swap_xy z x u w

theorem hasDerivAt_psi_third (z x y : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (fun u => psi z x y u) (psiDerivativeX z w y x) w := by
  convert hasDerivAt_psi_first z y x hw using 1
  funext u
  exact psi_swap_xw z x y u

/-- All three actual partial derivatives vanish at the all-a contact point. -/
theorem psi_aaa_partial_tangencies {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    HasDerivAt (fun x => psi z x (branchA z) (branchA z)) 0 (branchA z) ∧
    HasDerivAt (fun y => psi z (branchA z) y (branchA z)) 0 (branchA z) ∧
    HasDerivAt (fun w => psi z (branchA z) (branchA z) w) 0 (branchA z) := by
  refine ⟨hasDerivAt_psi_aaa_zero hz hz1 hg, ?_, ?_⟩
  · simpa only [psiDerivativeX_aaa hz hz1 hg] using
      hasDerivAt_psi_second z (branchA z) (branchA z) (branchA_pos hz).ne'
  · simpa only [psiDerivativeX_aaa hz hz1 hg] using
      hasDerivAt_psi_third z (branchA z) (branchA z) (branchA_pos hz).ne'

/-- All three actual partial derivatives vanish at the mixed contact point. -/
theorem psi_abb_partial_tangencies {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    HasDerivAt (fun x => psi z x (branchB z) (branchB z)) 0 (branchA z) ∧
    HasDerivAt (fun y => psi z (branchA z) y (branchB z)) 0 (branchB z) ∧
    HasDerivAt (fun w => psi z (branchA z) (branchB z) w) 0 (branchB z) := by
  refine ⟨hasDerivAt_psi_abb_a_zero hz hz1 hg, ?_, ?_⟩
  · simpa only [psiDerivativeX_bab hz hz1 hg] using
      hasDerivAt_psi_second z (branchA z) (branchB z) (branchB_pos z).ne'
  · have h := hasDerivAt_psi_third z (branchA z) (branchB z) (branchB_pos z).ne'
    rw [psiDerivativeX_swap_yw, psiDerivativeX_bab hz hz1 hg] at h
    exact h

/-- Value tangency at all mixed contact points, by symmetry. -/
theorem psi_mixed_value_tangencies {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (hg : gamma z (branchLog z) ≠ 0) :
    psi z (branchA z) (branchB z) (branchB z) = 0 ∧
    psi z (branchB z) (branchA z) (branchB z) = 0 ∧
    psi z (branchB z) (branchB z) (branchA z) = 0 := by
  refine ⟨psi_abb hz hz1 hg, ?_, ?_⟩
  · rw [psi_swap_xy]
    exact psi_abb hz hz1 hg
  · rw [psi_swap_xw]
    exact psi_abb hz hz1 hg

end SparseLowerTail.Certificate

import Mathlib.Tactic

/-!
# Exact normalized tangency algebra (`lem:certcoef`)

`L` and `z` are independent real variables here. These are the five rational
identities checked by `verification/family/symbolic.py`. The analytic bridge
`L = log (1/z)`, the coefficient signs, and global nonnegativity are not assumed
or proved by this file. All denominators used below are explicitly nonzero.
-/
noncomputable section
namespace SparseLowerTail.Certificate

def gamma (z L : ℝ) : ℝ :=
  6*L^2*z^2 + 3*L*z^3 - L*z^2 - L*z - L - z^3 + 3*z^2 - 3*z + 1

def d1 (z L : ℝ) : ℝ := z*(z-1)*(z+1)*(L+z-1)*(2*L+z-1)/(2*gamma z L)
def d2 (z L : ℝ) : ℝ := z*(z-1)^2*(2*L*z+z^2-1)/(2*gamma z L)
def d3 (z L : ℝ) : ℝ := -z*(z-1)^3*(3*L*z+L+2*z^2-2)/(2*(z+1)*gamma z L)
def d4 (z L : ℝ) : ℝ := (z-1)^4*(2*L*z+z^2-1)/(2*L*(z+1)*gamma z L)
def multiplier (z L : ℝ) : ℝ := 2*L/(1-z)^2
def logA (z L : ℝ) : ℝ := -L*(1+z^2)/(1-z)^2
def logB (z L : ℝ) : ℝ := -2*L*z/(1-z)^2
def mean (z : ℝ) : ℝ := (1+z)/2
def density (z : ℝ) : ℝ := (z^3+3*z)/4
def d0 (z L : ℝ) : ℝ := -d1 z L * mean z + d2 z L * multiplier z L * density z - density z/3
def s (z L u ell : ℝ) : ℝ :=
  d0 z L + d1 z L*u + d2 z L*u*ell + d3 z L*ell + d4 z L*u*ell^2
/-- Formal expression for the normalized derivative after the logarithms have
been substituted. This definition alone is not a derivative theorem. -/
def sd (z L u ell : ℝ) : ℝ :=
  d1 z L + d2 z L*(1+ell) + d3 z L/u + d4 z L*(ell^2+2*ell)

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- Value at the all-a pattern, after division by b³. -/
theorem value_aaa (z L : ℝ) (hz : 1-z ≠ 0) (hp : z+1 ≠ 0)
    (hg : gamma z L ≠ 0) :
    3*s z L z (logA z L) + 3*multiplier z L*d3 z L*z^2 +
      z^3*(1+3*multiplier z L*d4 z L*logA z L) = 0 := by
  unfold s d0 d1 d2 d3 d4 mean density multiplier logA
  field_simp [hz, hp, hg]
  unfold gamma
  ring

/-- Derivative expression at the all-a pattern, after division by b². -/
theorem gradient_aaa (z L : ℝ) (h0 : z ≠ 0) (hz : 1-z ≠ 0)
    (hp : z+1 ≠ 0) (hL : L ≠ 0) (hg : gamma z L ≠ 0) :
    sd z L z (logA z L) + 2*multiplier z L*d3 z L*z +
      z^2*(1+multiplier z L*d4 z L+3*multiplier z L*d4 z L*logA z L) = 0 := by
  unfold sd d1 d2 d3 d4 multiplier logA
  field_simp [h0, hz, hp, hL, hg]
  unfold gamma
  ring

/-- Value at the a,b,b pattern, after division by b³. -/
theorem value_abb (z L : ℝ) (hz : 1-z ≠ 0) (hp : z+1 ≠ 0)
    (hg : gamma z L ≠ 0) :
    s z L z (logA z L) + 2*s z L 1 (logB z L) +
      multiplier z L*d3 z L*(2*z+1) +
      z*(1+multiplier z L*d4 z L*(logA z L+2*logB z L)) = 0 := by
  unfold s d0 d1 d2 d3 d4 mean density multiplier logA logB
  field_simp [hz, hp, hg]
  unfold gamma
  ring

/-- Derivative expression in the a coordinate at a,b,b. -/
theorem gradient_abb_a (z L : ℝ) (h0 : z ≠ 0) (hz : 1-z ≠ 0)
    (hp : z+1 ≠ 0) (hL : L ≠ 0) (hg : gamma z L ≠ 0) :
    sd z L z (logA z L) + 2*multiplier z L*d3 z L +
      1+multiplier z L*d4 z L*(1+logA z L+2*logB z L) = 0 := by
  unfold sd d1 d2 d3 d4 multiplier logA logB
  field_simp [h0, hz, hp, hL, hg]
  unfold gamma
  ring

/-- Derivative expression in either b coordinate at a,b,b. -/
theorem gradient_abb_b (z L : ℝ) (hz : 1-z ≠ 0) (hp : z+1 ≠ 0)
    (hL : L ≠ 0) (hg : gamma z L ≠ 0) :
    sd z L 1 (logB z L) + multiplier z L*d3 z L*(z+1) +
      z*(1+multiplier z L*d4 z L*(1+logA z L+2*logB z L)) = 0 := by
  unfold sd d1 d2 d3 d4 multiplier logA logB
  field_simp [hz, hp, hL, hg]
  unfold gamma
  ring

end SparseLowerTail.Certificate

import SparseLowerTail.Section03.StepMatrixCut
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The numerical codegree, sparse-threshold and energy bookkeeping in lem:decorrelation.
The external hypergraph energy-selection theorem is not assumed or restated here. -/
noncomputable section
namespace SparseLowerTail.Section03

def triangleVertexCount (n : ℕ) : ℝ := n.choose 2
def triangleEdgeCount (n : ℕ) : ℝ := n.choose 3

theorem triangleVertexCount_formula (n : ℕ) :
    triangleVertexCount n=(n:ℝ)*((n:ℝ)-1)/2 := Nat.cast_choose_two ℝ n

theorem triangle_counts_relation (n : ℕ) (hn : 2≤n) :
    3*triangleEdgeCount n=triangleVertexCount n*((n:ℝ)-2) := by
  have hh := congrArg (fun k : ℕ => (k:ℝ)) (Nat.choose_succ_right_eq n 2)
  norm_num only [Nat.cast_mul,Nat.cast_sub hn,Nat.cast_ofNat] at hh
  change 3*(n.choose 3:ℝ)=(n.choose 2:ℝ)*((n:ℝ)-2)
  nlinarith

theorem triangleVertexCount_pos (n : ℕ) (hn : 2≤n) : 0<triangleVertexCount n := by
  rw [triangleVertexCount_formula]
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  exact div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)

theorem triangle_edge_vertex_ratio (n : ℕ) (hn : 2≤n) :
    triangleEdgeCount n/triangleVertexCount n=((n:ℝ)-2)/3 := by
  apply (div_eq_iff (triangleVertexCount_pos n hn).ne').mpr
  have hh := triangle_counts_relation n hn
  linarith

/-- A concrete vertex threshold suffices for any prescribed hypergraph size threshold. -/
theorem triangle_vertex_budget (V n : ℕ) (hn : V+2≤n) : (V:ℝ)≤triangleVertexCount n := by
  rw [triangleVertexCount_formula]
  have hn' : (V:ℝ)+2≤n := by exact_mod_cast hn
  have hv : (0:ℝ)≤V := Nat.cast_nonneg V
  have hprod : 0≤((n:ℝ)-2)*((n:ℝ)-1) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Given the triangle hypergraph's codegrees, these are exactly its three numerical conditions. -/
theorem triangle_numeric_codegree_bounds (n : ℕ) (hn : 4≤n) {ell p : ℝ}
    (hellp : 0≤ell*p) (hfirst : 2≤ell*p*(n:ℝ)) (hsecond : 2≤(ell*p)^2*(n:ℝ)) :
    (n:ℝ)-2≤3*triangleEdgeCount n/triangleVertexCount n ∧
      1≤3*(ell*p)*triangleEdgeCount n/triangleVertexCount n ∧
      1≤3*(ell*p)^2*triangleEdgeCount n/triangleVertexCount n := by
  have hratio := triangle_edge_vertex_ratio n (by omega)
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have hlinear : 1≤(ell*p)*((n:ℝ)-2) := by
    have hh := mul_nonneg hellp (show 0≤(n:ℝ)-4 by linarith)
    nlinarith
  have hquadratic : 1≤(ell*p)^2*((n:ℝ)-2) := by
    have hh := mul_nonneg (sq_nonneg (ell*p)) (show 0≤(n:ℝ)-4 by linarith)
    nlinarith
  constructor
  · rw [mul_div_assoc,hratio]; nlinarith
  constructor
  · rw [mul_div_assoc,hratio]; nlinarith
  · rw [mul_div_assoc,hratio]; nlinarith

/-- The lower bound p >= 2/(lambda sqrt(n)) implies both sparse codegree requirements. -/
theorem sparse_threshold_requirements (n : ℕ) (hn : 4≤n) {ell p : ℝ}
    (hell : 0<ell) (hp : (2/ell)/Real.sqrt n≤p) :
    0≤ell*p ∧ 2≤ell*p*(n:ℝ) ∧ 2≤(ell*p)^2*(n:ℝ) := by
  have hn' : (4:ℝ)≤n := by exact_mod_cast hn
  have hroot : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hs := Real.sq_sqrt (show (0:ℝ)≤n by positivity)
  have hp' : 0<p := lt_of_lt_of_le (div_pos (div_pos (by norm_num) hell) hroot) hp
  have hellp : 0≤ell*p := (mul_pos hell hp').le
  have hh := (div_le_iff₀ hroot).mp hp
  have hh' := (div_le_iff₀ hell).mp hh
  have htwo : 2≤ell*p*Real.sqrt n := by nlinarith [hh']
  have hroot1 : 1≤Real.sqrt (n:ℝ) := by nlinarith [hroot.le]
  have hlinear : 2≤ell*p*(n:ℝ) := by
    have he : ell*p*(n:ℝ)=(ell*p*Real.sqrt n)*Real.sqrt n := by nlinarith [hs]
    rw [he]
    exact htwo.trans (le_mul_of_one_le_right (by linarith : 0≤ell*p*Real.sqrt n) hroot1)
  have hsquare : 4≤(ell*p*Real.sqrt n)^2 := by nlinarith
  rw [mul_pow,Real.sq_sqrt (show (0:ℝ)≤n by positivity)] at hsquare
  exact ⟨hellp,hlinear,by linarith⟩

/-- The energy estimate's square roots give exactly beta times the triangle count. -/
theorem decorrelation_sqrt_energy {β e E : ℝ} (hβ : 0≤β) (he : 0≤e) (hE : 0≤E)
    (hbudget : E≤β^2*e/2) : Real.sqrt (2*e)*Real.sqrt E≤β*e := by
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg hβ he)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hE]
  nlinarith [mul_le_mul_of_nonneg_left hbudget (show 0≤2*e by positivity)]

theorem decorrelation_error_of_energy {β e E p D : ℝ} (hβ : 0≤β) (he : 0≤e)
    (hE : 0≤E) (hp : 0≤p) (hbudget : E≤β^2*e/2)
    (hcs : D≤p^3*(Real.sqrt (2*e)*Real.sqrt E)) : D≤β*p^3*e := by
  have hh := mul_le_mul_of_nonneg_left (decorrelation_sqrt_energy hβ he hE hbudget)
    (pow_nonneg hp 3)
  nlinarith

/-- One threshold handles hypergraph size, all numerical codegrees and n >= 4. -/
theorem exists_decorrelation_threshold {ell : ℝ} (hell : 0<ell) (V : ℕ) :
    ∃ L : ℝ, 4≤L ∧ ∀ n : ℕ, L≤(n:ℝ) → ∀ p : ℝ, L/Real.sqrt n≤p →
      (V:ℝ)≤triangleVertexCount n ∧
      (n:ℝ)-2≤3*triangleEdgeCount n/triangleVertexCount n ∧
      1≤3*(ell*p)*triangleEdgeCount n/triangleVertexCount n ∧
      1≤3*(ell*p)^2*triangleEdgeCount n/triangleVertexCount n := by
  let L := max 4 (max (2/ell) ((V:ℝ)+2))
  refine ⟨L,le_max_left _ _,?_⟩
  intro n hn p hp
  have hn4 : 4≤n := by exact_mod_cast ((le_max_left _ _).trans hn : (4:ℝ)≤n)
  have hnV : V+2≤n := by
    exact_mod_cast ((le_max_right (2/ell) ((V:ℝ)+2)).trans ((le_max_right 4 _).trans hn))
  have hL : 2/ell≤L := (le_max_left _ _).trans (le_max_right _ _)
  have hs := sparse_threshold_requirements n hn4 hell
    ((div_le_div_of_nonneg_right hL (Real.sqrt_nonneg _)).trans hp)
  exact ⟨triangle_vertex_budget V n hnV,triangle_numeric_codegree_bounds n hn4 hs.1 hs.2.1 hs.2.2⟩

/-- The square-root form is the manuscript's negative one-half power. -/
theorem sparse_half_power_identity (n : ℕ) (L : ℝ) :
    L*(n:ℝ)^(-(1/(2:ℝ)))=L/Real.sqrt n := by
  rw [Real.rpow_neg (Nat.cast_nonneg n),← Real.sqrt_eq_rpow,div_eq_mul_inv]

end SparseLowerTail.Section03

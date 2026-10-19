import SparseLowerTail.Section04.EntropyGeometry

/-!
# Algebra behind bipodal rigidity

Paper anchors: `s4:eq:bipsys`, `s4:eq:J`, and `prop:bipodal`.
The strictly positive J lemma is a separate internal obligation; it is not
classified as an external result. This module proves the elimination from the
stationary equations and vertex identity to J = 0.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section04

def vertexEntropy (u : ℝ) : ℝ := u*Real.log u-2*u+2

structure BipodalStationary (c μ a d b : ℝ) : Prop where
  first : Real.log a = -μ*(c*a^2+(1-c)*b^2)
  second : Real.log d = -μ*(c*b^2+(1-c)*d^2)
  cross : Real.log b = -μ*b*(c*a+(1-c)*d)
  vertex : c*vertexEntropy a+(1-c)*vertexEntropy b =
    c*vertexEntropy b+(1-c)*vertexEntropy d

/-- The explicit function whose positivity rules out unequal diagonal values. -/
def bipodalJ (x y : ℝ) : ℝ :=
  (1-y)*y*(1+x)*(-Real.log x)^2-(1-x)*x*(1+y)*(-Real.log y)^2-
    2*(y-x)*(-Real.log x)*(-Real.log y)+
    2*(1-x)*(1-y)*((1-y)*(-Real.log x)-(1-x)*(-Real.log y))

theorem BipodalStationary.swap {c μ a d b : ℝ} (h : BipodalStationary c μ a d b) :
    BipodalStationary (1-c) μ d a b := by
  constructor
  · convert h.second using 1; ring
  · convert h.first using 1; ring
  · convert h.cross using 1; ring
  · linear_combination -h.vertex

/-- Under a≤d, the logarithmic equations force both diagonal values below b
unless the model is constant. This uses no vertex equation or J inequality. -/
theorem BipodalStationary.ordered {c μ a d b : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hμ : 0 < μ) (ha : 0 < a) (hd : 0 < d) (hb : 0 < b)
    (had : a ≤ d) (hne : ¬(a = b ∧ d = b)) (h : BipodalStationary c μ a d b) :
    a < b ∧ d < b := by
  have hc1 : 0 < 1-c := sub_pos.mpr hc.2
  have hs : Real.log a+Real.log d-2*Real.log b =
      -μ*(c*(a-b)^2+(1-c)*(d-b)^2) := by
    linear_combination h.first+h.second-2*h.cross
  have hab : a < b := by
    by_contra hn
    have hba : b ≤ a := le_of_not_gt hn
    have hbd : b ≤ d := hba.trans had
    have hla : Real.log b ≤ Real.log a := Real.strictMonoOn_log.monotoneOn hb ha hba
    have hld : Real.log b ≤ Real.log d := Real.strictMonoOn_log.monotoneOn hb hd hbd
    have hq1 : 0 ≤ c*(a-b)^2 := mul_nonneg hc.1.le (sq_nonneg _)
    have hq2 : 0 ≤ (1-c)*(d-b)^2 := mul_nonneg hc1.le (sq_nonneg _)
    have hq : c*(a-b)^2+(1-c)*(d-b)^2 = 0 := by nlinarith
    have hab0 : (a-b)^2 = 0 :=
      (mul_eq_zero.mp (show c*(a-b)^2=0 by linarith)).resolve_left (ne_of_gt hc.1)
    have hdb0 : (d-b)^2 = 0 :=
      (mul_eq_zero.mp (show (1-c)*(d-b)^2=0 by linarith)).resolve_left (ne_of_gt hc1)
    exact hne ⟨by nlinarith [sq_nonneg (a-b)],by nlinarith [sq_nonneg (d-b)]⟩
  have hdb : d < b := by
    by_contra hn
    have hbd : b ≤ d := le_of_not_gt hn
    have hld : Real.log b ≤ Real.log d := Real.strictMonoOn_log.monotoneOn hb hd hbd
    have he : Real.log d-Real.log b =
        -μ*(c*b*(b-a)+(1-c)*d*(d-b)) := by
      linear_combination h.second-h.cross
    have hp : 0 < c*b*(b-a) := mul_pos (mul_pos hc.1 hb) (sub_pos.mpr hab)
    have hn : 0 ≤ (1-c)*d*(d-b) :=
      mul_nonneg (mul_pos hc1 hd).le (sub_nonneg.mpr hbd)
    nlinarith
  exact ⟨hab,hdb⟩

/-- Exact polynomial elimination of the normalized first-order system.
No logarithm or positivity result is used in this algebraic step. -/
theorem normalized_bipodal_elimination (c lam σ x y ξ ζ : ℝ)
    (hS : 1-x*y ≠ 0)
    (h1 : ξ = lam*((1-c)*(1-y)-x*c*(1-x)))
    (h2 : ζ = lam*(c*(1-x)-y*(1-c)*(1-y)))
    (h3 : σ = lam*(c*x+(1-c)*y))
    (hv : (2+σ)*((1-c)*(1-y)-c*(1-x))+c*x*ξ-(1-c)*y*ζ = 0) :
    (1-y)*y*(1+x)*ξ^2-(1-x)*x*(1+y)*ζ^2-2*(y-x)*ξ*ζ+
      2*(1-x)*(1-y)*((1-y)*ξ-(1-x)*ζ) = 0 := by
  have ht1 : lam*(1-x*y)*c*(1-x) = ζ+y*ξ := by
    linear_combination -y*h1-h2
  have ht2 : lam*(1-x*y)*(1-c)*(1-y) = ξ+x*ζ := by
    linear_combination -h1-x*h2
  have hσ : (1-x)*(1-y)*σ = y*ξ+x*ζ := by
    apply mul_left_cancel₀ hS
    linear_combination (1-x*y)*(1-x)*(1-y)*h3+
      x*(1-y)*ht1+y*(1-x)*ht2
  have hV : (1-x)*(1-y)*(2+σ)*((1-y)*ξ-(1-x)*ζ)+
      (1-y)*x*ξ*(ζ+y*ξ)-(1-x)*y*ζ*(ξ+x*ζ) = 0 := by
    linear_combination (1-x)*(1-y)*lam*(1-x*y)*hv-
      ((1-x)*(1-y)*(2+σ)-(1-x)*y*ζ)*ht2+
      ((1-x)*(1-y)*(2+σ)-(1-y)*x*ξ)*ht1
  linear_combination hV-((1-y)*ξ-(1-x)*ζ)*hσ

/-- The actual logarithmic stationary system reduces to the polynomial system
above after setting a=bx, d=by, lam=μb² and σ=-log b. -/
theorem BipodalStationary.J_zero {c μ b x y : ℝ} (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hS : 1-x*y ≠ 0)
    (h : BipodalStationary c μ (b*x) (b*y) b) : bipodalJ x y = 0 := by
  have hlogx : Real.log (b*x) = Real.log b+Real.log x :=
    Real.log_mul (ne_of_gt hb) (ne_of_gt hx)
  have hlogy : Real.log (b*y) = Real.log b+Real.log y :=
    Real.log_mul (ne_of_gt hb) (ne_of_gt hy)
  have h1 : -Real.log x = (μ*b^2)*((1-c)*(1-y)-x*c*(1-x)) := by
    linear_combination -h.first+h.cross+hlogx
  have h2 : -Real.log y = (μ*b^2)*(c*(1-x)-y*(1-c)*(1-y)) := by
    linear_combination -h.second+h.cross+hlogy
  have h3 : -Real.log b = (μ*b^2)*(c*x+(1-c)*y) := by
    linear_combination -h.cross
  have hv : (2-Real.log b)*((1-c)*(1-y)-c*(1-x))+
      c*x*(-Real.log x)-(1-c)*y*(-Real.log y) = 0 := by
    apply mul_left_cancel₀ (ne_of_gt hb)
    have hv := h.vertex
    unfold vertexEntropy at hv
    rw [hlogx,hlogy] at hv
    linear_combination -hv
  exact normalized_bipodal_elimination c (μ*b^2) (-Real.log b) x y
    (-Real.log x) (-Real.log y) hS h1 h2 h3 (by convert hv using 1)

/-- Conditional only on the separate internal positivity lemma `lem:J`.
This is the full algebraic reduction of `prop:bipodal`, not a proof of lem:J. -/
theorem bipodal_rigidity_of_J
    (hJ : ∀ x y : ℝ, 0 < x → x < y → y < 1 → 0 < bipodalJ x y)
    {c μ a d b : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hμ : 0 < μ)
    (ha : 0 < a) (hd : 0 < d) (hb : 0 < b)
    (hne : ¬(a = b ∧ d = b)) (h : BipodalStationary c μ a d b) :
    a = d ∧ a < b ∧ c = 1/2 := by
  have heq_ordered : ∀ {c a d : ℝ}, c ∈ Ioo (0 : ℝ) 1 → 0 < a → 0 < d →
      a ≤ d → ¬(a=b ∧ d=b) → BipodalStationary c μ a d b → a=d := by
    intro c a d hc ha hd had hne h
    have hord := h.ordered hc hμ ha hd hb had hne
    by_contra hneq
    have had' : a < d := lt_of_le_of_ne had hneq
    have hx : 0 < a/b := div_pos ha hb
    have hxy : a/b < d/b := (div_lt_div_iff_of_pos_right hb).mpr had'
    have hy1 : d/b < 1 := (div_lt_one hb).mpr hord.2
    have hy : 0 < d/b := div_pos hd hb
    have hx1 : a/b < 1 := hxy.trans hy1
    have hS : 1-(a/b)*(d/b) ≠ 0 := ne_of_gt (by nlinarith [mul_lt_mul_of_pos_left hy1 hx])
    have hs : BipodalStationary c μ (b*(a/b)) (b*(d/b)) b := by
      simpa [mul_div_cancel₀ _ (ne_of_gt hb)] using h
    have hzero := hs.J_zero hb hx hy hS
    exact (hJ (a/b) (d/b) hx hxy hy1).ne' hzero
  have had : a=d := by
    rcases le_total a d with had | hda
    · exact heq_ordered hc ha hd had hne h
    · have hc' : 1-c ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hc.1,hc.2]
      exact (heq_ordered hc' hd ha hda (fun he => hne ⟨he.2,he.1⟩) h.swap).symm
  have hab := (h.ordered hc hμ ha hd hb had.le hne).1
  have hfactor : μ*(2*c-1)*(a^2-b^2)=0 := by
    have hsecond := h.second
    rw [← had] at hsecond
    linear_combination h.first-hsecond
  have hsq : a^2-b^2 ≠ 0 := ne_of_lt (by nlinarith)
  have hmu : μ*(2*c-1)=0 := (mul_eq_zero.mp hfactor).resolve_right hsq
  have hc0 : 2*c-1=0 := (mul_eq_zero.mp hmu).resolve_left (ne_of_gt hμ)
  exact ⟨had,hab,by linarith⟩

end SparseLowerTail.Section04

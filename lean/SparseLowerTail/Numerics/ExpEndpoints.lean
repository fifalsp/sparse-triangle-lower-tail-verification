import SparseLowerTail.Numerics.IntervalArithmetic

/-! Rational endpoint certificates for exp(-q), 0 ≤ q ≤ 16.
The Taylor arithmetic is performed in ℚ and then transported to ℝ by the
proved cast identities. Every rounding comparison remains a kernel-checked
hypothesis; this module introduces no numerical oracle. -/
namespace SparseLowerTail.Numerics

/-- Exact rational Taylor polynomial. -/
def expTaylorRat (x : ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range n, x^m / (m.factorial : ℚ)

/-- The remainder bound used by `Real.exp_bound`. -/
def expRemainderRat (x : ℚ) (n : ℕ) : ℚ :=
  |x|^n * ((n+1 : ℕ) / ((n.factorial : ℚ)*n))

theorem expTaylorRat_cast (x : ℚ) (n : ℕ) :
    (expTaylorRat x n : ℝ) = ∑ m ∈ Finset.range n, (x : ℝ)^m/(m.factorial : ℝ) := by
  simp [expTaylorRat]

theorem expRemainderRat_cast (x : ℚ) (n : ℕ) :
    (expRemainderRat x n : ℝ) = |(x : ℝ)|^n*((n+1 : ℕ)/(n.factorial*n) : ℝ) := by
  simp [expRemainderRat]

/-- A rational Taylor check implies the corresponding real exp enclosure. -/
theorem exp_bounds_of_rat_taylor {x l u : ℚ} {n : ℕ}
    (hx : |x| ≤ 1) (hn : 0<n)
    (hl : l ≤ expTaylorRat x n - expRemainderRat x n)
    (hu : expTaylorRat x n + expRemainderRat x n ≤ u) :
    Bounds (Real.exp (x : ℝ)) (l : ℝ) (u : ℝ) := by
  have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have h := exp_taylor_bounds hx' hn
  rw [←expTaylorRat_cast, ←expRemainderRat_cast] at h
  have hl' : (l : ℝ) ≤ (expTaylorRat x n : ℝ) - (expRemainderRat x n : ℝ) := by
    exact_mod_cast hl
  have hu' : (expTaylorRat x n : ℝ) + (expRemainderRat x n : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hu
  exact ⟨hl'.trans h.1,h.2.trans hu'⟩

/-- Range reduction, rational rounding and power sixteen certify a full endpoint. -/
theorem exp_neg_bounds_of_rat_taylor {q l u L U : ℚ} {n : ℕ}
    (hq0 : 0≤q) (hq16 : q≤16) (hn : 0<n) (hl0 : 0≤l)
    (hl : l ≤ expTaylorRat (-q/16) n - expRemainderRat (-q/16) n)
    (hu : expTaylorRat (-q/16) n + expRemainderRat (-q/16) n ≤ u)
    (hL : L≤l^16) (hU : u^16≤U) :
    Bounds (Real.exp (-(q : ℝ))) (L : ℝ) (U : ℝ) := by
  have hx : |(-q/16 : ℚ)|≤1 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have h := (exp_bounds_of_rat_taylor hx hn hl hu).exp_scale_pow
    (by exact_mod_cast hl0) 16
  have heq : (16 : ℝ)*((-q/16 : ℚ) : ℝ) = -(q : ℝ) := by push_cast; ring
  norm_num only [Nat.cast_ofNat] at h
  rw [heq] at h
  exact ⟨(by exact_mod_cast hL : (L : ℝ)≤(l : ℝ)^16).trans h.1,
    h.2.trans (by exact_mod_cast hU : (u : ℝ)^16≤(U : ℝ))⟩

/-- Two endpoint enclosures certify exp(-x) throughout a logarithmic interval. -/
theorem exp_neg_bounds_on_interval {x a b L U : ℝ}
    (hx : Bounds x a b) (ha : Real.exp (-a)≤U) (hb : L≤Real.exp (-b)) :
    Bounds (Real.exp (-x)) L U :=
  ⟨hb.trans (Real.exp_le_exp.mpr (neg_le_neg hx.2)),
   (Real.exp_le_exp.mpr (neg_le_neg hx.1)).trans ha⟩

/-- Compact numerical data for one endpoint; `Valid` is checked separately. -/
structure ExpEndpointCertificate where
  q : ℚ
  order : ℕ
  baseLower : ℚ
  baseUpper : ℚ
  lower : ℚ
  upper : ℚ
  deriving Repr

namespace ExpEndpointCertificate

def Valid (c : ExpEndpointCertificate) : Prop :=
  0≤c.q ∧ c.q≤16 ∧ 0<c.order ∧ 0≤c.baseLower ∧
  c.baseLower≤expTaylorRat (-c.q/16) c.order-expRemainderRat (-c.q/16) c.order ∧
  expTaylorRat (-c.q/16) c.order+expRemainderRat (-c.q/16) c.order≤c.baseUpper ∧
  c.lower≤c.baseLower^16 ∧ c.baseUpper^16≤c.upper

instance (c : ExpEndpointCertificate) : Decidable c.Valid := inferInstanceAs (Decidable (
  0≤c.q ∧ c.q≤16 ∧ 0<c.order ∧ 0≤c.baseLower ∧
  c.baseLower≤expTaylorRat (-c.q/16) c.order-expRemainderRat (-c.q/16) c.order ∧
  expTaylorRat (-c.q/16) c.order+expRemainderRat (-c.q/16) c.order≤c.baseUpper ∧
  c.lower≤c.baseLower^16 ∧ c.baseUpper^16≤c.upper))

theorem bounds (c : ExpEndpointCertificate) (h : c.Valid) :
    Bounds (Real.exp (-(c.q : ℝ))) (c.lower : ℝ) (c.upper : ℝ) := by
  rcases h with ⟨h0,h16,hn,hl0,hl,hu,hL,hU⟩
  exact exp_neg_bounds_of_rat_taylor h0 h16 hn hl0 hl hu hL hU

end ExpEndpointCertificate

end SparseLowerTail.Numerics

import SparseLowerTail.Numerics.IntervalExpr

/-! Fixed-precision interval arithmetic. Every endpoint is an integer multiple
of 2⁻⁶⁰. Multiplication and rational constants round outwards using integer
Euclidean division. All soundness statements are proved over the reals. -/
namespace SparseLowerTail.Numerics

structure DyadicInterval where
  lower : ℤ
  upper : ℤ
  deriving DecidableEq, Repr

namespace DyadicInterval

def scale : ℤ := 2^60

theorem scale_pos : (0:ℤ)<scale := by norm_num [scale]
theorem scale_real_pos : (0:ℝ)<(scale:ℝ) := by exact_mod_cast scale_pos

def contains (I : DyadicInterval) (x : ℝ) : Prop :=
  Bounds x ((I.lower:ℝ)/scale) ((I.upper:ℝ)/scale)

def ceilDiv (a b : ℤ) : ℤ := -((-a)/b)

theorem floorDiv_le (a b : ℤ) (hb : 0<b) :
    ((a/b:ℤ):ℝ)≤(a:ℝ)/(b:ℝ) := by
  apply (le_div_iff₀ (show (0:ℝ)<b by exact_mod_cast hb)).mpr
  exact_mod_cast Int.ediv_mul_le a hb.ne'

theorem le_ceilDiv (a b : ℤ) (hb : 0<b) :
    (a:ℝ)/(b:ℝ)≤(ceilDiv a b:ℝ) := by
  have h := floorDiv_le (-a) b hb
  simp only [Int.cast_neg,neg_div] at h
  simp only [ceilDiv,Int.cast_neg]
  linarith

/-- Enclosure of a rational quotient after division by the fixed scale. -/
theorem rounded_div_bounds (a b : ℤ) (hb : 0<b) :
    Bounds ((a:ℝ)/(b:ℝ)/(scale:ℝ))
      (((a/b:ℤ):ℝ)/scale) ((ceilDiv a b:ℝ)/scale) := by
  exact ⟨div_le_div_of_nonneg_right (floorDiv_le a b hb) scale_real_pos.le,
    div_le_div_of_nonneg_right (le_ceilDiv a b hb) scale_real_pos.le⟩

def point (r : ℚ) : DyadicInterval :=
  ⟨(r.num*scale)/(r.den:ℤ),ceilDiv (r.num*scale) (r.den:ℤ)⟩
def add (I J : DyadicInterval) : DyadicInterval := ⟨I.lower+J.lower,I.upper+J.upper⟩
def neg (I : DyadicInterval) : DyadicInterval := ⟨-I.upper,-I.lower⟩
def mulLower (I J : DyadicInterval) : ℤ :=
  min (min (I.lower*J.lower) (I.lower*J.upper))
      (min (I.upper*J.lower) (I.upper*J.upper))
def mulUpper (I J : DyadicInterval) : ℤ :=
  max (max (I.lower*J.lower) (I.lower*J.upper))
      (max (I.upper*J.lower) (I.upper*J.upper))
def mul (I J : DyadicInterval) : DyadicInterval :=
  ⟨I.mulLower J/scale,ceilDiv (I.mulUpper J) scale⟩

theorem point_contains (r : ℚ) : (point r).contains (r:ℝ) := by
  have h := rounded_div_bounds (r.num*scale) r.den (by exact_mod_cast r.den_pos)
  have he : ((r.num*scale:ℤ):ℝ)/(r.den:ℝ)/(scale:ℝ)=(r:ℝ) := by
    rw [Int.cast_mul,Rat.cast_def]
    field_simp [scale_real_pos.ne']
  simpa only [contains,point,Int.cast_natCast,he] using h

theorem add_contains {I J : DyadicInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (I.add J).contains (x+y) := by
  simpa only [contains,add,Int.cast_add,add_div] using hx.add hy

theorem neg_contains {I : DyadicInterval} {x : ℝ}
    (hx : I.contains x) : I.neg.contains (-x) := by
  simpa only [contains,neg,Int.cast_neg,neg_div] using hx.neg

theorem mul_contains {I J : DyadicInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (I.mul J).contains (x*y) := by
  have hlo := (rounded_div_bounds (I.mulLower J) scale scale_pos).1
  have hhi := (rounded_div_bounds (I.mulUpper J) scale scale_pos).2
  apply Bounds.weaken (l := (I.mulLower J:ℝ)/scale/scale)
    (u := (I.mulUpper J:ℝ)/scale/scale) ?_ hlo hhi
  apply hx.mul_corners hy <;>
    simp only [mulLower,mulUpper,Int.cast_min,Int.cast_max,Int.cast_mul]
  all_goals
    rw [div_div,div_mul_div_comm]
    apply (div_le_div_iff_of_pos_right (mul_pos scale_real_pos scale_real_pos)).mpr
    simp only [min_le_iff,le_max_iff]
    aesop

/-- Conversion is only needed at the final interface, not at every operation. -/
def toRational (I : DyadicInterval) : RationalInterval :=
  ⟨(I.lower:ℚ)/scale,(I.upper:ℚ)/scale⟩

theorem toRational_contains {I : DyadicInterval} {x : ℝ} :
    I.toRational.contains x ↔ I.contains x := by
  simp only [toRational,RationalInterval.contains,contains,Rat.cast_div,Rat.cast_intCast]

/-- Round an existing rational interval outwards once. -/
def ofRational (I : RationalInterval) : DyadicInterval :=
  ⟨(point I.lower).lower,(point I.upper).upper⟩

theorem ofRational_contains {I : RationalInterval} {x : ℝ}
    (hx : I.contains x) : (ofRational I).contains x := by
  exact ⟨(point_contains I.lower).1.trans hx.1,
    hx.2.trans (point_contains I.upper).2⟩

theorem lower_le {I : DyadicInterval} {x : ℝ} (hx : I.contains x) :
    ((I.lower:ℝ)/scale)≤x := hx.1

theorem upper_ge {I : DyadicInterval} {x : ℝ} (hx : I.contains x) :
    x≤((I.upper:ℝ)/scale) := hx.2

theorem pos_of_lower_pos {I : DyadicInterval} {x : ℝ}
    (hx : I.contains x) (hl : 0<I.lower) : 0<x := by
  exact lt_of_lt_of_le (div_pos (by exact_mod_cast hl) scale_real_pos) hx.1

end DyadicInterval

namespace PolynomialExpr

def dyadicEval {n : ℕ} : PolynomialExpr n → (Fin n → DyadicInterval) → DyadicInterval
  | .rational r, _ => .point r
  | .var i, box => box i
  | .add e f, box => (e.dyadicEval box).add (f.dyadicEval box)
  | .neg e, box => (e.dyadicEval box).neg
  | .mul e f, box => (e.dyadicEval box).mul (f.dyadicEval box)

theorem dyadicEval_contains {n : ℕ} (e : PolynomialExpr n)
    {x : Fin n → ℝ} {box : Fin n → DyadicInterval}
    (hx : ∀i,(box i).contains (x i)) :
    (e.dyadicEval box).contains (e.realEval x) := by
  induction e with
  | rational r => exact DyadicInterval.point_contains r
  | var i => exact hx i
  | add e f he hf => exact DyadicInterval.add_contains he hf
  | neg e he => exact DyadicInterval.neg_contains he
  | mul e f he hf => exact DyadicInterval.mul_contains he hf

theorem dyadicEval_pos {n : ℕ} (e : PolynomialExpr n)
    {x : Fin n → ℝ} {box : Fin n → DyadicInterval}
    (hx : ∀i,(box i).contains (x i)) (hl : 0<(e.dyadicEval box).lower) :
    0<e.realEval x :=
  DyadicInterval.pos_of_lower_pos (e.dyadicEval_contains hx) hl

end PolynomialExpr
end SparseLowerTail.Numerics

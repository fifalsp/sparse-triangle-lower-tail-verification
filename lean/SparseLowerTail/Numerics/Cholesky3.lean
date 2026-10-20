import SparseLowerTail.Numerics.RationalExpr
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Positive-radicand soundness and a checked rational LDL version of 3×3 interval Cholesky. -/
noncomputable section
open scoped BigOperators
namespace SparseLowerTail.Numerics

/-- The square-root inclusion rule needed by interval Cholesky.
Endpoints may be outward-rounded rationals certified by squared comparisons. -/
theorem sqrt_interval_enclosure {x a b l u : ℝ} (hx : Bounds x a b)
    (hl : 0≤l) (hu : 0≤u) (hla : l^2≤a) (hbu : b≤u^2) :
    Bounds (Real.sqrt x) l u := by
  have hx0 : 0≤x := (sq_nonneg l).trans (hla.trans hx.1)
  have hs := Real.sq_sqrt hx0
  have hp := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1,hx.2]

/-- The six independent entries (a,b,c,d,e,f) represent [[a,b,c],[b,d,e],[c,e,f]]. -/
def quadratic3 (v : Fin 6 → ℝ) (x y z : ℝ) : ℝ :=
  v 0*x^2+2*v 1*x*y+2*v 2*x*z+v 3*y^2+2*v 4*y*z+v 5*z^2

def pivot1 (v : Fin 6 → ℝ) : ℝ := v 3-(v 1)^2/v 0
def pivot2 (v : Fin 6 → ℝ) : ℝ := v 5-(v 2)^2/v 0-(v 4-v 1*v 2/v 0)^2/pivot1 v

/-- Exact completion of squares; these coefficients are the Cholesky radicands. -/
theorem quadratic3_completion (v : Fin 6 → ℝ) (h0 : v 0≠0) (h1 : pivot1 v≠0) (x y z : ℝ) :
    quadratic3 v x y z=v 0*(x+v 1/v 0*y+v 2/v 0*z)^2+
      pivot1 v*(y+(v 4-v 1*v 2/v 0)/pivot1 v*z)^2+pivot2 v*z^2 := by
  unfold pivot1 at h1
  have hd : v 0*v 3-v 1^2≠0 := by
    intro hz
    apply h1
    have he : v 3-v 1^2/v 0=(v 0*v 3-v 1^2)/v 0 := by field_simp
    rw [he,hz,zero_div]
  unfold quadratic3 pivot2 pivot1
  field_simp [hd]
  ring

/-- Strictly positive pivots imply positive definiteness of the real symmetric quadratic form. -/
theorem quadratic3_pos_of_pivots {v : Fin 6 → ℝ} (h0 : 0<v 0) (h1 : 0<pivot1 v) (h2 : 0<pivot2 v)
    (x y z : ℝ) (hxyz : x≠0 ∨ y≠0 ∨ z≠0) : 0<quadratic3 v x y z := by
  rw [quadratic3_completion v (ne_of_gt h0) (ne_of_gt h1)]
  have ha := mul_nonneg h0.le (sq_nonneg (x+v 1/v 0*y+v 2/v 0*z))
  have hb := mul_nonneg h1.le (sq_nonneg (y+(v 4-v 1*v 2/v 0)/pivot1 v*z))
  by_cases hz : z=0
  · subst z
    simp only [mul_zero,add_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    by_cases hy : y=0
    · subst y
      have hx : x≠0 := by simpa using hxyz
      simpa using mul_pos h0 (sq_pos_of_ne_zero hx)
    · have hh := mul_pos h1 (sq_pos_of_ne_zero hy)
      positivity
  · exact add_pos_of_nonneg_of_pos (add_nonneg ha hb) (mul_pos h2 (sq_pos_of_ne_zero hz))

/-- Rational expressions for the first two exact pivots. -/
def pivotExpr1 : RationalExpr 6 := .var 3-(.var 1)^2/.var 0
def pivotExpr2 : RationalExpr 6 := .var 5-(.var 2)^2/.var 0-(.var 4-.var 1*.var 2/.var 0)^2/pivotExpr1

@[simp] theorem pivotExpr1_eval (v : Fin 6 → ℝ) : pivotExpr1.realEval v=pivot1 v := by
  simp [pivotExpr1,pivot1]
@[simp] theorem pivotExpr2_eval (v : Fin 6 → ℝ) : pivotExpr2.realEval v=pivot2 v := by
  simp [pivotExpr2,pivot2]

/-- The LDL recurrence is identical to the square-root Cholesky radicands. -/
theorem cholesky_radicands_eq (v : Fin 6 → ℝ) (h0 : 0<v 0) (h1 : 0<pivot1 v) :
    v 3-(v 1/Real.sqrt (v 0))^2=pivot1 v ∧
    v 5-(v 2/Real.sqrt (v 0))^2-
      ((v 4-(v 1/Real.sqrt (v 0))*(v 2/Real.sqrt (v 0)))/Real.sqrt (pivot1 v))^2=pivot2 v := by
  have hs0 := Real.sq_sqrt h0.le
  have hs1 := Real.sq_sqrt h1.le
  constructor
  · unfold pivot1
    rw [div_pow,hs0]
  · unfold pivot2
    rw [div_pow,div_pow,hs0,hs1]
    congr 2
    rw [div_mul_div_comm,← pow_two,hs0]

/-- A successful interval evaluation with positive lower endpoints certifies every
real symmetric matrix represented by the input entry intervals. -/
theorem interval_cholesky3_sound {box : Fin 6 → DyadicInterval} {I J : DyadicInterval}
    (h0 : 0<(box 0).lower) (hI : pivotExpr1.dyadicEval box=some I) (h1 : 0<I.lower)
    (hJ : pivotExpr2.dyadicEval box=some J) (h2 : 0<J.lower)
    {v : Fin 6 → ℝ} (hv : ∀ i, (box i).contains (v i)) :
    ∀ x y z : ℝ, x≠0 ∨ y≠0 ∨ z≠0 → 0<quadratic3 v x y z := by
  have hp0 := DyadicInterval.pos_of_lower_pos (hv 0) h0
  have hp1 := DyadicInterval.pos_of_lower_pos (pivotExpr1.dyadicEval_contains hv hI) h1
  have hp2 := DyadicInterval.pos_of_lower_pos (pivotExpr2.dyadicEval_contains hv hJ) h2
  simp only [pivotExpr1_eval,pivotExpr2_eval] at hp1 hp2
  exact quadratic3_pos_of_pivots hp0 hp1 hp2

/-- The literal Cholesky radicand criterion, for arbitrary sound interval enclosures. -/
theorem cholesky3_positive_of_interval_radicands {v : Fin 6 → ℝ} {l₀ u₀ l₁ u₁ l₂ u₂ : ℝ}
    (h0 : Bounds (v 0) l₀ u₀) (hl0 : 0<l₀)
    (h1 : Bounds (v 3-(v 1/Real.sqrt (v 0))^2) l₁ u₁) (hl1 : 0<l₁)
    (h2 : Bounds (v 5-(v 2/Real.sqrt (v 0))^2-
      ((v 4-(v 1/Real.sqrt (v 0))*(v 2/Real.sqrt (v 0)))/
        Real.sqrt (v 3-(v 1/Real.sqrt (v 0))^2))^2) l₂ u₂) (hl2 : 0<l₂) :
    ∀ x y z : ℝ, x≠0 ∨ y≠0 ∨ z≠0 → 0<quadratic3 v x y z := by
  have hp0 : 0<v 0 := hl0.trans_le h0.1
  have he1 : v 3-(v 1/Real.sqrt (v 0))^2=pivot1 v := by
    unfold pivot1
    rw [div_pow,Real.sq_sqrt hp0.le]
  rw [he1] at h1 h2
  have hp1 : 0<pivot1 v := hl1.trans_le h1.1
  rw [(cholesky_radicands_eq v hp0 hp1).2] at h2
  exact quadratic3_pos_of_pivots hp0 hp1 (hl2.trans_le h2.1)

/-- The actual symmetric real matrix represented by six independent entries. -/
def symmetricMatrix3 (v : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![v 0,v 1,v 2;v 1,v 3,v 4;v 2,v 4,v 5]

/-- Positivity of the quadratic form is exactly positive definiteness of the matrix. -/
theorem symmetricMatrix3_posDef {v : Fin 6 → ℝ}
    (hquad : ∀ x y z : ℝ, x≠0 ∨ y≠0 ∨ z≠0 → 0<quadratic3 v x y z) :
    (symmetricMatrix3 v).PosDef := by
  refine ⟨?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [symmetricMatrix3,Matrix.conjTranspose_apply]
  · intro w hw
    have hn : w 0≠0 ∨ w 1≠0 ∨ w 2≠0 := by
      by_contra hh
      push_neg at hh
      apply hw
      funext i
      fin_cases i <;> simp_all
    have hh := hquad (w 0) (w 1) (w 2) hn
    convert hh using 1
    simp [symmetricMatrix3,quadratic3,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring

/-- A successful checked interval run certifies every represented real symmetric matrix. -/
theorem interval_cholesky3_posDef {box : Fin 6 → DyadicInterval} {I J : DyadicInterval}
    (h0 : 0<(box 0).lower) (hI : pivotExpr1.dyadicEval box=some I) (h1 : 0<I.lower)
    (hJ : pivotExpr2.dyadicEval box=some J) (h2 : 0<J.lower)
    {v : Fin 6 → ℝ} (hv : ∀ i, (box i).contains (v i)) : (symmetricMatrix3 v).PosDef :=
  symmetricMatrix3_posDef (interval_cholesky3_sound h0 hI h1 hJ h2 hv)

/-- Literal interval-Cholesky success implies positive definiteness, in matrix form. -/
theorem cholesky3_interval_radicands_posDef {v : Fin 6 → ℝ} {l₀ u₀ l₁ u₁ l₂ u₂ : ℝ}
    (h0 : Bounds (v 0) l₀ u₀) (hl0 : 0<l₀)
    (h1 : Bounds (v 3-(v 1/Real.sqrt (v 0))^2) l₁ u₁) (hl1 : 0<l₁)
    (h2 : Bounds (v 5-(v 2/Real.sqrt (v 0))^2-
      ((v 4-(v 1/Real.sqrt (v 0))*(v 2/Real.sqrt (v 0)))/
        Real.sqrt (v 3-(v 1/Real.sqrt (v 0))^2))^2) l₂ u₂) (hl2 : 0<l₂) :
    (symmetricMatrix3 v).PosDef :=
  symmetricMatrix3_posDef (cholesky3_positive_of_interval_radicands h0 hl0 h1 hl1 h2 hl2)

/-- The executable test rejects a zero-crossing denominator and any nonpositive pivot lower endpoint. -/
def intervalCholesky3Check (box : Fin 6 → DyadicInterval) : Bool :=
  if 0<(box 0).lower then
    match pivotExpr1.dyadicEval box,pivotExpr2.dyadicEval box with
    | some I,some J => decide (0<I.lower ∧ 0<J.lower)
    | _,_ => false
  else false

/-- Every accepted input box certifies all real symmetric matrices inside it. -/
theorem intervalCholesky3Check_sound {box : Fin 6 → DyadicInterval}
    (h : intervalCholesky3Check box=true) {v : Fin 6 → ℝ} (hv : ∀ i, (box i).contains (v i)) :
    (symmetricMatrix3 v).PosDef := by
  unfold intervalCholesky3Check at h
  split_ifs at h with h0
  · cases hI : pivotExpr1.dyadicEval box with
    | none => simp [hI] at h
    | some I =>
      cases hJ : pivotExpr2.dyadicEval box with
      | none => simp [hI,hJ] at h
      | some J =>
        simp only [hI,hJ,decide_eq_true_eq] at h
        exact interval_cholesky3_posDef h0 hI h.1 hJ h.2 hv

/-- Kernel-evaluated acceptance of the identity matrix. -/
theorem intervalCholesky3Check_identity :
    intervalCholesky3Check ![.point 1,.point 0,.point 0,.point 1,.point 0,.point 1]=true := by decide +kernel

/-- A zero first pivot is rejected. -/
theorem intervalCholesky3Check_zero :
    intervalCholesky3Check ![.point 0,.point 0,.point 0,.point 1,.point 0,.point 1]=false := by decide +kernel

/-- A negative final pivot is rejected. -/
theorem intervalCholesky3Check_indefinite :
    intervalCholesky3Check ![.point 1,.point 0,.point 0,.point 1,.point 0,.point (-1)]=false := by decide +kernel

end SparseLowerTail.Numerics

import SparseLowerTail.Section08.FamilyLocalScaling
import SparseLowerTail.Numerics.DyadicInterval

/-! Exact dyadic replay of the three-by-three congruence and its row margins. -/
namespace SparseLowerTail.Certificate
open Numerics
abbrev FamilyIntervalMatrix := Fin 3 → Fin 3 → DyadicInterval
abbrev FamilyRationalMatrix := Fin 3 → Fin 3 → ℚ

def intervalSumThree (v : Fin 3 → DyadicInterval) : DyadicInterval :=
  ((v 0).add (v 1)).add (v 2)

theorem intervalSumThree_contains {v : Fin 3 → DyadicInterval} {x : Fin 3 → ℝ}
    (hx : ∀i,(v i).contains (x i)) : (intervalSumThree v).contains (sumThree x) :=
  DyadicInterval.add_contains (DyadicInterval.add_contains (hx 0) (hx 1)) (hx 2)

def familyIntervalCongruence (H : FamilyIntervalMatrix) (T : FamilyRationalMatrix) :
    FamilyIntervalMatrix := fun i j => intervalSumThree fun k => intervalSumThree fun l =>
      ((DyadicInterval.point (T k i)).mul (H k l)).mul (DyadicInterval.point (T l j))

theorem familyIntervalCongruence_contains {H : FamilyIntervalMatrix}
    {A : FamilyMatrix} (hH : ∀i j,(H i j).contains (A i j))
    (T : FamilyRationalMatrix) (i j : Fin 3) :
    (familyIntervalCongruence H T i j).contains
      (familyCongruence A (fun k l => (T k l : ℝ)) i j) := by
  have h := intervalSumThree_contains (fun k => intervalSumThree_contains (fun l =>
    DyadicInterval.mul_contains (DyadicInterval.mul_contains
      (DyadicInterval.point_contains (T k i)) (hH k l))
      (DyadicInterval.point_contains (T l j))))
  convert h using 1
  simp only [familyCongruence,Matrix.mul_apply,Matrix.transpose_apply,
    Fin.sum_univ_three,sumThree]
  ring

def intervalAbsBound (I : DyadicInterval) : ℤ := max (-I.lower) I.upper

theorem intervalAbsBound_sound {I : DyadicInterval} {x : ℝ} (hx : I.contains x) :
    |x|≤(intervalAbsBound I : ℝ)/DyadicInterval.scale := by
  apply abs_le.mpr
  constructor
  · have h : (-(I.lower : ℝ))≤(intervalAbsBound I : ℝ) := by
      exact_mod_cast le_max_left (-I.lower) I.upper
    have hh := div_le_div_of_nonneg_right h DyadicInterval.scale_real_pos.le
    dsimp [DyadicInterval.contains] at hx
    rw [neg_div] at hh
    linarith [hx.1]
  · exact hx.2.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast le_max_right (-I.lower) I.upper)
      DyadicInterval.scale_real_pos.le)

def familyIntervalRowMargin (H : FamilyIntervalMatrix) (i j k : Fin 3) : ℤ :=
  (H i i).lower-intervalAbsBound (H i j)-intervalAbsBound (H i k)

theorem familyIntervalRowMargin_sound {H : FamilyIntervalMatrix} {A : FamilyMatrix}
    (hH : ∀i j,(H i j).contains (A i j)) (i j k : Fin 3) :
    (familyIntervalRowMargin H i j k : ℝ)/DyadicInterval.scale+
      |A i j|+|A i k|≤A i i := by
  have h1 := intervalAbsBound_sound (hH i j)
  have h2 := intervalAbsBound_sound (hH i k)
  have h3 := (hH i i).1
  simp only [familyIntervalRowMargin,Int.cast_sub,sub_div]
  linarith

/-- Every operation in this sufficient positivity test is integer arithmetic. -/
def FamilyIntervalPositive (H : FamilyIntervalMatrix) : Prop :=
  0<familyIntervalRowMargin H 0 1 2 ∧
  0<familyIntervalRowMargin H 1 0 2 ∧
  0<familyIntervalRowMargin H 2 0 1

instance (H : FamilyIntervalMatrix) : Decidable (FamilyIntervalPositive H) :=
  inferInstanceAs (Decidable (0<familyIntervalRowMargin H 0 1 2 ∧
    0<familyIntervalRowMargin H 1 0 2 ∧ 0<familyIntervalRowMargin H 2 0 1))

/-- Positive computed row margins prove strict positivity of any actual
symmetric matrix, including a numerically proposed congruence. -/
theorem familyQuadratic_pos_of_interval_congruence {A : FamilyMatrix}
    (hA : ∀i j,A i j=A j i) (H : FamilyIntervalMatrix) (T : FamilyRationalMatrix)
    (hH : ∀i j,(H i j).contains (A i j))
    (hp : FamilyIntervalPositive (familyIntervalCongruence H T))
    {v : FamilyVector} (hv : v≠0) : 0<familyQuadratic A v := by
  let J := familyIntervalCongruence H T
  let η : ℝ := (min (min (familyIntervalRowMargin J 0 1 2)
    (familyIntervalRowMargin J 1 0 2)) (familyIntervalRowMargin J 2 0 1) : ℤ)/
    DyadicInterval.scale
  have hη : 0<η := by
    apply div_pos _ DyadicInterval.scale_real_pos
    exact_mod_cast lt_min (lt_min hp.1 hp.2.1) hp.2.2
  have hc := familyIntervalCongruence_contains hH T
  have h0 := familyIntervalRowMargin_sound hc 0 1 2
  have h1 := familyIntervalRowMargin_sound hc 1 0 2
  have h2 := familyIntervalRowMargin_sound hc 2 0 1
  have he (i j : Fin 3) := familyCongruence_symmetric _ (fun k l => (T k l : ℝ))
    hA i j
  rw [he 1 0] at h1
  rw [he 2 0,he 2 1] at h2
  apply familyQuadratic_pos_of_congruence_dominance A
    (fun k l => (T k l : ℝ)) hη (he 1 0) (he 2 0) (he 2 1) _ _ _ hv
  all_goals
    have hmin0 : η≤(familyIntervalRowMargin J 0 1 2 : ℝ)/DyadicInterval.scale := by
      apply div_le_div_of_nonneg_right _ DyadicInterval.scale_real_pos.le
      exact_mod_cast (min_le_left _ _).trans (min_le_left _ _)
    have hmin1 : η≤(familyIntervalRowMargin J 1 0 2 : ℝ)/DyadicInterval.scale := by
      apply div_le_div_of_nonneg_right _ DyadicInterval.scale_real_pos.le
      exact_mod_cast (min_le_left _ _).trans (min_le_right _ _)
    have hmin2 : η≤(familyIntervalRowMargin J 2 0 1 : ℝ)/DyadicInterval.scale := by
      apply div_le_div_of_nonneg_right _ DyadicInterval.scale_real_pos.le
      exact_mod_cast min_le_right _ _
    linarith

/-- The generic integer replay applies to the actual scaled family Hessian. -/
theorem familyHessian_pos_of_interval_congruence {z : ℝ} {q : FamilyVector}
    (H : FamilyIntervalMatrix) (T : FamilyRationalMatrix)
    (hH : ∀i j,(H i j).contains (familyHessianScaled z q i j))
    (hp : FamilyIntervalPositive (familyIntervalCongruence H T))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  apply familyHessian_pos_of_scaled z q (v := v) (hv := hv)
  intro w hw
  exact familyQuadratic_pos_of_interval_congruence (familyHessianScaled_symmetric z q)
    H T hH hp hw

end SparseLowerTail.Certificate

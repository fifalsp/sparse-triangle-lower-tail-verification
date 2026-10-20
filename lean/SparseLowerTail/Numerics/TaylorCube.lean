import SparseLowerTail.Numerics.BoxLowerBounds
import SparseLowerTail.Numerics.TaylorThird
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The full quantitative C³ cube estimate in `lem:taylor`. -/
noncomputable section
namespace SparseLowerTail.Numerics
open Set
open scoped BigOperators

def infinity3 (y : Fin 3 → ℝ) : ℝ := max |y 0| (max |y 1| |y 2|)
def euclideanSq3 (y : Fin 3 → ℝ) : ℝ := (y 0)^2+(y 1)^2+(y 2)^2

theorem infinity3_nonneg (y : Fin 3 → ℝ) : 0≤ infinity3 y :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem abs_le_infinity3 (y : Fin 3 → ℝ) (i : Fin 3) : |y i|≤ infinity3 y := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The explicit maximum is exactly the usual supremum norm on the coordinate space. -/
theorem infinity3_eq_norm (y : Fin 3 → ℝ) : infinity3 y=‖y‖ := by
  apply le_antisymm
  · exact max_le (norm_le_pi_norm y 0)
      (max_le (norm_le_pi_norm y 1) (norm_le_pi_norm y 2))
  · exact (pi_norm_le_iff_of_nonneg (infinity3_nonneg y)).mpr (abs_le_infinity3 y)

theorem infinity3_sq_le_euclideanSq3 (y : Fin 3 → ℝ) : infinity3 y^2≤euclideanSq3 y := by
  have h0 : |y 0|^2≤euclideanSq3 y := by
    dsimp [euclideanSq3]; rw [sq_abs]; nlinarith [sq_nonneg (y 1),sq_nonneg (y 2)]
  have h1 : |y 1|^2≤euclideanSq3 y := by
    dsimp [euclideanSq3]; rw [sq_abs]; nlinarith [sq_nonneg (y 0),sq_nonneg (y 2)]
  have h2 : |y 2|^2≤euclideanSq3 y := by
    dsimp [euclideanSq3]; rw [sq_abs]; nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]
  unfold infinity3
  rcases le_total |y 0| (max |y 1| |y 2|) with h|h
  · rw [max_eq_right h]
    rcases le_total |y 1| |y 2| with h'|h'
    · rwa [max_eq_right h']
    · rwa [max_eq_left h']
  · rwa [max_eq_left h]

/-- The sum of squares is the square of the genuine Euclidean norm. -/
theorem euclideanSq3_eq_norm_sq (y : Fin 3 → ℝ) :
    euclideanSq3 y=‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [euclideanSq3,Fin.sum_univ_three,Real.norm_eq_abs,sq_abs]

def thirdForm3 (T : Fin 3 → Fin 3 → Fin 3 → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  ∑ i,∑ j,∑ k,T i j k*y i*y j*y k

/-- Component enclosures give the paper's sharp cubic supremum-norm remainder. -/
theorem thirdForm3_bound {T C : Fin 3 → Fin 3 → Fin 3 → ℝ} (y : Fin 3 → ℝ)
    (hC : ∀ i j k, |T i j k|≤C i j k) :
    |thirdForm3 T y|≤(∑ i,∑ j,∑ k,C i j k)*infinity3 y^3 := by
  have hm := infinity3_nonneg y
  have hp (i j k : Fin 3) : |y i*y j*y k|≤ infinity3 y^3 := by
    rw [abs_mul,abs_mul,pow_succ,pow_two]
    exact mul_le_mul (mul_le_mul (abs_le_infinity3 y i) (abs_le_infinity3 y j)
      (abs_nonneg _) hm) (abs_le_infinity3 y k) (abs_nonneg _) (mul_nonneg hm hm)
  have hterm (i j k : Fin 3) : |T i j k*y i*y j*y k|≤C i j k*infinity3 y^3 := by
    have hh := mul_le_mul (hC i j k) (hp i j k) (abs_nonneg _) ((abs_nonneg _).trans (hC i j k))
    simpa only [abs_mul,mul_assoc] using hh
  unfold thirdForm3
  calc
    |∑ i,∑ j,∑ k,T i j k*y i*y j*y k|
        ≤∑ i,∑ j,∑ k,|T i j k*y i*y j*y k| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤∑ i,∑ j,∑ k,C i j k*infinity3 y^3 :=
      Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>Finset.sum_le_sum fun k _=>hterm i j k
    _ = (∑ i,∑ j,∑ k,C i j k)*infinity3 y^3 := by simp only [Finset.sum_mul]

theorem qform3_eq_hessian_sum (H : Fin 6 → ℝ) (y : Fin 3 → ℝ) :
    qform3 H y=∑ i,∑ j,hessianRow3 H i j*y i*y j := by
  simp [qform3,quadratic3,hessianRow3,Fin.sum_univ_three]
  ring

/-- The third segment derivative for an arbitrary genuine third-partial tensor. -/
theorem box_segment_third {K : (Fin 3 → ℝ) → Fin 6 → ℝ}
    {T : (Fin 3 → ℝ) → Fin 3 → Fin 3 → Fin 3 → ℝ} (c y : Fin 3 → ℝ) (t : ℝ)
    (hK : ∀ i j, HasFDerivAt (fun x=>hessianRow3 (K x) i j)
      (linearForm3 (T (c+t•y) i j)) (c+t•y)) :
    HasDerivAt (fun s:ℝ=>qform3 (K (c+s•y)) y) (thirdForm3 (T (c+t•y)) y) t := by
  have h i j := box_segment_first (G:=fun x=>T x i j) c y t (hK i j)
  have hs := HasDerivAt.sum (u:=Finset.univ) (fun i _=>
    HasDerivAt.sum (u:=Finset.univ) (fun j _=>((h i j).mul_const (y i)).mul_const (y j)))
  convert hs using 1
  · ext s
    simp [qform3,quadratic3,hessianRow3,Fin.sum_univ_three]
    ring
  · simp [thirdForm3,dot3,Fin.sum_univ_three]
    ring

/-- Full quantitative estimate, with all three actual segment derivatives supplied
by the chain rule and a uniform bound for the third partial tensor. -/
theorem taylor_cube_segment {f f₁ f₂ f₃ : ℝ → ℝ} {y : Fin 3 → ℝ} {δ S ℓ : ℝ}
    (h₁ : ∀ t∈Icc (0:ℝ) 1,HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t∈Icc (0:ℝ) 1,HasDerivAt f₁ (f₂ t) t)
    (h₃ : ∀ t∈Icc (0:ℝ) 1,HasDerivAt f₂ (f₃ t) t)
    (h0 : f 0=0) (hd0 : f₁ 0=0) (hH : ℓ*euclideanSq3 y≤f₂ 0)
    (hthird : ∀ t∈Icc (0:ℝ) 1, |f₃ t|≤S*infinity3 y^3)
    (hS : 0≤S) (hℓ : 0<ℓ) (hy : 0< infinity3 y ∧ infinity3 y≤δ)
    (hmargin : δ*S<3*ℓ) :
    ℓ/2*euclideanSq3 y-S/6*infinity3 y^3≤f 1 ∧
    (ℓ/2-δ*S/6)*infinity3 y^2≤ℓ/2*euclideanSq3 y-S/6*infinity3 y^3 ∧
    0<(ℓ/2-δ*S/6)*infinity3 y^2 := by
  have ht := segment_taylor3_lower h₁ h₂ h₃
    (fun t ht=>(abs_le.mp (hthird t ht)).1)
  rw [h0,hd0] at ht
  have hnorm := infinity3_sq_le_euclideanSq3 y
  have hscale : S*infinity3 y^3≤δ*S*infinity3 y^2 := by
    have hh := mul_le_mul_of_nonneg_right hy.2 (mul_nonneg hS (sq_nonneg (infinity3 y)))
    nlinarith only [hh]
  refine ⟨by linarith,?_,mul_pos (by linarith) (sq_pos_of_pos hy.1)⟩
  nlinarith [mul_le_mul_of_nonneg_left hnorm hℓ.le]

/-- `lem:taylor` for the actual function, gradient, Hessian and third partials.
The cube is expressed coordinatewise; infinity3_eq_norm identifies its norm. -/
theorem taylor_cube_lower
    {Φ : (Fin 3 → ℝ) → ℝ} {G : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {K : (Fin 3 → ℝ) → Fin 6 → ℝ}
    {T : (Fin 3 → ℝ) → Fin 3 → Fin 3 → Fin 3 → ℝ}
    {C : Fin 3 → Fin 3 → Fin 3 → ℝ} {P y : Fin 3 → ℝ} {δ S ℓ : ℝ}
    (hΦ : ∀ x, (∀ i,|x i-P i|≤δ) → HasFDerivAt Φ (linearForm3 (G x)) x)
    (hG : ∀ x, (∀ i,|x i-P i|≤δ) → ∀ i,
      HasFDerivAt (fun w=>G w i) (linearForm3 (hessianRow3 (K x) i)) x)
    (hK : ∀ x, (∀ i,|x i-P i|≤δ) → ∀ i j,
      HasFDerivAt (fun w=>hessianRow3 (K w) i j) (linearForm3 (T x i j)) x)
    (hval : Φ P=0) (hgrad : ∀ i,G P i=0)
    (hH : ∀ v,ℓ*euclideanSq3 v≤qform3 (K P) v)
    (hC : ∀ x, (∀ i,|x i-P i|≤δ) → ∀ i j k, |T x i j k|≤C i j k)
    (hS : (∑ i,∑ j,∑ k,C i j k)≤S)
    (hℓ : 0<ℓ) (hy : 0< infinity3 y ∧ infinity3 y≤δ) (hmargin : δ*S<3*ℓ) :
    ℓ/2*euclideanSq3 y-S/6*infinity3 y^3≤Φ (P+y) ∧
    (ℓ/2-δ*S/6)*infinity3 y^2≤ℓ/2*euclideanSq3 y-S/6*infinity3 y^3 ∧
    0<(ℓ/2-δ*S/6)*infinity3 y^2 := by
  have hseg (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : ∀ i,|(P+t•y) i-P i|≤δ := by
    intro i
    have hm : |t|≤1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have hcoord := mul_le_mul hm (abs_le_infinity3 y i) (abs_nonneg _) zero_le_one
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_sub_cancel_left,abs_mul,one_mul]
      using (by simpa only [one_mul] using hcoord : |t| * |y i|≤ infinity3 y).trans hy.2
  have hP : ∀ i, |P i-P i|≤δ := by
    intro i
    simpa using hy.1.le.trans hy.2
  have hS0 : 0≤S := (Finset.sum_nonneg (fun i _=>Finset.sum_nonneg
    (fun j _=>Finset.sum_nonneg (fun k _=>(abs_nonneg _).trans (hC P hP i j k))))).trans hS
  have ht := taylor_cube_segment
    (fun t ht=>box_segment_first P y t (hΦ _ (hseg t ht)))
    (fun t ht=>box_segment_second P y t (hG _ (hseg t ht)))
    (fun t ht=>box_segment_third P y t (hK _ (hseg t ht)))
    (by simpa using hval) (by simp [dot3,hgrad]) (by simpa using hH y)
    (fun t ht=>(thirdForm3_bound y (hC _ (hseg t ht))).trans
      (mul_le_mul_of_nonneg_right hS (pow_nonneg (infinity3_nonneg y) 3)))
    hS0 hℓ hy hmargin
  simpa using ht

end SparseLowerTail.Numerics

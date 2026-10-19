import SparseLowerTail.Section08.FamilyLocalDominance
import SparseLowerTail.Section08.FamilyGradientParameter
import SparseLowerTail.Numerics.QuadraticAxisBounds

/-! Analytic assembly of the exterior-family Taylor bound. All inputs are
explicit scalar value, gradient, and Hessian enclosures. A complete finite
cover must still supply these bounds and a positive numerical margin. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Numerics Set

private theorem cross_term_lower {a x y K r s : ℝ}
    (ha : |a|≤K) (hx : |x|≤r) (hy : |y|≤s) : -K*r*s≤x*y*a := by
  have hK : 0≤K := (abs_nonneg a).trans ha
  have hr : 0≤r := (abs_nonneg x).trans hx
  have hab : |a| * |x|≤K*r := mul_le_mul ha hx (abs_nonneg x) hK
  have hh := mul_le_mul hab hy (abs_nonneg y) (mul_nonneg hK hr)
  have he : |a| * |x| * |y|=|x*y*a| := by rw [abs_mul,abs_mul]; ring
  rw [he] at hh
  linarith [neg_abs_le (x*y*a)]

def familyCrossError (K : Fin 3 → Fin 3 → ℝ) (r : FamilyVector) : ℝ :=
  K 0 1*r 0*r 1+K 0 2*r 0*r 2+K 1 2*r 1*r 2

/-- Diagonal curvature retains its sign; only cross terms use absolute
bounds. This is sharper than replacing the whole Hessian by a norm. -/
theorem familyHessianForm_exterior_lower {z : ℝ} {q v r h : FamilyVector}
    {K : Fin 3 → Fin 3 → ℝ}
    (hv : ∀i,|v i|≤r i)
    (hdiag : ∀i,h i≤familyHessian z q i i)
    (hoff : ∀i j,i<j → |familyHessian z q i j|≤K i j) :
    sumThree (fun i => h i*(v i)^2)-2*familyCrossError K r≤familyHessianForm z q v := by
  have hd0 := mul_nonneg (sub_nonneg.mpr (hdiag 0)) (sq_nonneg (v 0))
  have hd1 := mul_nonneg (sub_nonneg.mpr (hdiag 1)) (sq_nonneg (v 1))
  have hd2 := mul_nonneg (sub_nonneg.mpr (hdiag 2)) (sq_nonneg (v 2))
  have ho01 := cross_term_lower (hoff 0 1 (by decide)) (hv 0) (hv 1)
  have ho02 := cross_term_lower (hoff 0 2 (by decide)) (hv 0) (hv 2)
  have ho12 := cross_term_lower (hoff 1 2 (by decide)) (hv 1) (hv 2)
  have hs10 := familyHessian_symmetric z q 1 0
  have hs20 := familyHessian_symmetric z q 2 0
  have hs21 := familyHessian_symmetric z q 2 1
  simp only [familyHessianForm,familyCrossError,sumThree,hs10,hs20,hs21]
  nlinarith

/-- The exterior leaf bound used in the paper. The beta values may be chosen
from any of the three certified one-coordinate quadratic estimates. -/
theorem familyPhi_exterior_lower {z : ℝ} {p q r P m h β : FamilyVector}
    {K : Fin 3 → Fin 3 → ℝ} {A : ℝ}
    (hvalue : A≤familyPhi z p)
    (hr : ∀i,|q i-p i|≤r i)
    (hgupper : ∀i,|familyGradient z p i|≤P i)
    (hglower : ∀i,m i≤|familyGradient z p i|)
    (hchoice : ∀i,β i≤-P i*r i+min 0 (h i)*(r i)^2/2 ∨
      (0<h i ∧ β i≤-(P i)^2/(2*h i)) ∨
      (0<h i ∧ h i*r i≤m i ∧ β i≤-P i*r i+h i*(r i)^2/2))
    (hdiag : ∀s∈Icc (0:ℝ) 1,∀i,h i≤familyHessian z (familySegment p (q-p) s) i i)
    (hoff : ∀s∈Icc (0:ℝ) 1,∀i j,i<j →
      |familyHessian z (familySegment p (q-p) s) i j|≤K i j) :
    A+sumThree β-familyCrossError K r≤familyPhi z q := by
  have ht := segment_taylor_lower
    (f := fun s => familyPhi z (familySegment p (q-p) s))
    (f₁ := fun s => sumThree (fun i => (q-p) i*familyGradient z (familySegment p (q-p) s) i))
    (f₂ := fun s => familyHessianForm z (familySegment p (q-p) s) (q-p))
    (M := -(sumThree (fun i => h i*((q-p) i)^2)-2*familyCrossError K r))
    (fun s _ => familyPhi_segment_deriv z p (q-p) s)
    (fun s _ => familyHessianForm_segment_deriv z p (q-p) s)
    (fun s hs => by
      simpa only [neg_neg] using familyHessianForm_exterior_lower hr (hdiag s hs) (hoff s hs))
  have hb (i : Fin 3) := quadratic_axis_chosen (hgupper i) (hglower i) (hr i) (hchoice i)
  simp only [familySegment_zero,familySegment_sub_one,sumThree,Pi.sub_apply] at ht
  simp only [sumThree]
  nlinarith [hb 0,hb 1,hb 2]

end SparseLowerTail.Certificate

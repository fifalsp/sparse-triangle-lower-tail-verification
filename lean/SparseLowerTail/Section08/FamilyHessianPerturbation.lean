import SparseLowerTail.Section08.FamilyScaledIntervals
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Quantitative stability of the actual scaled family Hessian. These bounds
allow a radius extension to reuse existing point and parameter certificates. -/
noncomputable section
namespace SparseLowerTail.Certificate.HessianPerturbation
open Numerics Section04 Set

/-- Bounds for two values and their change under a coordinate perturbation. -/
structure PairedBounds (ε x y B K : ℝ) : Prop where
  left : |x| ≤ B
  right : |y| ≤ B
  change : |x-y| ≤ K*ε

namespace PairedBounds

theorem constant {ε c B : ℝ} (hc : |c| ≤ B) : PairedBounds ε c c B 0 :=
  ⟨hc,hc,by simp⟩

theorem add {ε x y u v B K C L : ℝ}
    (h : PairedBounds ε x y B K) (g : PairedBounds ε u v C L) :
    PairedBounds ε (x+u) (y+v) (B+C) (K+L) := by
  refine ⟨(abs_add_le x u).trans (add_le_add h.left g.left),
    (abs_add_le y v).trans (add_le_add h.right g.right),?_⟩
  have he : (x+u)-(y+v)=(x-y)+(u-v) := by ring
  rw [he]
  have hh := (abs_add_le (x-y) (u-v)).trans (add_le_add h.change g.change)
  nlinarith only [hh]

theorem neg {ε x y B K : ℝ} (h : PairedBounds ε x y B K) :
    PairedBounds ε (-x) (-y) B K := by
  refine ⟨by simpa only [abs_neg] using h.left,
    by simpa only [abs_neg] using h.right, ?_⟩
  simpa only [neg_sub_neg,abs_sub_comm y x] using h.change

theorem sub {ε x y u v B K C L : ℝ}
    (h : PairedBounds ε x y B K) (g : PairedBounds ε u v C L) :
    PairedBounds ε (x-u) (y-v) (B+C) (K+L) := by
  simpa only [sub_eq_add_neg] using h.add g.neg

theorem mul {ε x y u v B K C L : ℝ}
    (h : PairedBounds ε x y B K) (g : PairedBounds ε u v C L) :
    PairedBounds ε (x*u) (y*v) (B*C) (B*L+C*K) := by
  have hB : 0 ≤ B := (abs_nonneg x).trans h.left
  refine ⟨?_,?_,?_⟩
  · rw [abs_mul]
    exact mul_le_mul h.left g.left (abs_nonneg _) hB
  · rw [abs_mul]
    exact mul_le_mul h.right g.right (abs_nonneg _) hB
  · have he : x*u-y*v=x*(u-v)+(x-y)*v := by ring
    rw [he]
    calc
      _ ≤ |x*(u-v)|+|(x-y)*v| := abs_add_le _ _
      _ = |x| * |u-v| + |x-y| * |v| := by rw [abs_mul,abs_mul]
      _ ≤ B*(L*ε)+(K*ε)*C := add_le_add
        (mul_le_mul h.left g.change (abs_nonneg _) hB)
        (mul_le_mul h.change g.right (abs_nonneg _) ((abs_nonneg _).trans h.change))
      _ = (B*L+C*K)*ε := by ring

end PairedBounds

theorem exp_neg_bound {x : ℝ} (hx : -1 ≤ x) : |Real.exp (-x)| ≤ 3 := by
  rw [abs_of_pos (Real.exp_pos _)]
  have he := Real.exp_le_exp.mpr (show -x ≤ 1 by linarith)
  linarith [Real.exp_one_lt_d9]

theorem exp_neg_change {x y : ℝ} (hx : -1 ≤ x) (hy : -1 ≤ y) :
    |Real.exp (-x)-Real.exp (-y)| ≤ 3*|x-y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.exp) (C:=3) (fun t (_ : t∈Iic (1:ℝ)) => Real.differentiableAt_exp)
    (fun t ht => by
      rw [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos t)]
      have he := Real.exp_le_exp.mpr ht
      linarith [Real.exp_one_lt_d9])
    (convex_Iic (1:ℝ)) (show -y∈Iic (1:ℝ) by change -y ≤ 1; linarith)
    (show -x∈Iic (1:ℝ) by change -x ≤ 1; linarith)
  simpa only [Real.norm_eq_abs,neg_sub_neg,abs_sub_comm y x] using h

theorem exp_neg_pair {ε x y K : ℝ} (hx : -1 ≤ x) (hy : -1 ≤ y)
    (hd : |x-y| ≤ K*ε) :
    PairedBounds ε (Real.exp (-x)) (Real.exp (-y)) 3 (3*K) := by
  refine ⟨exp_neg_bound hx,exp_neg_bound hy,?_⟩
  have h := (exp_neg_change hx hy).trans (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤3))
  nlinarith only [h]

theorem coordinate_pair {ε : ℝ} {q p : FamilyVector}
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) (i : Fin 3) : PairedBounds ε (q i) (p i) 11 1 := by
  refine ⟨abs_le.mpr ⟨by linarith [(hq i).1],(hq i).2⟩,
    abs_le.mpr ⟨by linarith [(hp i).1],(hp i).2⟩,?_⟩
  simpa only [one_mul] using hd i

theorem coordinate_exp_pair {ε : ℝ} {q p : FamilyVector}
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) (i : Fin 3) :
    PairedBounds ε (Real.exp (-q i)) (Real.exp (-p i)) 3 3 := by
  simpa only [mul_one] using exp_neg_pair (ε:=ε) (K:=1) (hq i).1 (hp i).1
    (by simpa only [one_mul] using hd i)

/-- A common coefficient bound, later discharged by the parameter certificates. -/
structure CoefficientBounds (z : ℝ) : Prop where
  c1_bound : |c1 z| ≤ 1000
  c2_bound : |c2 z| ≤ 1000
  c4_bound : |c4 z| ≤ 1000
  mu_c3_bound : |branchMu z*c3 z| ≤ 1000
  mu_c4_bound : |branchMu z*c4 z| ≤ 1000

private theorem sum_pair {ε : ℝ} {q p : FamilyVector}
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) :
    PairedBounds ε (q 0+q 1+q 2) (p 0+p 1+p 2) 33 3 := by
  convert ((coordinate_pair hq hp hd 0).add (coordinate_pair hq hp hd 1)).add
    (coordinate_pair hq hp hd 2) using 1 <;> norm_num

private theorem common_pair {ε z : ℝ} {q p : FamilyVector}
    (hc : CoefficientBounds z)
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) :
    PairedBounds ε
      (1+2*(branchMu z*c4 z)-(branchMu z*c4 z)*(q 0+q 1+q 2))
      (1+2*(branchMu z*c4 z)-(branchMu z*c4 z)*(p 0+p 1+p 2)) 35001 3000 := by
  have h1 := PairedBounds.constant (ε:=ε) (by norm_num : |(1:ℝ)|≤1)
  have h2 := PairedBounds.constant (ε:=ε) (by norm_num : |(2:ℝ)|≤2)
  have ha := PairedBounds.constant (ε:=ε) hc.mu_c4_bound
  convert (h1.add (h2.mul ha)).sub (ha.mul (sum_pair hq hp hd)) using 1 <;> norm_num

private theorem polynomial_pair {ε : ℝ} {q p : FamilyVector}
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) (i : Fin 3) :
    PairedBounds ε ((q i)^2-4*q i+2) ((p i)^2-4*p i+2) 167 26 := by
  have hq0 := coordinate_pair hq hp hd i
  have h4 := PairedBounds.constant (ε:=ε) (by norm_num : |(4:ℝ)|≤4)
  have h2 := PairedBounds.constant (ε:=ε) (by norm_num : |(2:ℝ)|≤2)
  convert ((hq0.mul hq0).sub (h4.mul hq0)).add h2 using 1 <;> norm_num [pow_two]

/-- A quantitative bound for the actual diagonal formula, uniform on the box. -/
theorem diagonal_pair {ε z : ℝ} {q p : FamilyVector}
    (hc : CoefficientBounds z)
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) (i j k : Fin 3) :
    PairedBounds ε (familyScaledDiagonal z q i j k)
      (familyScaledDiagonal z p i j k) 502009 690018 := by
  have h1 := PairedBounds.constant (ε:=ε) hc.c1_bound
  have h2 := PairedBounds.constant (ε:=ε) hc.c2_bound
  have h4 := PairedBounds.constant (ε:=ε) hc.c4_bound
  have hm := PairedBounds.constant (ε:=ε) hc.mu_c3_bound
  have ht := PairedBounds.constant (ε:=ε) (by norm_num : |(2:ℝ)|≤2)
  have hi := coordinate_pair hq hp hd i
  have hj := coordinate_exp_pair hq hp hd j
  have hk := coordinate_exp_pair hq hp hd k
  have hpoly := polynomial_pair hq hp hd i
  have hg := common_pair hc hq hp hd
  convert (((h1.add (h2.mul (ht.sub hi))).add (h4.mul hpoly)).add
    (hm.mul (hj.add hk))).add ((hj.mul hk).mul hg) using 1 <;>
    norm_num [familyScaledDiagonal, mul_assoc]

private theorem mean_exp_pair {ε : ℝ} {q p : FamilyVector}
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) (i j : Fin 3) :
    PairedBounds ε (Real.exp (-(q i+q j)/2))
      (Real.exp (-(p i+p j)/2)) 3 3 := by
  have hlq : -1 ≤ (q i+q j)/2 := by linarith [(hq i).1,(hq j).1]
  have hlp : -1 ≤ (p i+p j)/2 := by linarith [(hp i).1,(hp j).1]
  have he : (q i+q j)/2-(p i+p j)/2=((q i-p i)+(q j-p j))/2 := by ring
  have hb : |(q i+q j)/2-(p i+p j)/2| ≤ 1*ε := by
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs := abs_add_le (q i-p i) (q j-p j)
    linarith [hd i,hd j]
  convert exp_neg_pair hlq hlp hb using 1 <;> congr 2 <;> ring

/-- A quantitative bound for the actual off-diagonal formula. -/
theorem offDiagonal_pair {ε z : ℝ} {q p : FamilyVector}
    (hc : CoefficientBounds z)
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) (i j k : Fin 3) :
    PairedBounds ε (familyScaledOffDiagonal z q i j k)
      (familyScaledOffDiagonal z p i j k) 318009 660018 := by
  have hm := PairedBounds.constant (ε:=ε) hc.mu_c3_bound
  convert (mean_exp_pair hq hp hd i j).mul
    (hm.add ((coordinate_exp_pair hq hp hd k).mul (common_pair hc hq hp hd)))
    using 1 <;> norm_num [familyScaledOffDiagonal,mul_assoc]

/-- Entrywise stability of the actual scaled Hessian. All hypotheses are
explicit elementary bounds; no Hessian conclusion is assumed. -/
theorem scaled_hessian_change {ε z : ℝ} {q p : FamilyVector}
    (hε : 0≤ε) (hc : CoefficientBounds z)
    (hq : ∀i,q i∈Icc (-1:ℝ) 11) (hp : ∀i,p i∈Icc (-1:ℝ) 11)
    (hd : ∀i,|q i-p i|≤ε) (i j : Fin 3) :
    |familyHessianScaled z q i j-familyHessianScaled z p i j| ≤ 1000000*ε := by
  have hdiag (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
      |familyHessianScaled z q i i-familyHessianScaled z p i i| ≤ 1000000*ε := by
    rw [familyHessianScaled_diagonal_formula z q i j k hij hik hjk,
      familyHessianScaled_diagonal_formula z p i j k hij hik hjk]
    have h := (diagonal_pair hc hq hp hd i j k).change
    nlinarith
  have hoff (i j k : Fin 3) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
      |familyHessianScaled z q i j-familyHessianScaled z p i j| ≤ 1000000*ε := by
    rw [familyHessianScaled_offDiagonal_formula z q i j k hij hik hjk,
      familyHessianScaled_offDiagonal_formula z p i j k hij hik hjk]
    have h := (offDiagonal_pair hc hq hp hd i j k).change
    nlinarith
  fin_cases i <;> fin_cases j
  · exact hdiag 0 1 2 (by decide) (by decide) (by decide)
  · exact hoff 0 1 2 (by decide) (by decide) (by decide)
  · exact hoff 0 2 1 (by decide) (by decide) (by decide)
  · exact hoff 1 0 2 (by decide) (by decide) (by decide)
  · exact hdiag 1 0 2 (by decide) (by decide) (by decide)
  · exact hoff 1 2 0 (by decide) (by decide) (by decide)
  · exact hoff 2 0 1 (by decide) (by decide) (by decide)
  · exact hoff 2 1 0 (by decide) (by decide) (by decide)
  · exact hdiag 2 0 1 (by decide) (by decide) (by decide)

end SparseLowerTail.Certificate.HessianPerturbation

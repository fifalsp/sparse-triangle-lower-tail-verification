import SparseLowerTail.Numerics.Cholesky3
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The four lower bounds in `lem:comp-box`, with genuine segment Taylor remainders. -/
noncomputable section
namespace SparseLowerTail.Numerics
open Set

/-- The exact second order endpoint formula, obtained by applying Rolle twice.
Only the displayed first and second derivatives along the segment are needed. -/
theorem segment_taylor_exact {f f₁ f₂ : ℝ → ℝ}
    (h₁ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ t) t) :
    ∃ t ∈ Ioo (0:ℝ) 1, f 1=f 0+f₁ 0+f₂ t/2 := by
  let A := f 1-f 0-f₁ 0
  let R := fun t : ℝ => f t-f 0-f₁ 0*t-A*t^2
  let R₁ := fun t : ℝ => f₁ t-f₁ 0-2*A*t
  have hR : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt R (R₁ t) t := by
    intro t ht
    convert (((h₁ t ht).sub_const (f 0)).sub ((hasDerivAt_id t).const_mul (f₁ 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul A) using 1
    dsimp [R,R₁]
    ring
  have hR₁ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt R₁ (f₂ t-2*A) t := by
    intro t ht
    simpa [R₁] using ((h₂ t ht).sub_const (f₁ 0)).sub
      ((hasDerivAt_id t).const_mul (2*A))
  obtain ⟨u,hu,huz⟩ := exists_hasDerivAt_eq_zero zero_lt_one
    (fun t ht => (hR t ht).continuousAt.continuousWithinAt)
    (by simp [R,A]) (fun t ht => hR t (Ioo_subset_Icc_self ht))
  have hsub : Icc (0:ℝ) u ⊆ Icc (0:ℝ) 1 := fun t ht => ⟨ht.1,ht.2.trans hu.2.le⟩
  obtain ⟨t,ht,htz⟩ := exists_hasDerivAt_eq_zero hu.1
    (fun t ht => (hR₁ t (hsub ht)).continuousAt.continuousWithinAt)
    (by simpa [R₁] using huz.symm)
    (fun t ht => hR₁ t (hsub (Ioo_subset_Icc_self ht)))
  refine ⟨t,⟨ht.1,ht.2.trans hu.2⟩,?_⟩
  dsimp [A] at htz
  linarith

/-- The first order endpoint formula with a point in the open segment. -/
theorem segment_mean_exact {f f₁ : ℝ → ℝ}
    (h₁ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ t) t) :
    ∃ t ∈ Ioo (0:ℝ) 1, f 1=f 0+f₁ t := by
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope f f₁ zero_lt_one
    (fun t ht => (h₁ t ht).continuousAt.continuousWithinAt)
    (fun t ht => h₁ t (Ioo_subset_Icc_self ht))
  refine ⟨t,ht,?_⟩
  norm_num at he
  linarith

def dot3 (a b : Fin 3 → ℝ) : ℝ := a 0*b 0+a 1*b 1+a 2*b 2

def qform3 (H : Fin 6 → ℝ) (y : Fin 3 → ℝ) : ℝ := quadratic3 H (y 0) (y 1) (y 2)

def matVec3 (H : Fin 6 → ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![H 0*y 0+H 1*y 1+H 2*y 2,
    H 1*y 0+H 3*y 1+H 4*y 2,
    H 2*y 0+H 4*y 1+H 5*y 2]

/-- Magnitude of a closed interval. -/
def intervalAbs (l u : ℝ) : ℝ := max |l| |u|

theorem abs_le_intervalAbs {v l u : ℝ} (hv : v∈Icc l u) : |v| ≤ intervalAbs l u := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |l| |u|)).trans ((neg_abs_le l).trans hv.1)
  · exact hv.2.trans ((le_abs_self u).trans (le_max_right |l| |u|))

/-- A linear term is bounded by the coefficient magnitude and the radius. -/
theorem linear_radius_lower {a y r A : ℝ} (ha : |a|≤A) (hy : |y|≤r) :
    -r*A≤a*y := by
  have hr : 0≤r := (abs_nonneg y).trans hy
  have h := mul_le_mul ha hy (abs_nonneg y) ((abs_nonneg a).trans ha)
  rw [←abs_mul] at h
  nlinarith [neg_abs_le (a*y)]

/-- The negative diagonal part is the only diagonal contribution lost at a radius bound. -/
theorem diagonal_radius_lower {a l y r : ℝ} (ha : l≤a) (hy : |y|≤r) :
    min 0 l*r^2≤a*y^2 := by
  have hr : 0≤r := (abs_nonneg y).trans hy
  have hs : y^2≤r^2 := by nlinarith [abs_le.mp hy, sq_abs y]
  by_cases hl : 0≤l
  · rw [min_eq_left hl]
    simpa using mul_nonneg (hl.trans ha) (sq_nonneg y)
  · rw [min_eq_right (le_of_not_ge hl)]
    exact (mul_le_mul_of_nonpos_left hs (le_of_not_ge hl)).trans
      (mul_le_mul_of_nonneg_right ha (sq_nonneg y))

def boxLinearLoss (r A : Fin 3 → ℝ) : ℝ := r 0*A 0+r 1*A 1+r 2*A 2

def boxQuadraticLower (r : Fin 3 → ℝ) (l U : Fin 6 → ℝ) : ℝ :=
  (min 0 (l 0)*r 0^2+min 0 (l 3)*r 1^2+min 0 (l 5)*r 2^2)/2-
    (U 1*r 0*r 1+U 2*r 0*r 2+U 4*r 1*r 2)

theorem dot3_radius_lower {g y r A : Fin 3 → ℝ}
    (hg : ∀ i, |g i|≤A i) (hy : ∀ i, |y i|≤r i) :
    -boxLinearLoss r A≤dot3 g y := by
  have h0 := linear_radius_lower (hg 0) (hy 0)
  have h1 := linear_radius_lower (hg 1) (hy 1)
  have h2 := linear_radius_lower (hg 2) (hy 2)
  dsimp [dot3,boxLinearLoss]
  linarith

theorem qform3_radius_lower {H l U : Fin 6 → ℝ} {y r : Fin 3 → ℝ}
    (hl : ∀ i, l i≤H i) (hU : ∀ i, |H i|≤U i) (hy : ∀ i, |y i|≤r i) :
    boxQuadraticLower r l U≤qform3 H y/2 := by
  have hd0 := diagonal_radius_lower (hl 0) (hy 0)
  have hd1 := diagonal_radius_lower (hl 3) (hy 1)
  have hd2 := diagonal_radius_lower (hl 5) (hy 2)
  have hp01 : |y 0*y 1|≤r 0*r 1 := by
    rw [abs_mul]; exact mul_le_mul (hy 0) (hy 1) (abs_nonneg _) ((abs_nonneg _).trans (hy 0))
  have hp02 : |y 0*y 2|≤r 0*r 2 := by
    rw [abs_mul]; exact mul_le_mul (hy 0) (hy 2) (abs_nonneg _) ((abs_nonneg _).trans (hy 0))
  have hp12 : |y 1*y 2|≤r 1*r 2 := by
    rw [abs_mul]; exact mul_le_mul (hy 1) (hy 2) (abs_nonneg _) ((abs_nonneg _).trans (hy 1))
  have ho01 := linear_radius_lower (hU 1) hp01
  have ho02 := linear_radius_lower (hU 2) hp02
  have ho12 := linear_radius_lower (hU 4) hp12
  dsimp [qform3,quadratic3,boxQuadraticLower]
  nlinarith

/-- Exact supporting-plane identity for every symmetric 3×3 quadratic. -/
theorem qform3_support_identity (H : Fin 6 → ℝ) (g y z : Fin 3 → ℝ) :
    dot3 g y+qform3 H y/2=
      dot3 g z+qform3 H z/2+dot3 (g+matVec3 H z) (y-z)+qform3 H (y-z)/2 := by
  simp [dot3,qform3,quadratic3,matVec3,Pi.add_apply,Pi.sub_apply]
  ring

/-- Minimizing an affine function of one coordinate uses just its two endpoints. -/
theorem affine_endpoint_min {a y r z : ℝ} (hy : |y|≤r) :
    min (a*(-r-z)) (a*(r-z))≤a*(y-z) := by
  rcases abs_le.mp hy with ⟨hlo,hhi⟩
  by_cases ha : 0≤a
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (by linarith) ha)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left (by linarith) (le_of_not_ge ha))

def boxAffineMinimum (a r z : Fin 3 → ℝ) : ℝ :=
  min (a 0*(-r 0-z 0)) (a 0*(r 0-z 0))+
  min (a 1*(-r 1-z 1)) (a 1*(r 1-z 1))+
  min (a 2*(-r 2-z 2)) (a 2*(r 2-z 2))

def boxSupportLower (V : ℝ) (g : Fin 3 → ℝ) (H : Fin 6 → ℝ) (r z : Fin 3 → ℝ) : ℝ :=
  V+dot3 g z+qform3 H z/2+boxAffineMinimum (g+matVec3 H z) r z

theorem qform3_box_support_lower {H : Fin 6 → ℝ} {g y r z : Fin 3 → ℝ}
    (hH : ∀ v, 0≤qform3 H v) (hy : ∀ i, |y i|≤r i) (V : ℝ) :
    boxSupportLower V g H r z≤V+dot3 g y+qform3 H y/2 := by
  have h0 := affine_endpoint_min (a:=(g+matVec3 H z) 0) (z:=z 0) (hy 0)
  have h1 := affine_endpoint_min (a:=(g+matVec3 H z) 1) (z:=z 1) (hy 1)
  have h2 := affine_endpoint_min (a:=(g+matVec3 H z) 2) (z:=z 2) (hy 2)
  have he := qform3_support_identity H g y z
  have hp := hH (y-z)
  dsimp [boxSupportLower,boxAffineMinimum,dot3] at *
  linarith

/-- Positive definiteness supplies the nonnegative remainder used by the affine bound. -/
theorem qform3_nonneg_of_positive {H : Fin 6 → ℝ}
    (hH : ∀ x y z : ℝ, x≠0 ∨ y≠0 ∨ z≠0 → 0<quadratic3 H x y z)
    (v : Fin 3 → ℝ) : 0≤qform3 H v := by
  by_cases hv : v 0≠0 ∨ v 1≠0 ∨ v 2≠0
  · exact (hH _ _ _ hv).le
  · push_neg at hv
    simp [qform3,quadratic3,hv.1,hv.2.1,hv.2.2]

/-- L₀, L₁, L₂ hold without any positivity assumption on the Hessian. -/
theorem box_three_lower_bounds {f : ℝ → ℝ} {G : ℝ → Fin 3 → ℝ} {K : ℝ → Fin 6 → ℝ}
    {y r gL gU Glo Ghi : Fin 3 → ℝ} {KL KU : Fin 6 → ℝ} {V VB : ℝ}
    (h₁ : ∀ t∈Icc (0:ℝ) 1, HasDerivAt f (dot3 (G t) y) t)
    (h₂ : ∀ t∈Icc (0:ℝ) 1, HasDerivAt (fun s => dot3 (G s) y) (qform3 (K t) y) t)
    (hy : ∀ i, |y i|≤r i) (hV : V≤f 0) (hVB : VB≤f 1)
    (hg : ∀ i, G 0 i∈Icc (gL i) (gU i))
    (hG : ∀ t∈Icc (0:ℝ) 1, ∀ i, G t i∈Icc (Glo i) (Ghi i))
    (hK : ∀ t∈Icc (0:ℝ) 1, ∀ i, K t i∈Icc (KL i) (KU i))
 :
    max (max VB (V-boxLinearLoss r (fun i=>intervalAbs (Glo i) (Ghi i))))
      (V-boxLinearLoss r (fun i=>intervalAbs (gL i) (gU i))+
        boxQuadraticLower r KL (fun i=>intervalAbs (KL i) (KU i)))≤f 1 := by
  obtain ⟨t,ht,hm⟩ := segment_mean_exact h₁
  have hl := dot3_radius_lower (fun i=>abs_le_intervalAbs (hG t (Ioo_subset_Icc_self ht) i)) hy
  have hL₁ : V-boxLinearLoss r (fun i=>intervalAbs (Glo i) (Ghi i))≤f 1 := by linarith
  obtain ⟨u,hu,hT⟩ := segment_taylor_exact h₁ h₂
  have hku := hK u (Ioo_subset_Icc_self hu)
  have hlin := dot3_radius_lower (fun i=>abs_le_intervalAbs (hg i)) hy
  have hquad := qform3_radius_lower (fun i=>(hku i).1)
    (fun i=>abs_le_intervalAbs (hku i)) hy
  have hL₂ : V-boxLinearLoss r (fun i=>intervalAbs (gL i) (gU i))+
      boxQuadraticLower r KL (fun i=>intervalAbs (KL i) (KU i))≤f 1 := by linarith
  exact max_le (max_le hVB hL₁) hL₂

/-- The complete four-bound argument on a segment. Derivative hypotheses are the
ordinary gradient/Hessian chain rule, not lower bounds on the unknown function.
The final hypothesis is precisely the paper's numerical definition of L₃. -/
theorem box_lower_bounds {f : ℝ → ℝ} {G : ℝ → Fin 3 → ℝ} {K : ℝ → Fin 6 → ℝ}
    {y r gL gU Glo Ghi : Fin 3 → ℝ} {KL KU : Fin 6 → ℝ} {V VB L₃ : ℝ} {z : Fin 3 → ℝ}
    (h₁ : ∀ t∈Icc (0:ℝ) 1, HasDerivAt f (dot3 (G t) y) t)
    (h₂ : ∀ t∈Icc (0:ℝ) 1, HasDerivAt (fun s => dot3 (G s) y) (qform3 (K t) y) t)
    (hy : ∀ i, |y i|≤r i) (hV : V≤f 0) (hVB : VB≤f 1)
    (hg : ∀ i, G 0 i∈Icc (gL i) (gU i))
    (hG : ∀ t∈Icc (0:ℝ) 1, ∀ i, G t i∈Icc (Glo i) (Ghi i))
    (hK : ∀ t∈Icc (0:ℝ) 1, ∀ i, K t i∈Icc (KL i) (KU i))
    (hpositive : ∀ H : Fin 6 → ℝ, (∀ i,H i∈Icc (KL i) (KU i)) →
      ∀ x y z : ℝ, x≠0 ∨ y≠0 ∨ z≠0 → 0<quadratic3 H x y z)
    (hL₃ : ∀ g : Fin 3 → ℝ, (∀ i,g i∈Icc (gL i) (gU i)) →
      ∀ H : Fin 6 → ℝ, (∀ i,H i∈Icc (KL i) (KU i)) → L₃≤boxSupportLower V g H r z) :
    max (max VB (V-boxLinearLoss r (fun i=>intervalAbs (Glo i) (Ghi i))))
      (max (V-boxLinearLoss r (fun i=>intervalAbs (gL i) (gU i))+
        boxQuadraticLower r KL (fun i=>intervalAbs (KL i) (KU i))) L₃)≤f 1 := by
  obtain ⟨t,ht,hm⟩ := segment_mean_exact h₁
  have hl := dot3_radius_lower (fun i=>abs_le_intervalAbs (hG t (Ioo_subset_Icc_self ht) i)) hy
  have hL₁ : V-boxLinearLoss r (fun i=>intervalAbs (Glo i) (Ghi i))≤f 1 := by linarith
  obtain ⟨u,hu,hT⟩ := segment_taylor_exact h₁ h₂
  have hku := hK u (Ioo_subset_Icc_self hu)
  have hlin := dot3_radius_lower (fun i=>abs_le_intervalAbs (hg i)) hy
  have hquad := qform3_radius_lower (fun i=>(hku i).1)
    (fun i=>abs_le_intervalAbs (hku i)) hy
  have hL₂ : V-boxLinearLoss r (fun i=>intervalAbs (gL i) (gU i))+
      boxQuadraticLower r KL (fun i=>intervalAbs (KL i) (KU i))≤f 1 := by linarith
  have hs := qform3_box_support_lower
    (qform3_nonneg_of_positive (hpositive (K u) hku)) hy V (z:=z) (g:=G 0)
  have hL : L₃≤f 1 := by linarith [hL₃ (G 0) hg (K u) hku]
  exact max_le (max_le hVB hL₁) (max_le hL₂ hL)

/-- The continuous linear functional represented by three gradient coordinates. -/
def linearForm3 (g : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  g 0 • ContinuousLinearMap.proj 0+g 1 • ContinuousLinearMap.proj 1+
    g 2 • ContinuousLinearMap.proj 2

@[simp] theorem linearForm3_apply (g y : Fin 3 → ℝ) : linearForm3 g y=dot3 g y := by
  simp [linearForm3,dot3]

def hessianRow3 (H : Fin 6 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![H 0,H 1,H 2],![H 1,H 3,H 4],![H 2,H 4,H 5]]

/-- The first chain rule on the actual center-to-point segment. -/
theorem box_segment_first {Φ : (Fin 3 → ℝ) → ℝ} {G : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (c y : Fin 3 → ℝ) (t : ℝ)
    (hΦ : HasFDerivAt Φ (linearForm3 (G (c+t•y))) (c+t•y)) :
    HasDerivAt (fun s:ℝ=>Φ (c+s•y)) (dot3 (G (c+t•y)) y) t := by
  have hp : HasDerivAt (fun s:ℝ=>c+s•y) y t := by
    simpa only [zero_add,one_smul] using (hasDerivAt_const t c).add ((hasDerivAt_id t).smul_const y)
  simpa only [Function.comp_def,linearForm3_apply] using hΦ.comp_hasDerivAt t hp

/-- The second chain rule contracts the actual Hessian with the displacement twice. -/
theorem box_segment_second {G : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {K : (Fin 3 → ℝ) → Fin 6 → ℝ} (c y : Fin 3 → ℝ) (t : ℝ)
    (hG : ∀ i, HasFDerivAt (fun x=>G x i)
      (linearForm3 (hessianRow3 (K (c+t•y)) i)) (c+t•y)) :
    HasDerivAt (fun s:ℝ=>dot3 (G (c+s•y)) y) (qform3 (K (c+t•y)) y) t := by
  have hp : HasDerivAt (fun s:ℝ=>c+s•y) y t := by
    simpa only [zero_add,one_smul] using (hasDerivAt_const t c).add ((hasDerivAt_id t).smul_const y)
  have h i := (hG i).comp_hasDerivAt t hp
  simp only [Function.comp_def,linearForm3_apply] at h
  convert (((h 0).mul_const (y 0)).add ((h 1).mul_const (y 1))).add
    ((h 2).mul_const (y 2)) using 1
  simp [hessianRow3,dot3,qform3,quadratic3]
  ring

/-- `lem:comp-box` for an arbitrary convex box (and even any convex set).
`hΦ` and `hGrad` specify the actual gradient and symmetric Hessian. All interval
inputs are enclosures, and the calculus/Taylor and affine-minimization deductions
are proved above. No minimum or function-value conclusion is assumed. -/
theorem box_lower_bounds_on_box
    {Φ : (Fin 3 → ℝ) → ℝ} {G : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {K : (Fin 3 → ℝ) → Fin 6 → ℝ} {B : Set (Fin 3 → ℝ)}
    {c q r gL gU Glo Ghi : Fin 3 → ℝ} {KL KU : Fin 6 → ℝ}
    {V VB L₃ : ℝ} {z : Fin 3 → ℝ}
    (hB : Convex ℝ B) (hc : c∈B) (hq : q∈B)
    (hΦ : ∀ x∈B, HasFDerivAt Φ (linearForm3 (G x)) x)
    (hGrad : ∀ x∈B, ∀ i, HasFDerivAt (fun w=>G w i) (linearForm3 (hessianRow3 (K x) i)) x)
    (hr : ∀ i, |q i-c i|≤r i) (hV : V≤Φ c) (hVB : ∀ x∈B, VB≤Φ x)
    (hg : ∀ i,G c i∈Icc (gL i) (gU i))
    (hG : ∀ x∈B, ∀ i,G x i∈Icc (Glo i) (Ghi i))
    (hK : ∀ x∈B, ∀ i,K x i∈Icc (KL i) (KU i))
    (hpositive : ∀ H : Fin 6 → ℝ, (∀ i,H i∈Icc (KL i) (KU i)) →
      ∀ x y z : ℝ, x≠0 ∨ y≠0 ∨ z≠0 → 0<quadratic3 H x y z)
    (hL₃ : ∀ g : Fin 3 → ℝ, (∀ i,g i∈Icc (gL i) (gU i)) →
      ∀ H : Fin 6 → ℝ, (∀ i,H i∈Icc (KL i) (KU i)) → L₃≤boxSupportLower V g H r z) :
    max (max VB (V-boxLinearLoss r (fun i=>intervalAbs (Glo i) (Ghi i))))
      (max (V-boxLinearLoss r (fun i=>intervalAbs (gL i) (gU i))+
        boxQuadraticLower r KL (fun i=>intervalAbs (KL i) (KU i))) L₃)≤Φ q := by
  have hseg (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : c+t•(q-c)∈B :=
    hB.add_smul_mem hc (by simpa using hq) ht
  have h := box_lower_bounds (f:=fun t:ℝ=>Φ (c+t•(q-c)))
    (G:=fun t:ℝ=>G (c+t•(q-c))) (K:=fun t:ℝ=>K (c+t•(q-c)))
    (y:=q-c) (z:=z)
    (fun t ht=>box_segment_first c (q-c) t (hΦ _ (hseg t ht)))
    (fun t ht=>box_segment_second c (q-c) t (hGrad _ (hseg t ht)))
    hr (by simpa using hV) (by simpa using hVB q hq)
    (by simpa using hg) (fun t ht=>hG _ (hseg t ht))
    (fun t ht=>hK _ (hseg t ht)) hpositive hL₃
  simpa using h

/-- The same actual-function theorem when no positive-definite Hessian enclosure
is available: retain the three unconditional bounds. This is the L₃=-∞ branch. -/
theorem box_three_lower_bounds_on_box
    {Φ : (Fin 3 → ℝ) → ℝ} {G : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {K : (Fin 3 → ℝ) → Fin 6 → ℝ} {B : Set (Fin 3 → ℝ)}
    {c q r gL gU Glo Ghi : Fin 3 → ℝ} {KL KU : Fin 6 → ℝ}
    {V VB : ℝ}
    (hB : Convex ℝ B) (hc : c∈B) (hq : q∈B)
    (hΦ : ∀ x∈B, HasFDerivAt Φ (linearForm3 (G x)) x)
    (hGrad : ∀ x∈B, ∀ i, HasFDerivAt (fun w=>G w i) (linearForm3 (hessianRow3 (K x) i)) x)
    (hr : ∀ i, |q i-c i|≤r i) (hV : V≤Φ c) (hVB : ∀ x∈B, VB≤Φ x)
    (hg : ∀ i,G c i∈Icc (gL i) (gU i))
    (hG : ∀ x∈B, ∀ i,G x i∈Icc (Glo i) (Ghi i))
    (hK : ∀ x∈B, ∀ i,K x i∈Icc (KL i) (KU i)) :
    max (max VB (V-boxLinearLoss r (fun i=>intervalAbs (Glo i) (Ghi i))))
      (V-boxLinearLoss r (fun i=>intervalAbs (gL i) (gU i))+
        boxQuadraticLower r KL (fun i=>intervalAbs (KL i) (KU i)))≤Φ q := by
  have hseg (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : c+t•(q-c)∈B :=
    hB.add_smul_mem hc (by simpa using hq) ht
  have h := box_three_lower_bounds (f:=fun t:ℝ=>Φ (c+t•(q-c)))
    (G:=fun t:ℝ=>G (c+t•(q-c))) (K:=fun t:ℝ=>K (c+t•(q-c)))
    (y:=q-c)
    (fun t ht=>box_segment_first c (q-c) t (hΦ _ (hseg t ht)))
    (fun t ht=>box_segment_second c (q-c) t (hGrad _ (hseg t ht)))
    hr (by simpa using hV) (by simpa using hVB q hq)
    (by simpa using hg) (fun t ht=>hG _ (hseg t ht))
    (fun t ht=>hK _ (hseg t ht))
  simpa using h

end SparseLowerTail.Numerics

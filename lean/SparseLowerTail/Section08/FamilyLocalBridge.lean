import SparseLowerTail.Section08.FamilyLocalFormula

/-! A local Hessian certificate implies nonnegativity and an exact contact
zero. The Hessian input is an explicit matrix inequality, never the desired
positivity conclusion. -/
noncomputable section
open Set
namespace SparseLowerTail.Certificate
open Numerics

/-- Strictly positive second derivative and zero first derivative at the
contact give strict positivity at the other endpoint. -/
theorem segment_strict_contact {f f₁ f₂ : ℝ→ℝ}
    (h₁ : ∀s∈Icc (0:ℝ) 1, HasDerivAt f (f₁ s) s)
    (h₂ : ∀s∈Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ s) s)
    (hpos : ∀s∈Ioo (0:ℝ) 1,0<f₂ s)
    (hf : f 0=0) (hg : f₁ 0=0) : 0<f 1 := by
  have hm : StrictMonoOn f₁ (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s hs; exact (h₂ s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(h₂ s ⟨hs.1.le,hs.2.le⟩).deriv]
      exact hpos s hs
  have hfmono : StrictMonoOn f (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s hs; exact (h₁ s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(h₁ s ⟨hs.1.le,hs.2.le⟩).deriv]
      have hh := hm (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) ⟨hs.1.le,hs.2.le⟩ hs.1
      simpa only [hg] using hh
  have hh := hfmono (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) zero_lt_one
  simpa only [hf] using hh

def familyHessianForm (z : ℝ) (q v : FamilyVector) : ℝ :=
  sumThree (fun i => sumThree (fun j => v i*v j*familyHessian z q i j))

def familyNormSq (v : FamilyVector) : ℝ := sumThree (fun i => (v i)^2)

theorem familyHessianForm_segment_deriv (z : ℝ) (p v : FamilyVector) (s : ℝ) :
    HasDerivAt (fun t => sumThree (fun i => v i*familyGradient z (familySegment p v t) i))
      (familyHessianForm z (familySegment p v s) v) s := by
  have h0 := (familyGradient_segment_deriv z p v s 0).const_mul (v 0)
  have h1 := (familyGradient_segment_deriv z p v s 1).const_mul (v 1)
  have h2 := (familyGradient_segment_deriv z p v s 2).const_mul (v 2)
  convert (h0.add h1).add h2 using 1
  simp only [sumThree,familyHessianForm]
  ring

theorem familySegment_mem_convex {S : Set FamilyVector} (hS : Convex ℝ S)
    {p q : FamilyVector} (hp : p∈S) (hq : q∈S) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    familySegment p (q-p) s∈S := by
  have hh := hS hp hq (show 0≤1-s by linarith [hs.2]) hs.1 (by ring : (1-s)+s=1)
  convert hh using 1
  funext i
  simp only [familySegment,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

@[simp] theorem familySegment_zero (p v : FamilyVector) : familySegment p v 0=p := by
  funext i
  simp [familySegment]

@[simp] theorem familySegment_sub_one (p q : FamilyVector) : familySegment p (q-p) 1=q := by
  funext i
  simp [familySegment]

/-- Exact-zero bridge for the actual logarithmic family certificate on any
convex domain. Its numerical input is only positive definiteness of the
explicit Hessian throughout that domain. -/
theorem familyPhi_local_nonneg_zero_iff {z : ℝ} {S : Set FamilyVector}
    (hS : Convex ℝ S) {p : FamilyVector} (hp : p∈S)
    (hval : familyPhi z p=0) (hgrad : ∀i,familyGradient z p i=0)
    (hH : ∀q∈S,∀v : FamilyVector,v≠0 → 0<familyHessianForm z q v)
    {q : FamilyVector} (hq : q∈S) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=p) := by
  by_cases he : q=p
  · subst q
    simp [hval]
  have hv : q-p≠0 := sub_ne_zero.mpr he
  have hf := segment_strict_contact
    (f := fun s => familyPhi z (familySegment p (q-p) s))
    (f₁ := fun s => sumThree (fun i => (q-p) i*familyGradient z (familySegment p (q-p) s) i))
    (f₂ := fun s => familyHessianForm z (familySegment p (q-p) s) (q-p))
    (fun s _ => familyPhi_segment_deriv z p (q-p) s)
    (fun s _ => familyHessianForm_segment_deriv z p (q-p) s)
    (fun s hs => hH _ (familySegment_mem_convex hS hp hq ⟨hs.1.le,hs.2.le⟩) _ hv)
    (by simpa using hval) (by simp [hgrad,sumThree])
  simp only [familySegment_sub_one] at hf
  exact ⟨hf.le,⟨fun hh => (ne_of_gt hf hh).elim,fun hh => (he hh).elim⟩⟩

/-- Quantitative version for a uniform Hessian margin η. -/
theorem familyPhi_local_quadratic_lower {z η : ℝ} {S : Set FamilyVector}
    (hS : Convex ℝ S) {p : FamilyVector} (hp : p∈S)
    (hval : familyPhi z p=0) (hgrad : ∀i,familyGradient z p i=0)
    (hH : ∀q∈S,∀v : FamilyVector,η*familyNormSq v≤familyHessianForm z q v)
    {q : FamilyVector} (hq : q∈S) :
    η*familyNormSq (q-p)/2≤familyPhi z q := by
  have hf := segment_taylor_lower
    (f := fun s => familyPhi z (familySegment p (q-p) s))
    (f₁ := fun s => sumThree (fun i => (q-p) i*familyGradient z (familySegment p (q-p) s) i))
    (f₂ := fun s => familyHessianForm z (familySegment p (q-p) s) (q-p))
    (M := -(η*familyNormSq (q-p)))
    (fun s _ => familyPhi_segment_deriv z p (q-p) s)
    (fun s _ => familyHessianForm_segment_deriv z p (q-p) s)
    (fun s hs => by simpa only [neg_neg] using hH _ (familySegment_mem_convex hS hp hq hs) (q-p))
  simpa [hval,hgrad,sumThree,neg_div] using hf

end SparseLowerTail.Certificate

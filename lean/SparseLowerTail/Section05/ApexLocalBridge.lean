import SparseLowerTail.Section05.ApexCalculus

/-! Local convexity bridge for the actual critical-apex certificate. Exact
contact values and gradients and checked Hessian positivity are explicit inputs.
Numerical certificate obligations are not asserted in this module. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05
open Numerics Certificate

def apexHessianForm (θ : Fin 12 → ℝ) (lam : ℝ) (q v : ApexVector) : ℝ :=
  sumThree (fun i => sumThree (fun j => v i*v j*apexHessian θ lam q i j))

def apexNormSq (v : ApexVector) : ℝ := sumThree (fun i => (v i)^2)

theorem apexHessianForm_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ) (p v : ApexVector) (s : ℝ) :
    HasDerivAt (fun t => sumThree (fun i => v i*apexGradient θ lam (familySegment p v t) i))
      (apexHessianForm θ lam (familySegment p v s) v) s := by
  have h0 := (apexGradient_segment_deriv θ lam p v s 0).const_mul (v 0)
  have h1 := (apexGradient_segment_deriv θ lam p v s 1).const_mul (v 1)
  have h2 := (apexGradient_segment_deriv θ lam p v s 2).const_mul (v 2)
  convert (h0.add h1).add h2 using 1
  simp only [sumThree,apexHessianForm]
  ring

/-- Exact-zero bridge for the actual logarithmic apex certificate on any
convex domain. Its numerical input is only positive definiteness of the
explicit Hessian throughout that domain. -/
theorem apexPhi_local_nonneg_zero_iff {θ : Fin 12 → ℝ} {lam : ℝ} {S : Set ApexVector}
    (hS : Convex ℝ S) {p : ApexVector} (hp : p∈S)
    (hval : apexPhi θ lam p=0) (hgrad : ∀i,apexGradient θ lam p i=0)
    (hH : ∀q∈S,∀v : ApexVector,v≠0 → 0<apexHessianForm θ lam q v)
    {q : ApexVector} (hq : q∈S) :
    0≤apexPhi θ lam q ∧ (apexPhi θ lam q=0 ↔ q=p) := by
  by_cases he : q=p
  · subst q
    simp [hval]
  have hv : q-p≠0 := sub_ne_zero.mpr he
  have hf := segment_strict_contact
    (f := fun s => apexPhi θ lam (familySegment p (q-p) s))
    (f₁ := fun s => sumThree (fun i => (q-p) i*apexGradient θ lam (familySegment p (q-p) s) i))
    (f₂ := fun s => apexHessianForm θ lam (familySegment p (q-p) s) (q-p))
    (fun s _ => apexPhi_segment_deriv θ lam p (q-p) s)
    (fun s _ => apexHessianForm_segment_deriv θ lam p (q-p) s)
    (fun s hs => hH _ (familySegment_mem_convex hS hp hq ⟨hs.1.le,hs.2.le⟩) _ hv)
    (by simpa using hval) (by simp [hgrad,sumThree])
  simp only [familySegment_sub_one] at hf
  exact ⟨hf.le,⟨fun hh => (ne_of_gt hf hh).elim,fun hh => (he hh).elim⟩⟩

/-- Quantitative version for a uniform Hessian margin η. -/
theorem apexPhi_local_quadratic_lower {θ : Fin 12 → ℝ} {lam η : ℝ} {S : Set ApexVector}
    (hS : Convex ℝ S) {p : ApexVector} (hp : p∈S)
    (hval : apexPhi θ lam p=0) (hgrad : ∀i,apexGradient θ lam p i=0)
    (hH : ∀q∈S,∀v : ApexVector,η*apexNormSq v≤apexHessianForm θ lam q v)
    {q : ApexVector} (hq : q∈S) :
    η*apexNormSq (q-p)/2≤apexPhi θ lam q := by
  have hf := segment_taylor_lower
    (f := fun s => apexPhi θ lam (familySegment p (q-p) s))
    (f₁ := fun s => sumThree (fun i => (q-p) i*apexGradient θ lam (familySegment p (q-p) s) i))
    (f₂ := fun s => apexHessianForm θ lam (familySegment p (q-p) s) (q-p))
    (M := -(η*apexNormSq (q-p)))
    (fun s _ => apexPhi_segment_deriv θ lam p (q-p) s)
    (fun s _ => apexHessianForm_segment_deriv θ lam p (q-p) s)
    (fun s hs => by simpa only [neg_neg] using hH _ (familySegment_mem_convex hS hp hq hs) (q-p))
  simpa [hval,hgrad,sumThree,neg_div] using hf

end SparseLowerTail.Section05

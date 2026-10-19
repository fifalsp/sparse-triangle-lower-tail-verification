import SparseLowerTail.Section08.FamilyLocalBridge

/-! The two actual contact points have zero value and gradient. Together
with a replayed Hessian bound, this proves the local part of appA3:compact. -/
noncomputable section
open Set
namespace SparseLowerTail.Certificate
open Section04

def familyContactAAA (z : ℝ) : FamilyVector := fun _ => qA z

def familyContactABB (z : ℝ) : FamilyVector :=
  ![qA z,-Real.log (branchB z),-Real.log (branchB z)]

theorem phiDerivative_chain_rule (z u v w : ℝ) :
    phiDerivative z u v w= -Real.exp (-u)*
      psiDerivativeX z (Real.exp (-u)) (Real.exp (-v)) (Real.exp (-w)) := by
  unfold phiDerivative psiDerivativeX potentialDerivative
  simp only [Real.log_exp]
  field_simp [(Real.exp_pos (-u)).ne']
  ring

theorem familyContactAAA_value {z : ℝ} (hz : 0<z) (hz1 : z<1)
    (hg : gamma z (branchLog z)≠0) : familyPhi z (familyContactAAA z)=0 := by
  simpa only [familyPhi,familyContactAAA,phi,qA,neg_neg,Real.exp_log (branchA_pos hz)]
    using psi_aaa hz hz1 hg

theorem familyContactABB_value {z : ℝ} (hz : 0<z) (hz1 : z<1)
    (hg : gamma z (branchLog z)≠0) : familyPhi z (familyContactABB z)=0 := by
  simpa only [familyPhi,familyContactABB,phi,qA,Matrix.cons_val,neg_neg,
    Real.exp_log (branchA_pos hz),Real.exp_log (branchB_pos z)] using psi_abb hz hz1 hg

theorem familyContactAAA_gradient {z : ℝ} (hz : 0<z) (hz1 : z<1)
    (hg : gamma z (branchLog z)≠0) : ∀i,familyGradient z (familyContactAAA z) i=0 := by
  intro i
  rw [familyGradient_formula]
  fin_cases i <;>
    simp only [familyContactAAA,phiDerivative_chain_rule,qA,neg_neg,
      Real.exp_log (branchA_pos hz),psiDerivativeX_aaa hz hz1 hg,mul_zero] <;> rfl

theorem familyContactABB_gradient {z : ℝ} (hz : 0<z) (hz1 : z<1)
    (hg : gamma z (branchLog z)≠0) : ∀i,familyGradient z (familyContactABB z) i=0 := by
  intro i
  rw [familyGradient_formula]
  fin_cases i <;>
    simp only [familyContactABB,Matrix.cons_val,phiDerivative_chain_rule,qA,neg_neg,
      Real.exp_log (branchA_pos hz),Real.exp_log (branchB_pos z),
      psiDerivativeX_abb hz hz1 hg,psiDerivativeX_bab hz hz1 hg,mul_zero] <;> rfl

/-- Closed cube in logarithmic coordinates. -/
def familyCube (p : FamilyVector) (δ : ℝ) : Set FamilyVector :=
  {q | ∀i,|q i-p i|≤δ}

theorem familyCube_convex (p : FamilyVector) (δ : ℝ) : Convex ℝ (familyCube p δ) := by
  intro x hx y hy a b ha hb hab i
  change |a*x i+b*y i-p i|≤δ
  have he : a*x i+b*y i-p i=a*(x i-p i)+b*(y i-p i) := by
    have hh := congrArg (fun t : ℝ => t*p i) hab
    nlinarith only [hh]
  rw [he]
  have h1 := abs_add_le (a*(x i-p i)) (b*(y i-p i))
  rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] at h1
  have h2 := mul_le_mul_of_nonneg_left (hx i) ha
  have h3 := mul_le_mul_of_nonneg_left (hy i) hb
  have hh := congrArg (fun t : ℝ => t*δ) hab
  nlinarith only [h1,h2,h3,hh]

/-- Local all-a zero, conditional only on the explicit Hessian certificate. -/
theorem familyContactAAA_local {z δ : ℝ} (hz : 0<z) (hz1 : z<1)
    (hg : gamma z (branchLog z)≠0) (hδ : 0≤δ)
    (hH : ∀q∈familyCube (familyContactAAA z) δ,∀v : FamilyVector,
      v≠0 → 0<familyHessianForm z q v)
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) δ) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactAAA z) := by
  exact familyPhi_local_nonneg_zero_iff (familyCube_convex _ _)
    (by intro i; simpa using hδ) (familyContactAAA_value hz hz1 hg)
    (familyContactAAA_gradient hz hz1 hg) hH hq

/-- Local mixed zero, conditional only on the explicit Hessian certificate. -/
theorem familyContactABB_local {z δ : ℝ} (hz : 0<z) (hz1 : z<1)
    (hg : gamma z (branchLog z)≠0) (hδ : 0≤δ)
    (hH : ∀q∈familyCube (familyContactABB z) δ,∀v : FamilyVector,
      v≠0 → 0<familyHessianForm z q v)
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z) δ) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) := by
  exact familyPhi_local_nonneg_zero_iff (familyCube_convex _ _)
    (by intro i; simpa using hδ) (familyContactABB_value hz hz1 hg)
    (familyContactABB_gradient hz hz1 hg) hH hq

end SparseLowerTail.Certificate

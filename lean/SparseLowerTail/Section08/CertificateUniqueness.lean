import SparseLowerTail.Section08.CertificateSigns
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The determinant and uniqueness calculation in the proof of `lem:certcoef`. -/
noncomputable section
namespace SparseLowerTail.Certificate
open Section04
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def contactMatrix (z L : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let M := multiplier z L
  let a := logA z L
  let b := logB z L
  !![z-mean z, z*a+M*density z, a+M*z^2, z*a*(a+M*z^2);
     1, 1+a, 1/z+2*M*z, a^2+2*a+M*z^2*(1+3*a);
     1, 1+a, 1/z+2*M, a^2+2*a+M*(1+a+2*b);
     1, 1+b, 1+M*(z+1), b^2+2*b+M*z*(1+a+2*b)]

def contactRhs (z:ℝ) : Fin 4 → ℝ := ![(density z-z^3)/3,-z^2,-1,-z]
def contactCoefficients (z L:ℝ) : Fin 4 → ℝ := ![d1 z L,d2 z L,d3 z L,d4 z L]

/-- Polynomial coordinates avoid repeated rational denominators in the determinant calculation. -/
def contactMatrixParam (z M:ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let a:= -M*(1+z^2)/2
  let b:= -M*z
  !![z-mean z, z*a+M*density z, a+M*z^2, z*a*(a+M*z^2);
     1, 1+a, 1/z+2*M*z, a^2+2*a+M*z^2*(1+3*a);
     1, 1+a, 1/z+2*M, a^2+2*a+M*(1+a+2*b);
     1, 1+b, 1+M*(z+1), b^2+2*b+M*z*(1+a+2*b)]

theorem contactMatrix_eq_param (z L:ℝ) :
    contactMatrix z L=contactMatrixParam z (multiplier z L) := by
  have ha:logA z L= -multiplier z L*(1+z^2)/2 := by unfold logA multiplier;ring
  have hb:logB z L= -multiplier z L*z := by unfold logB multiplier;ring
  simp only [contactMatrix,contactMatrixParam,ha,hb]

theorem contactMatrixParam_det (z M:ℝ) (hz:z≠0) :
    (contactMatrixParam z M).det= -M*(z+1)*gamma z (M*(1-z)^2/2)/(2*z) := by
  have h00 : ((0:Fin 4)).succAbove (0:Fin 3) = 1 := by decide
  have h01 : ((0:Fin 4)).succAbove (1:Fin 3) = 2 := by decide
  have h02 : ((0:Fin 4)).succAbove (2:Fin 3) = 3 := by decide
  have h10 : ((1:Fin 4)).succAbove (0:Fin 3) = 0 := by decide
  have h11 : ((1:Fin 4)).succAbove (1:Fin 3) = 2 := by decide
  have h12 : ((1:Fin 4)).succAbove (2:Fin 3) = 3 := by decide
  have h20 : ((2:Fin 4)).succAbove (0:Fin 3) = 0 := by decide
  have h21 : ((2:Fin 4)).succAbove (1:Fin 3) = 1 := by decide
  have h22 : ((2:Fin 4)).succAbove (2:Fin 3) = 3 := by decide
  have h30 : ((3:Fin 4)).succAbove (0:Fin 3) = 0 := by decide
  have h31 : ((3:Fin 4)).succAbove (1:Fin 3) = 1 := by decide
  have h32 : ((3:Fin 4)).succAbove (2:Fin 3) = 2 := by decide
  have hs : (2:Fin 3).succ = (3:Fin 4) := by decide
  rw [Matrix.det_succ_row_zero]
  norm_num [contactMatrixParam,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,
    h00,h01,h02,h10,h11,h12,h20,h21,h22,h30,h31,h32,hs,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail]
  unfold mean density gamma
  ring_nf
  field_simp [hz]
  ring

/-- The exact determinant printed after dividing the value equation by 3b³. -/
theorem contactMatrix_det (z L:ℝ) (hz:z≠0) (h1:1-z≠0) :
    (contactMatrix z L).det= -L*(z+1)*gamma z L/(z*(z-1)^2) := by
  have hz1:z-1≠0 := by intro h;apply h1;linarith
  rw [contactMatrix_eq_param,contactMatrixParam_det z _ hz]
  have hL:multiplier z L*(1-z)^2/2=L := by unfold multiplier;field_simp
  rw [hL]
  unfold multiplier
  field_simp [hz,h1,hz1]
  ring

/-- The published rational coefficients solve the actual four-by-four system. -/
theorem contactCoefficients_solve (z L:ℝ) (hz:z≠0) (h1:1-z≠0)
    (hp:z+1≠0) (hL:L≠0) (hg:gamma z L≠0) :
    (contactMatrix z L).mulVec (contactCoefficients z L)=contactRhs z := by
  ext i
  fin_cases i
  · have h:=value_aaa z L h1 hp hg
    dsimp [s,d0] at h
    simp [contactMatrix,contactCoefficients,contactRhs,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    nlinarith
  · have h:=gradient_aaa z L hz h1 hp hL hg
    dsimp [sd] at h
    simp only [div_eq_mul_inv] at h
    simp [contactMatrix,contactCoefficients,contactRhs,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    nlinarith
  · have h:=gradient_abb_a z L hz h1 hp hL hg
    dsimp [sd] at h
    simp only [div_eq_mul_inv] at h
    simp [contactMatrix,contactCoefficients,contactRhs,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    nlinarith
  · have h:=gradient_abb_b z L h1 hp hL hg
    dsimp [sd] at h
    simp only [div_eq_mul_inv] at h
    simp [contactMatrix,contactCoefficients,contactRhs,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    nlinarith

/-- Nonvanishing of the determinant gives uniqueness for all independent z,L. -/
theorem contactCoefficients_unique (z L:ℝ) (hz:z≠0) (h1:1-z≠0)
    (hp:z+1≠0) (hL:L≠0) (hg:gamma z L≠0) (v:Fin 4→ℝ)
    (hv:(contactMatrix z L).mulVec v=contactRhs z) : v=contactCoefficients z L := by
  have hd:(contactMatrix z L).det≠0 := by
    rw [contactMatrix_det z L hz h1]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hL) hp) hg)
      (mul_ne_zero hz (pow_ne_zero 2 (by intro h;apply h1;linarith)))
  have hu:IsUnit (contactMatrix z L) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  exact (Matrix.mulVec_injective_iff_isUnit.mpr hu)
    (hv.trans (contactCoefficients_solve z L hz h1 hp hL hg).symm)

/-- The four normalized value/derivative residuals before solving for d₁,…,d₄. -/
def contactResidual (z L:ℝ) (v:Fin 4→ℝ) : Fin 4→ℝ :=
  let M:=multiplier z L
  let a:=logA z L
  let b:=logB z L
  let c:= -v 0*mean z+v 1*M*density z-density z/3
  let S:=fun u ell:ℝ=>c+v 0*u+v 1*u*ell+v 2*ell+v 3*u*ell^2
  let D:=fun u ell:ℝ=>v 0+v 1*(1+ell)+v 2/u+v 3*(ell^2+2*ell)
  ![S z a+M*v 2*z^2+z^3/3*(1+3*M*v 3*a),
    D z a+2*M*v 2*z+z^2*(1+M*v 3+3*M*v 3*a),
    D z a+2*M*v 2+1+M*v 3*(1+a+2*b),
    D 1 b+M*v 2*(z+1)+z*(1+M*v 3*(1+a+2*b))]

/-- The residuals are exactly the stated linear system, not extra hypotheses. -/
theorem contactResidual_eq (z L:ℝ) (v:Fin 4→ℝ) :
    contactResidual z L v=(contactMatrix z L).mulVec v-contactRhs z := by
  ext i
  fin_cases i <;> simp [contactResidual,contactMatrix,contactRhs,dotProduct,
    Fin.sum_univ_succ,div_eq_mul_inv] <;> ring

/-- Existence and uniqueness for the four normalized tangency equations. -/
theorem contactResidual_exists_unique (z L:ℝ) (hz:z≠0) (h1:1-z≠0)
    (hp:z+1≠0) (hL:L≠0) (hg:gamma z L≠0) :
    ∃! v:Fin 4→ℝ,contactResidual z L v=0 := by
  refine ⟨contactCoefficients z L,?_,?_⟩
  · change contactResidual z L (contactCoefficients z L)=0
    rw [contactResidual_eq,contactCoefficients_solve z L hz h1 hp hL hg,sub_self]
  · intro v hv
    rw [contactResidual_eq] at hv
    exact contactCoefficients_unique z L hz h1 hp hL hg v (sub_eq_zero.mp hv)

/-- All nonvanishing conditions are discharged on the manuscript's stated interval. -/
theorem branch_contactResidual_exists_unique {z:ℝ} (hz:0<z) (hz40:z≤1/40) :
    ∃! v:Fin 4→ℝ,contactResidual z (branchLog z) v=0 := by
  have hz1:z<1 := by linarith
  exact contactResidual_exists_unique z (branchLog z) hz.ne' (sub_pos.mpr hz1).ne'
    (by positivity) (branchLog_pos hz hz1).ne' (gamma_branch_neg hz hz40).ne

/-- The normalized certificate with arbitrary unknown coefficients and actual logarithms. -/
def unknownPotential (z : ℝ) (v : Fin 4 → ℝ) (u : ℝ) : ℝ :=
  -v 0*mean z+v 1*multiplier z (branchLog z)*density z-density z/3+
    v 0*u+v 1*u*Real.log (branchB z*u)+v 2*Real.log (branchB z*u)+
    v 3*u*(Real.log (branchB z*u))^2

def unknownPotentialDerivative (z : ℝ) (v : Fin 4 → ℝ) (u : ℝ) : ℝ :=
  v 0+v 1*(1+Real.log (branchB z*u))+v 2/u+
    v 3*((Real.log (branchB z*u))^2+2*Real.log (branchB z*u))

theorem hasDerivAt_unknownPotential (z : ℝ) (v : Fin 4 → ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (unknownPotential z v) (unknownPotentialDerivative z v u) u := by
  have hb := (branchB_pos z).ne'
  have hid := hasDerivAt_id u
  have hl : HasDerivAt (fun t : ℝ => Real.log (branchB z*t)) (1/u) u := by
    convert (Real.hasDerivAt_log (mul_ne_zero hb hu)).comp u (hid.const_mul (branchB z)) using 1
    field_simp
  have hd := ((((hasDerivAt_const u
    (-v 0*mean z+v 1*multiplier z (branchLog z)*density z-density z/3)).add
      (hid.const_mul (v 0))).add ((hid.const_mul (v 1)).mul hl)).add
      (hl.const_mul (v 2))).add ((hid.const_mul (v 3)).mul (hl.pow 2))
  convert hd using 1
  dsimp [unknownPotentialDerivative]
  field_simp
  ring

def unknownPsi (z : ℝ) (v : Fin 4 → ℝ) (x y w : ℝ) : ℝ :=
  unknownPotential z v x+unknownPotential z v y+unknownPotential z v w+
    multiplier z (branchLog z)*v 2*(x*y+y*w+w*x)+
    x*y*w*(1+multiplier z (branchLog z)*v 3*
      (Real.log (branchB z*x)+Real.log (branchB z*y)+Real.log (branchB z*w)))

def unknownPsiDerivative (z : ℝ) (v : Fin 4 → ℝ) (x y w : ℝ) : ℝ :=
  unknownPotentialDerivative z v x+multiplier z (branchLog z)*v 2*(y+w)+
    y*w*(1+multiplier z (branchLog z)*v 3*
      (1+Real.log (branchB z*x)+Real.log (branchB z*y)+Real.log (branchB z*w)))

theorem hasDerivAt_unknownPsi (z : ℝ) (v : Fin 4 → ℝ) (y w : ℝ)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u => unknownPsi z v u y w) (unknownPsiDerivative z v x y w) x := by
  have hb := (branchB_pos z).ne'
  have hid := hasDerivAt_id x
  have hl : HasDerivAt (fun t : ℝ => Real.log (branchB z*t)) (1/x) x := by
    convert (Real.hasDerivAt_log (mul_ne_zero (branchB_pos z).ne' hx)).comp x
      (hid.const_mul (branchB z)) using 1
    field_simp [hb]
  have hp := (((hasDerivAt_unknownPotential z v hx).add_const
    (unknownPotential z v y)).add_const (unknownPotential z v w)).add
    ((((hid.mul_const y).add_const (y*w)).add (hid.const_mul w)).const_mul
      (multiplier z (branchLog z)*v 2))
  have hq := ((hid.mul_const y).mul_const w).mul
    (((hl.add_const (Real.log (branchB z*y))).add_const (Real.log (branchB z*w))).const_mul
      (multiplier z (branchLog z)*v 3) |>.const_add 1)
  convert hp.add hq using 1
  dsimp [unknownPsi,unknownPsiDerivative]
  field_simp
  ring

/-- The four residuals are values and genuine partial derivatives of the unsolved certificate. -/
theorem contactResidual_eq_actual {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (v : Fin 4 → ℝ) :
    contactResidual z (branchLog z) v =
      ![unknownPsi z v z z z/3,
        deriv (fun u => unknownPsi z v u z z) z,
        deriv (fun u => unknownPsi z v u 1 1) z,
        deriv (fun u => unknownPsi z v u z 1) 1] := by
  have ha : Real.log (branchB z*z)=logA z (branchLog z) := by
    simpa [branchA,mul_comm] using branch_logA hz hz1
  rw [(hasDerivAt_unknownPsi z v z z hz.ne').deriv,
      (hasDerivAt_unknownPsi z v 1 1 hz.ne').deriv,
      (hasDerivAt_unknownPsi z v z 1 (by norm_num : (1:ℝ)≠0)).deriv]
  ext i
  fin_cases i <;> dsimp only [contactResidual,unknownPsi,unknownPotential,
    unknownPsiDerivative,unknownPotentialDerivative] <;>
    simp only [mul_one,ha,branch_logB,div_one] <;> ring

/-- Specializing the unknowns recovers the previously defined normalized certificate. -/
theorem unknownPsi_coefficients (z x y w : ℝ) :
    unknownPsi z (contactCoefficients z (branchLog z)) x y w=normalizedPsi z x y w := by
  simp [unknownPsi,unknownPotential,contactCoefficients,normalizedPsi,s,d0]

/-- The actual normalized tangency problem has exactly the published coefficients as solution. -/
theorem branch_actual_tangency_iff {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40)
    (v : Fin 4 → ℝ) :
    (unknownPsi z v z z z=0 ∧
      deriv (fun u => unknownPsi z v u z z) z=0 ∧
      deriv (fun u => unknownPsi z v u 1 1) z=0 ∧
      deriv (fun u => unknownPsi z v u z 1) 1=0) ↔
      v=contactCoefficients z (branchLog z) := by
  have hz1 : z < 1 := by linarith
  have hr : contactResidual z (branchLog z) v=0 ↔
      (unknownPsi z v z z z=0 ∧
      deriv (fun u => unknownPsi z v u z z) z=0 ∧
      deriv (fun u => unknownPsi z v u 1 1) z=0 ∧
      deriv (fun u => unknownPsi z v u z 1) 1=0) := by
    rw [contactResidual_eq_actual hz hz1]
    simp [funext_iff,Fin.forall_fin_succ]
  rw [← hr]
  constructor
  · intro hv
    exact (branch_contactResidual_exists_unique hz hz40).unique hv
      (by rw [contactResidual_eq,contactCoefficients_solve z (branchLog z) hz.ne'
            (sub_pos.mpr hz1).ne' (by positivity) (branchLog_pos hz hz1).ne'
            (gamma_branch_neg hz hz40).ne,sub_self])
  · rintro rfl
    rw [contactResidual_eq,contactCoefficients_solve z (branchLog z) hz.ne'
      (sub_pos.mpr hz1).ne' (by positivity) (branchLog_pos hz hz1).ne'
      (gamma_branch_neg hz hz40).ne,sub_self]

/-- The unscaled certificate before solving for its four free coefficients. -/
def unknownPhysicalPotential (z : ℝ) (v : Fin 4 → ℝ) (x : ℝ) : ℝ :=
  let b:=branchB z
  b^3*(-v 0*mean z+v 1*multiplier z (branchLog z)*density z-density z/3)+
    b^2*v 0*x+b^2*v 1*x*Real.log x+b^3*v 2*Real.log x+
    b^2*v 3*x*(Real.log x)^2

def unknownPhysicalPsi (z : ℝ) (v : Fin 4 → ℝ) (x y w : ℝ) : ℝ :=
  unknownPhysicalPotential z v x+unknownPhysicalPotential z v y+
    unknownPhysicalPotential z v w+
    branchMu z*branchB z^3*v 2*(x*y+y*w+w*x)+
    x*y*w*(1+branchMu z*branchB z^2*v 3*(Real.log x+Real.log y+Real.log w))

/-- The generic constant term is exactly the paper's prescribed c₀. -/
theorem unknown_constant_scaling (z : ℝ) (v : Fin 4 → ℝ) :
    branchB z^3*(-v 0*mean z+v 1*multiplier z (branchLog z)*density z-density z/3)=
      -(branchB z^2*v 0)*((branchA z+branchB z)/2)+
        (branchB z^2*v 1)*branchMu z*balancedTriangle (branchA z) (branchB z)-
        balancedTriangle (branchA z) (branchB z)/3 := by
  rw [branch_triangle,← branchMu_scaled]
  unfold branchA mean density
  ring

/-- Rescaling the unknown certificate divides its value by b³. -/
theorem unknownPhysicalPsi_scaled (z : ℝ) (v : Fin 4 → ℝ) (x y w : ℝ) :
    unknownPhysicalPsi z v (branchB z*x) (branchB z*y) (branchB z*w)=
      branchB z^3*unknownPsi z v x y w := by
  unfold unknownPhysicalPsi unknownPhysicalPotential unknownPsi unknownPotential
  rw [← branchMu_scaled]
  ring

/-- The derivative of the unscaled unknown certificate has the stated b² normalization. -/
theorem hasDerivAt_unknownPhysicalPsi (z : ℝ) (v : Fin 4 → ℝ) (y w : ℝ)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t => unknownPhysicalPsi z v t (branchB z*y) (branchB z*w))
      (branchB z^2*unknownPsiDerivative z v x y w) (branchB z*x) := by
  have hb := (branchB_pos z).ne'
  have hnorm := (hasDerivAt_unknownPsi z v y w hx).const_mul (branchB z^3)
  have hscale : (branchB z*x)/branchB z=x := by field_simp
  have hnorm' : HasDerivAt (fun t => branchB z^3*unknownPsi z v t y w)
      (branchB z^3*unknownPsiDerivative z v x y w) ((branchB z*x)/branchB z) := by
    rwa [hscale]
  have hd := hnorm'.comp (branchB z*x) ((hasDerivAt_id (branchB z*x)).div_const (branchB z))
  dsimp only [Function.comp_def,id_eq] at hd
  have hfun : (fun t => branchB z^3*unknownPsi z v (t/branchB z) y w)=
      (fun t => unknownPhysicalPsi z v t (branchB z*y) (branchB z*w)) := by
    funext t
    rw [← unknownPhysicalPsi_scaled]
    congr 1
    field_simp
  rw [hfun] at hd
  convert hd using 1
  field_simp

theorem unknownPhysicalPsi_swap_xy (z : ℝ) (v : Fin 4 → ℝ) (x y w : ℝ) :
    unknownPhysicalPsi z v x y w=unknownPhysicalPsi z v y x w := by
  unfold unknownPhysicalPsi
  ring

/-- The four original value/partial-derivative equations determine exactly the published dᵢ. -/
theorem branch_physical_tangency_iff {z : ℝ} (hz : 0 < z) (hz40 : z ≤ 1/40)
    (v : Fin 4 → ℝ) :
    (unknownPhysicalPsi z v (branchA z) (branchA z) (branchA z)=0 ∧
      deriv (fun u => unknownPhysicalPsi z v u (branchA z) (branchA z)) (branchA z)=0 ∧
      deriv (fun u => unknownPhysicalPsi z v u (branchB z) (branchB z)) (branchA z)=0 ∧
      deriv (fun u => unknownPhysicalPsi z v (branchA z) u (branchB z)) (branchB z)=0) ↔
      v=contactCoefficients z (branchLog z) := by
  have hb := (branchB_pos z).ne'
  have hA : branchA z=branchB z*z := by unfold branchA;ring
  have hn := branch_actual_tangency_iff hz hz40 v
  rw [(hasDerivAt_unknownPsi z v z z hz.ne').deriv,
    (hasDerivAt_unknownPsi z v 1 1 hz.ne').deriv,
    (hasDerivAt_unknownPsi z v z 1 (by norm_num : (1:ℝ)≠0)).deriv] at hn
  have hs : (fun u => unknownPhysicalPsi z v (branchB z*z) u (branchB z))=
      (fun u => unknownPhysicalPsi z v u (branchB z*z) (branchB z)) := by
    funext u
    exact unknownPhysicalPsi_swap_xy z v _ _ _
  rw [hA,hs,unknownPhysicalPsi_scaled,
    (hasDerivAt_unknownPhysicalPsi z v z z hz.ne').deriv]
  have h1 := (hasDerivAt_unknownPhysicalPsi z v 1 1 hz.ne').deriv
  have h2 := (hasDerivAt_unknownPhysicalPsi z v z 1 (by norm_num : (1:ℝ)≠0)).deriv
  simp only [mul_one] at h1 h2
  rw [h1,h2]
  simpa only [mul_eq_zero,pow_ne_zero 3 hb,pow_ne_zero 2 hb,false_or] using hn

end SparseLowerTail.Certificate

import SparseLowerTail.Section08.MinimizerExpectation
import SparseLowerTail.Section08.CertificateSigns
import SparseLowerTail.Section02.TriangleL2

/-! Tie exclusion from the explicit pointwise family certificate. The certificate
positivity/zero-set obligation remains visible; all graphon consequences are proved. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Certificate
open Section02 Section04 TriangleIntegration

/-- Fubini identifies the mean codegree with the squared degree norm. -/
theorem integral_codegree_eq_degree_square (U : Graphon) :
    (∫ p,codegree U p.1 p.2 ∂squareMeasure)=
      ∫ x,(∫ y,U (x,y) ∂unitMeasure)^2 ∂unitMeasure := by
  have htest := integral_test_codegree U (BoundedObservable.const (μ:=squareMeasure) 1)
  simp only [one_mul] at htest
  have hcycle := integral_cycle U (fun _ y w => y*w)
  have hpair := integral_centered_pair U 0
  simp only [sub_zero,degreeEnergy,centeredKernel] at hpair
  calc
    _ = ∫ p,Y U p*Z U p ∂tripleMeasure := htest.symm
    _ = ∫ p,Z U p*X U p ∂tripleMeasure := hcycle.symm
    _ = ∫ p,X U p*Z U p ∂tripleMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => mul_comm _ _
    _ = _ := hpair

/-- The mean codegree is at least the square of the edge density. -/
theorem edgeDensity_sq_le_integral_codegree (U : Graphon) :
    (edgeDensity U)^2≤∫ p,codegree U p.1 p.2 ∂squareMeasure := by
  have hd := (graphon_boundedObservable U).integral_left
  have h := integral_mul_sq_le hd (BoundedObservable.const (μ:=unitMeasure) 1)
  simp only [mul_one,one_pow,integral_const,measureReal_univ_eq_one,smul_eq_mul,mul_one] at h
  have he : (∫ x,(∫ y,U (x,y) ∂unitMeasure) ∂unitMeasure)=edgeDensity U :=
    (integral_prod _ (graphon_integrable U)).symm
  rw [he] at h
  rwa [integral_codegree_eq_degree_square]

/-- The signed logarithmic codegree moment has the required sign. -/
theorem integral_mul_log_codegree_nonpos (U : Graphon) :
    (∫ p,U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure)≤0 := by
  apply integral_nonpos_of_ae
  filter_upwards [U.bounded,codegree_mem_Icc_ae U] with p hp hc
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hp.1 (Real.log_nonpos hp.1 hp.2)) hc.1

/-- Equal costs give the multiplier difference without dividing by the target. -/
theorem multiplier_difference_mul_triangle {r z : ℝ} (hr : 0<r)
    (hz : z∈Ioo (0:ℝ) 1) {U : Graphon}
    (ht : balancedTriangle (branchA z) (branchB z)=r^3)
    (hF : cost U=balancedCost (branchA z) (branchB z)) :
    (branchMu z-graphonMultiplier U r)*balancedTriangle (branchA z) (branchB z)=
      edgeDensity U-(branchA z+branchB z)/2 := by
  have hb := balancedEL_multiplier_cost (branch_balancedEL hz.1 hz.2)
  have hU : graphonMultiplier U r*r^3=1-cost U-edgeDensity U := by
    unfold graphonMultiplier
    exact div_mul_cancel₀ _ (pow_ne_zero 3 hr.ne')
  rw [ht] at hb ⊢
  rw [hF] at hU
  nlinarith

/-- The certificate expectation times t, with no division in the comparison. -/
theorem tie_expectation_mul_triangle {r z : ℝ} (hr : r∈Ioo (0:ℝ) 1)
    (hz : z∈Ioo (0:ℝ) 1) {U : Graphon} (hU : IsMinimizer r U)
    (ht : balancedTriangle (branchA z) (branchB z)=r^3)
    (hF : cost U=balancedCost (branchA z) (branchB z)) :
    expectation z U*balancedTriangle (branchA z) (branchB z)=
      3*(edgeDensity U-(branchA z+branchB z)/2)*
        ((c1 z+c2 z)*balancedTriangle (branchA z) (branchB z)+
          c3 z*(∫ p,codegree U p.1 p.2 ∂squareMeasure)+
          c4 z*(∫ p,U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure)) := by
  rw [minimizer_expectation_identity hr hU ht]
  have hd := multiplier_difference_mul_triangle hr.1 hz ht hF
  linear_combination 3*(c2 z*balancedTriangle (branchA z) (branchB z)+
    c3 z*(∫ p,codegree U p.1 p.2 ∂squareMeasure)+
    c4 z*(∫ p,U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure))*hd

/-- The coefficient sign bound makes every strictly positive edge excess
incompatible with a nonnegative certificate expectation. -/
theorem tie_expectation_bound {r z : ℝ} (hr : r∈Ioo (0:ℝ) 1)
    (hz : 0<z) (hz40 : z≤1/40) {U : Graphon} (hU : IsMinimizer r U)
    (ht : balancedTriangle (branchA z) (branchB z)=r^3)
    (hF : cost U=balancedCost (branchA z) (branchB z))
    (he : (branchA z+branchB z)/2≤edgeDensity U) :
    expectation z U*balancedTriangle (branchA z) (branchB z)≤
      3*(edgeDensity U-(branchA z+branchB z)/2)*cbar z*
        balancedTriangle (branchA z) (branchB z) := by
  have hz1 : z<1 := by linarith
  have htpos : 0<balancedTriangle (branchA z) (branchB z) := by rw [ht]; exact pow_pos hr.1 3
  obtain ⟨_,_,hc3,hc4⟩ := coefficient_signs hz hz40
  have hm0 : 0≤(branchA z+branchB z)/2 := by
    have ha := branchA_pos hz
    have hb := branchB_pos z
    positivity
  have hC : ((branchA z+branchB z)/2)^2≤∫ p,codegree U p.1 p.2 ∂squareMeasure :=
    (pow_le_pow_left₀ hm0 he 2).trans (edgeDensity_sq_le_integral_codegree U)
  have h3 := mul_le_mul_of_nonpos_left hC hc3.le
  have h4 := mul_nonpos_of_nonneg_of_nonpos hc4.le (integral_mul_log_codegree_nonpos U)
  have hbar : (c1 z+c2 z)*balancedTriangle (branchA z) (branchB z)+
      c3 z*((branchA z+branchB z)/2)^2=
      cbar z*balancedTriangle (branchA z) (branchB z) := by
    unfold cbar
    symm
    rw [add_mul,div_mul_cancel₀ _ htpos.ne']
  have hbnd : (c1 z+c2 z)*balancedTriangle (branchA z) (branchB z)+
      c3 z*(∫ p,codegree U p.1 p.2 ∂squareMeasure)+
      c4 z*(∫ p,U p*Real.log (U p)*codegree U p.1 p.2 ∂squareMeasure)≤
      cbar z*balancedTriangle (branchA z) (branchB z) := by
    rw [← hbar]
    linarith
  rw [tie_expectation_mul_triangle hr ⟨hz,hz1⟩ hU ht hF]
  have hh := mul_le_mul_of_nonneg_left hbnd
    (show 0≤3*(edgeDensity U-(branchA z+branchB z)/2) from
      mul_nonneg (by norm_num) (sub_nonneg.mpr he))
  simpa only [mul_assoc] using hh

/-- Positivity alone forces matching edge density; the zero-set description is
needed only in the subsequent structure theorem. -/
theorem tie_edgeDensity_eq {r z : ℝ} (hr : r∈Ioo (0:ℝ) 1)
    (hz : 0<z) (hz40 : z≤1/40) {U : Graphon} (hU : IsMinimizer r U)
    (ht : balancedTriangle (branchA z) (branchB z)=r^3)
    (hF : cost U=balancedCost (branchA z) (branchB z))
    (he : (branchA z+branchB z)/2≤edgeDensity U)
    (hpos : ∀ x∈Ioc (0:ℝ) 1,∀ y∈Ioc (0:ℝ) 1,∀ w∈Ioc (0:ℝ) 1,0≤psi z x y w) :
    edgeDensity U=(branchA z+branchB z)/2 := by
  have hrange : ∀ᵐ p ∂squareMeasure,U p∈Ioc (0:ℝ) 1 := by
    filter_upwards [minimizer_pos_ae hr hU,U.bounded] with p hp hb
    exact ⟨hp,hb.2⟩
  have hnonneg : 0≤expectation z U := by
    apply integral_nonneg_of_ae
    filter_upwards [edgeX_qmp.ae hrange,edgeY_qmp.ae hrange,edgeZ_qmp.ae hrange] with p hx hy hw
    exact hpos _ hx _ hy _ hw
  have htpos : 0<balancedTriangle (branchA z) (branchB z) := by rw [ht]; exact pow_pos hr.1 3
  have hbnd := tie_expectation_bound hr hz hz40 hU ht hF he
  have hE := mul_nonneg hnonneg htpos.le
  apply le_antisymm _ he
  by_contra hnot
  have hdiff : 0<edgeDensity U-(branchA z+branchB z)/2 := sub_pos.mpr (lt_of_not_ge hnot)
  have hneg : 3*(edgeDensity U-(branchA z+branchB z)/2)*cbar z*
      balancedTriangle (branchA z) (branchB z)<0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (cbar_neg hz hz40)) htpos
  linarith

/-- `lem:tieexclusion` for the actual unrestricted minimizer, conditional only
on the explicit pointwise family certificate at the given branch parameter.
All analytic, multiplier, expectation, and graphon-structure steps are proved. -/
theorem minimizer_balanced_of_tie_certificate {r z : ℝ} (hr : r∈Ioo (0:ℝ) 1)
    (hz : 0<z) (hz40 : z≤1/40) {U : Graphon} (hU : IsMinimizer r U)
    (ht : balancedTriangle (branchA z) (branchB z)=r^3)
    (hF : cost U=balancedCost (branchA z) (branchB z))
    (he : (branchA z+branchB z)/2≤edgeDensity U)
    (hcert : ∀ x∈Ioc (0:ℝ) 1,∀ y∈Ioc (0:ℝ) 1,∀ w∈Ioc (0:ℝ) 1,
      0≤psi z x y w ∧ (psi z x y w=0 →
        AllowedPattern (branchA z) (branchB z) x y w)) :
    IsBalanced U (branchA z) (branchB z) := by
  have hm := tie_edgeDensity_eq hr hz hz40 hU ht hF he
    (fun x hx y hy w hw => (hcert x hx y hy w hw).1)
  exact minimizer_balanced_of_certificate hr ⟨hz,by linarith⟩ hU ht hF hm hcert

end SparseLowerTail.Certificate

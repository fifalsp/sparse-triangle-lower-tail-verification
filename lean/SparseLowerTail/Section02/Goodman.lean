import SparseLowerTail.Section02.TriangleL2

/-! The graphon Goodman bound, manuscript lem:goodman. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section02
open TriangleIntegration

/-- Degree energy dominates the square of the edge density by integral Cauchy--Schwarz. -/
theorem degreeEnergy_ge_mean_sq (U : Graphon) : (edgeDensity U)^2 ≤ degreeEnergy U 0 := by
  have hd := (graphon_boundedObservable U).integral_left
  have h := integral_mul_sq_le hd (BoundedObservable.const (1:ℝ))
  have he : (∫ x, ∫ y, U (x,y) ∂unitMeasure ∂unitMeasure) = edgeDensity U := by
    exact (integral_prod _ (graphon_integrable U)).symm
  simpa only [mul_one, one_pow, integral_const, measureReal_univ_eq_one, smul_eq_mul,
    one_mul, he, degreeEnergy, centeredKernel, sub_zero] using h

/-- The integrated triangle inequality underlying Goodman's bound. -/
theorem triangle_ge_degreeEnergy (U : Graphon) : 2*degreeEnergy U 0-edgeDensity U ≤ triangle U := by
  have hxy := (boundedX U).mul (boundedY U)
  have hxz := (boundedX U).mul (boundedZ U)
  have hxyz := hxy.mul (boundedZ U)
  have hleft : Integrable (fun p => X U p*Y U p+X U p*Z U p-X U p) tripleMeasure :=
    (hxy.integrable.add hxz.integrable).sub (boundedX U).integrable
  have hi := integral_mono_ae hleft hxyz.integrable (show
      (fun p => X U p*Y U p+X U p*Z U p-X U p) ≤ᵐ[tripleMeasure]
      (fun p => X U p*Y U p*Z U p) from by
    filter_upwards [edgeX_qmp.ae U.bounded, edgeY_qmp.ae U.bounded, edgeZ_qmp.ae U.bounded]
      with p hx hy hz
    have hx0 : 0 ≤ X U p := hx.1
    have hy1 : Y U p ≤ 1 := hy.2
    have hz1 : Z U p ≤ 1 := hz.2
    have h := mul_nonneg hx0 (mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hz1))
    nlinarith)
  rw [integral_sub (f := fun p => X U p*Y U p+X U p*Z U p) (g := X U)
      (hxy.integrable.add hxz.integrable) (boundedX U).integrable,
    integral_add hxy.integrable hxz.integrable, integral_XYZ] at hi
  have hac : (∫ p, X U p*Z U p ∂tripleMeasure) = degreeEnergy U 0 := by
    simpa only [sub_zero] using integral_centered_pair U 0
  have hca : (∫ p, Z U p*X U p ∂tripleMeasure) = degreeEnergy U 0 := by
    simpa only [mul_comm] using hac
  have hbc : (∫ p, Y U p*Z U p ∂tripleMeasure) = degreeEnergy U 0 :=
    (integral_cycle U (fun _ y z => y*z)).symm.trans hca
  have hab : (∫ p, X U p*Y U p ∂tripleMeasure) = degreeEnergy U 0 :=
    (integral_cycle U (fun x y _ => x*y)).symm.trans hbc
  have he : (∫ p, X U p ∂tripleMeasure) = edgeDensity U :=
    integral_X (f := id) U (graphon_boundedObservable U)
  rw [hac, hab, he] at hi
  linarith

/-- First conclusion of manuscript lem:goodman. -/
theorem goodman (U : Graphon) : edgeDensity U*(2*edgeDensity U-1) ≤ triangle U := by
  have h1 := triangle_ge_degreeEnergy U
  have h2 := degreeEnergy_ge_mean_sq U
  nlinarith

/-- The equivalent explicit upper bound on the mean. -/
theorem goodman_mean_bound (U : Graphon) :
    edgeDensity U ≤ (1+Real.sqrt (1+8*triangle U))/4 := by
  have hg := goodman U
  have hn : 0 ≤ 1+8*triangle U := by nlinarith [triangle_nonneg U]
  have hs := Real.sq_sqrt hn
  have hsq := Real.sqrt_nonneg (1+8*triangle U)
  by_cases hsmall : edgeDensity U ≤ 1/4
  · nlinarith
  · have hp : 0 ≤ 4*edgeDensity U-1 := by linarith
    have hle : 4*edgeDensity U-1 ≤ Real.sqrt (1+8*triangle U) := by
      apply (sq_le_sq₀ hp hsq).mp
      nlinarith
    linarith

end SparseLowerTail.Section02

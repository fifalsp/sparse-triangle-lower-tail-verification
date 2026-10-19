import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Shared definitions for the integral proof of `lem:J`. -/
noncomputable section
namespace SparseLowerTail.Section04

/-- The four truncated linear/quadratic coordinates in `lem:J`. -/
def bipodalPhi (x y s : ℝ) : Fin 4 → ℝ :=
  ![s-x, max (s-y) 0, (s^2-x^2)/2, max (s^2-y^2) 0/2]

/-- The symmetric bilinear form from the proof of `lem:J`. -/
def bipodalBilinear (x y : ℝ) (v w : Fin 4 → ℝ) : ℝ :=
  (1-y)*y*(1+x)*v 0*w 0-(1-x)*x*(1+y)*v 1*w 1
  -(y-x)*(v 0*w 1+v 1*w 0)
  -(1-y)*((y*v 0+v 1)*w 2+(y*w 0+w 1)*v 2)
  +(1-x)*((v 0+x*v 1)*w 3+(w 0+x*w 1)*v 3)

/-- The continuous kernel whose positivity proves `lem:J`. -/
def bipodalOmega (x y s t : ℝ) : ℝ :=
  bipodalBilinear x y (bipodalPhi x y s) (bipodalPhi x y t)

/-- The logarithmic moment vector. -/
def bipodalPhiHat (x y : ℝ) : Fin 4 → ℝ := ![-Real.log x,-Real.log y,1-x,1-y]

end SparseLowerTail.Section04

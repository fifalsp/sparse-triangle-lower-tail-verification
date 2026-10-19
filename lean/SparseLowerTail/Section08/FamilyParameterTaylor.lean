import SparseLowerTail.Section08.FamilyParameterCalculus
import SparseLowerTail.Section08.CertificateTail
import SparseLowerTail.Numerics.TaylorParameter
import SparseLowerTail.Numerics.DyadicFiniteSum

/-! Actual parameter Taylor bounds for the logarithmic family certificate.
Weights are combined before taking absolute values, preserving the coefficient
cancellations used by the paper's exterior-region verification. -/
noncomputable section
namespace SparseLowerTail.Certificate.FamilyCoeff
open Numerics Section04 Set

/-- Signs and factors are included in the weights; coefficient order is the
same stable seven-entry order as `coefficientValues`. -/
def phiWeights (q : Fin 3 → ℝ) : Fin 7 → ℝ :=
  let x := fun i => Real.exp (-q i)
  let s := q 0+q 1+q 2
  ![3,x 0+x 1+x 2,-(q 0*x 0+q 1*x 1+q 2*x 2),-s,
    (q 0)^2*x 0+(q 1)^2*x 1+(q 2)^2*x 2,
    x 0*x 1+x 1*x 2+x 2*x 0,-s*(x 0*x 1*x 2)]

def weightedDerivative (w : Fin 7 → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i,w i*coefficientDerivative i n t

def phiParameterDerivative (q : Fin 3 → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  weightedDerivative (phiWeights q) n t+
    if n=0 then Real.exp (-q 0)*Real.exp (-q 1)*Real.exp (-q 2) else 0

theorem phiParameterDerivative_zero (q : Fin 3 → ℝ) (t : ℝ) :
    phiParameterDerivative q 0 t=phi (Real.exp (-t)) (q 0) (q 1) (q 2) := by
  rw [phi_formula]
  simp [phiParameterDerivative,weightedDerivative,coefficientDerivative_zero,
    phiWeights,coefficientValues,Fin.sum_univ_succ,logPotential]
  <;> ring

theorem weightedDerivative_hasDerivAt (w : Fin 7 → ℝ) (n : ℕ) {t : ℝ}
    (ht : 0<t) (he : ∀i,(derivativeExpr i n).Domain (parameterCurve t)) :
    HasDerivAt (weightedDerivative w n) (weightedDerivative w (n+1) t) t := by
  exact HasDerivAt.fun_sum (fun i _ => (coefficientDerivative_hasDerivAt i n ht (he i)).const_mul (w i))

theorem phiParameterDerivative_hasDerivAt (q : Fin 3 → ℝ) (n : ℕ) {t : ℝ}
    (ht : 0<t) (he : ∀i,(derivativeExpr i n).Domain (parameterCurve t)) :
    HasDerivAt (phiParameterDerivative q n) (phiParameterDerivative q (n+1) t) t := by
  simpa only [phiParameterDerivative,Nat.add_one_ne_zero,↓reduceIte,add_zero] using
    (weightedDerivative_hasDerivAt (phiWeights q) n ht he).add_const
      (if n=0 then Real.exp (-q 0)*Real.exp (-q 1)*Real.exp (-q 2) else 0)

/-- A finite dot product keeps cancellation until its final enclosure. -/
def weightedInterval (W D : Fin 7 → DyadicInterval) : DyadicInterval :=
  DyadicInterval.sumFin (fun i => (W i).mul (D i))

theorem weightedDerivative_interval (C : FamilyParameterCertificate) (hC : C.Valid)
    (w : Fin 7 → ℝ) (n : ℕ) (W D : Fin 7 → DyadicInterval)
    (hW : ∀i,(W i).contains (w i))
    (hD : ∀i,(derivativeExpr i n).dyadicEval C.parameterBox=some (D i))
    {t : ℝ} (ht : Bounds t (C.logLower.q : ℝ) (C.logUpper.q : ℝ)) :
    (weightedInterval W D).contains (weightedDerivative w n t) := by
  apply DyadicInterval.sumFin_contains
  intro i
  exact DyadicInterval.mul_contains (hW i) (coefficientDerivative_interval C hC i n (hD i) ht)

/-- Checked coefficient expressions supply all three analytic derivative
steps. This is the parameter Taylor bound of `compact_test`, before q variation. -/
theorem phi_parameter_taylor_lower (C : FamilyParameterCertificate) (hC : C.Valid)
    (q : Fin 3 → ℝ) (W : Fin 7 → DyadicInterval)
    (D : Fin 4 → Fin 7 → DyadicInterval)
    (hW : ∀i,(W i).contains (phiWeights q i))
    (hD : ∀n i,(derivativeExpr i n.val).dyadicEval C.parameterBox=some (D n i))
    {c d w : ℝ}
    (hpath : ∀s ∈ Icc (0:ℝ) 1,
      Bounds (c+s*d) (C.logLower.q : ℝ) (C.logUpper.q : ℝ))
    (hpos : 0<(C.logLower.q : ℝ)) (hd : |d|≤w) :
    phi (Real.exp (-c)) (q 0) (q 1) (q 2)-|phiParameterDerivative q 1 c| * w+
      min 0 (phiParameterDerivative q 2 c)*w^2/2-
        ((weightedInterval W (D 3)).absBound : ℝ)/DyadicInterval.scale*w^3/6 ≤
    phi (Real.exp (-(c+d))) (q 0) (q 1) (q 2) := by
  have hdv (n : Fin 3) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      HasDerivAt (phiParameterDerivative q n.val)
        (phiParameterDerivative q (n.val+1) (c+s*d)) (c+s*d) := by
    apply phiParameterDerivative_hasDerivAt q n.val (hpos.trans_le (hpath s hs).1)
    intro i
    apply RationalExpr.domain_of_dyadicEval _ _ (hD ⟨n.val,by omega⟩ i)
    rw [parameterCurve_eq]
    apply C.parameterBox_contains hC (Real.exp_pos _)
    simpa only [branchLog_eq_neg_log,Real.log_exp,neg_neg] using hpath s hs
  have hb (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      |phiParameterDerivative q 3 (c+s*d)| ≤
        ((weightedInterval W (D 3)).absBound : ℝ)/DyadicInterval.scale := by
    simpa only [phiParameterDerivative,show (3:ℕ)≠0 by decide,↓reduceIte,add_zero] using
      DyadicInterval.abs_le_absBound
        (weightedDerivative_interval C hC (phiWeights q) 3 W (D 3) hW (hD 3) (hpath s hs))
  simpa [phiParameterDerivative_zero] using
    parameter_taylor3_lower (hdv 0) (hdv 1) (hdv 2) hb hd

end SparseLowerTail.Certificate.FamilyCoeff

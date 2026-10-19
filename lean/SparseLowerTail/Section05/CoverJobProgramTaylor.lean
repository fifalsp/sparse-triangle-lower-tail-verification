import SparseLowerTail.Section05.CoverJobProgram

/-! Shared evaluation preserves the original job margin exactly, including
its diagonal square intervals. No numerical acceptance criterion is weakened. -/
namespace SparseLowerTail.Section05.CoverJobProgram
open Numerics

def run (box : Fin 24 → DyadicInterval) : RegisterTree DyadicInterval :=
  IntervalProgram.dyadic code depth box

def gradientOutputs : Fin 3 → ℕ :=
  ![outputGradient0,outputGradient1,outputGradient2]
def hessianOutputs : Fin 3 → Fin 3 → ℕ :=
  ![![outputHessian00,outputHessian01,outputHessian02],
    ![outputHessian10,outputHessian11,outputHessian12],
    ![outputHessian20,outputHessian21,outputHessian22]]

theorem value_eq (box : Fin 24 → DyadicInterval) :
    (run box).get outputValue=apexCertificateExpr.dyadicEval box := by
  rw [run,IntervalProgram.dyadic_eq,outputValue_eq]

theorem gradient_eq (box : Fin 24 → DyadicInterval) (i : Fin 3) :
    (run box).get (gradientOutputs i)=(coverGradientExpr i).dyadicEval box := by
  rw [run,IntervalProgram.dyadic_eq]
  fin_cases i
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputGradient0_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputGradient1_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputGradient2_eq

theorem hessian_eq (box : Fin 24 → DyadicInterval) (i j : Fin 3) :
    (run box).get (hessianOutputs i j)=(coverHessianExpr i j).dyadicEval box := by
  rw [run,IntervalProgram.dyadic_eq]
  fin_cases i <;> fin_cases j
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian00_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian01_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian02_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian10_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian11_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian12_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian20_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian21_eq
  · exact congrArg (fun e : ApexExpr => e.dyadicEval box) outputHessian22_eq

open RefinedCover.S1TaylorBoxData in
def margin (D : S1TaylorBoxData) (job : Fin 36) : ℤ :=
  let st := run (RefinedCover.nonapexBoxIntervals (jobStartBox D) job)
  let wh := run (RefinedCover.nonapexBoxIntervals (jobWholeBox D) job)
  let v := jobVelocity D
  let g := DyadicInterval.sumThree (fun i => (v i).mul (st.get (gradientOutputs i)))
  let h := DyadicInterval.sumThree (fun i => DyadicInterval.sumThree (fun j =>
    (dyadicVelocityProduct v i j).mul (wh.get (hessianOutputs i j))))
  2*(st.get outputValue).lower+2*g.lower+h.lower

theorem margin_eq_job (D : S1TaylorBoxData) (job : Fin 36) :
    margin D job=RefinedCover.S1TaylorBoxData.jobMargin D job := by
  simp only [margin,value_eq,gradient_eq,hessian_eq]
  rfl

theorem positive (D : S1TaylorBoxData) (job : Fin 36)
    (hl : ∀i,(D.lowerExp i).Valid) (hu : ∀i,(D.upperExp i).Valid)
    (hc : ∀i,(D.centerExp i).Valid)
    (hql : ∀i,(D.lowerExp i).q=D.box.lower i)
    (hqu : ∀i,(D.upperExp i).q=D.box.upper i)
    (hqc : ∀i,(D.centerExp i).q=D.box.centerCoordinate i)
    (hm : 0<margin D job) {q : EdgeTriple} (hq : q∈D.box.region) :
    0<logCertificate (coverCellTheta (CoverGeometry.nonapexCell job))
      (CoverGeometry.cellLambda (CoverGeometry.nonapexCell job))
      (CoverGeometry.nonapexVertex job) q := by
  apply RefinedCover.S1TaylorBoxData.job_positive D job hl hu hc hql hqu hqc ?_ hq
  rwa [←margin_eq_job]

end SparseLowerTail.Section05.CoverJobProgram
